//! Jump threading through blocks that branch on a phi of constants.
//!
//! A block `B` ending in `br c T F` or `br_table c ...`, where `c` is a phi of
//! `B`, sends every path that enters from a predecessor `P` whose incoming `c`
//! is a constant to one known successor. So does `c = enum.tag p` for a phi
//! `p` of `B` whose incoming value from `P` is an `enum.make`. The edge `P -> B` is retargeted straight to that
//! successor: `B`'s other instructions, which must be pure and few, are
//! recomputed at the end of `P` from `P`'s incoming values, and the
//! successor's phis take what `B` would have passed them. `B` is deleted
//! once no predecessor is left. When `P` has other successors, the recomputed
//! instructions also run on their paths, so they must be speculatable.
//!
//! A cursor loop's `Option` test is the motivating shape: the latch tests
//! the next cursor, enters a join that materializes the tag as `phi(1, 0)`,
//! and branches on the tag again. Threading leaves one branch, and the
//! header's cursor phi then takes the latch's value on the edge where the
//! latch's own comparison holds.
//!
//! Rebuilding an `Option` and matching it again is the enum shape: a join
//! takes `enum.make` values from its predecessors and branches on their tag.
//!
//! `B`'s values reach the rest of the function through its successors' phis.
//! A use below a successor entered only from `B` gets such a phi first, so
//! threading can supply each path's value.
//!
//! A loop header is never threaded: retargeting an entry edge into the
//! loop's body would give the loop a second entry.

use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, I256, Immediate, InstId, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        control_flow::{BranchKind, Phi},
        data,
    },
};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode, clone_inst_before, defined_in},
    domtree::DomTree,
};

/// The most instructions of a threaded block recomputed in a predecessor.
const MAX_DUPLICATED_INSTS: usize = 4;

#[derive(Default)]
pub struct JumpThread;

impl JumpThread {
    pub fn new() -> Self {
        Self
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        let mut domtree = DomTree::new();
        domtree.compute(editor.cfg());
        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        let mut changed = false;
        for block in blocks {
            if editor.func().layout.is_block_inserted(block)
                && thread_block(&mut editor, &domtree, block)
            {
                domtree.compute(editor.cfg());
                changed = true;
            }
        }
        if changed {
            let unreachable: Vec<_> = {
                let reachable = editor.cfg().reachable_blocks();
                editor
                    .func()
                    .layout
                    .iter_block()
                    .filter(|block| !reachable[*block])
                    .collect()
            };
            editor.delete_blocks_unreachable(&unreachable);
        }
        changed
    }
}

/// A block that may be threaded.
struct Candidate {
    cond_phi: InstId,
    /// Whether the condition is the tag of `cond_phi`'s enum.
    tag_of_phi: bool,
    /// The successor for each condition value with one of its own; `br`
    /// sends zero to its zero destination.
    cases: SmallVec<[(Immediate, BlockId); 4]>,
    /// The successor for any other condition value.
    default: Option<BlockId>,
    /// The pure instructions between the block's phis and its terminator.
    body: SmallVec<[InstId; MAX_DUPLICATED_INSTS]>,
    /// Values of the block used below a successor entered only from it,
    /// with that successor.
    escapes: SmallVec<[(ValueId, BlockId); 2]>,
}

fn candidate(editor: &CfgEditor<'_>, domtree: &DomTree, block: BlockId) -> Option<Candidate> {
    let func = editor.func();
    if func.layout.entry_block() == Some(block)
        || !domtree.is_reachable(block)
        || editor
            .cfg()
            .preds_of(block)
            .any(|pred| domtree.dominates(block, *pred))
    {
        return None;
    }
    let term = func.layout.last_inst_of(block)?;
    let (cond, cases, default): (_, SmallVec<_>, _) =
        match func.dfg.branch_info(term)?.branch_kind() {
            BranchKind::Br(br) => {
                let zero = Immediate::zero(func.dfg.value_ty(*br.cond()));
                (
                    *br.cond(),
                    smallvec![(zero, *br.z_dest())],
                    Some(*br.nz_dest()),
                )
            }
            BranchKind::BrTable(table) => (
                *table.scrutinee(),
                table
                    .table()
                    .iter()
                    .map(|&(key, dest)| Some((func.dfg.value_imm(key)?, dest)))
                    .collect::<Option<_>>()?,
                *table.default(),
            ),
            BranchKind::Jump(_) => return None,
        };
    let dests: SmallVec<[BlockId; 4]> =
        cases.iter().map(|&(_, dest)| dest).chain(default).collect();
    if dests.iter().all(|&dest| dest == dests[0]) || dests.contains(&block) {
        return None;
    }
    let cond_inst = func.dfg.value_inst(cond)?;
    let (cond_phi, tag_of_phi) = match func.dfg.downcast::<&data::EnumTag>(cond_inst) {
        Some(tag) => (func.dfg.value_inst(*tag.value())?, true),
        None => (cond_inst, false),
    };
    if !func.dfg.is_phi(cond_phi) || func.layout.inst_block(cond_phi) != block {
        return None;
    }

    let mut body = SmallVec::new();
    for inst in func.layout.iter_inst(block) {
        if inst == term {
            break;
        }
        if func.dfg.is_phi(inst) {
            // An incoming value defined in the block itself is only available
            // after it, not at the end of a predecessor.
            let phi = func.dfg.cast_phi(inst)?;
            if phi
                .args()
                .iter()
                .any(|(value, _)| defined_in(func, *value, block))
            {
                return None;
            }
            continue;
        }
        if !func.dfg.has_value_semantics(inst) || body.len() == MAX_DUPLICATED_INSTS {
            return None;
        }
        body.push(inst);
    }

    // What the block defines reaches its own instructions and its
    // successors' phis on the edges from it, so a threaded path needs only
    // the successors' phi inputs. A use below a successor entered only from
    // the block can be given such a phi.
    let mut escapes = SmallVec::new();
    for inst in func.layout.iter_inst(block) {
        for &result in func.dfg.inst_results(inst) {
            for &user in func.dfg.users(result) {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }
                let user_block = func.layout.inst_block(user);
                if user_block == block {
                    continue;
                }
                let via_edge_from_block = dests.contains(&user_block)
                    && func.dfg.cast_phi(user).is_some_and(|phi| {
                        phi.args()
                            .iter()
                            .all(|(value, from)| *value != result || *from == block)
                    });
                if via_edge_from_block {
                    continue;
                }
                let succ = dests.iter().copied().find(|&dest| {
                    editor.cfg().preds_of(dest).eq([&block])
                        && use_dominated_by(func, domtree, user, result, dest)
                })?;
                if !escapes.contains(&(result, succ)) {
                    escapes.push((result, succ));
                }
            }
        }
    }

    Some(Candidate {
        cond_phi,
        tag_of_phi,
        cases,
        default,
        body,
        escapes,
    })
}

/// Whether `user`'s uses of `value` all lie in blocks `dest` dominates: a
/// phi's at the ends of its predecessors, any other's in its own block.
fn use_dominated_by(
    func: &Function,
    domtree: &DomTree,
    user: InstId,
    value: ValueId,
    dest: BlockId,
) -> bool {
    match func.dfg.cast_phi(user) {
        Some(phi) => phi
            .args()
            .iter()
            .all(|(input, from)| *input != value || domtree.dominates(dest, *from)),
        None => domtree.dominates(dest, func.layout.inst_block(user)),
    }
}

/// Gives `dest`, entered only from `block`, a phi for `value`, and moves the
/// uses `dest` dominates onto it.
fn route_through_phi(
    func: &mut Function,
    domtree: &DomTree,
    block: BlockId,
    value: ValueId,
    dest: BlockId,
) {
    let ty = func.dfg.value_ty(value);
    let phi = Phi::new_unchecked(func.inst_set(), smallvec![(value, block)]);
    let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(dest));
    let phi_inst = cursor.prepend_inst_data(func, phi);
    let routed = func.dfg.make_value(Value::Inst {
        inst: phi_inst,
        result_idx: 0,
        ty,
    });
    cursor.attach_result(func, phi_inst, routed);

    let users: Vec<_> = func
        .dfg
        .users(value)
        .copied()
        .filter(|&user| user != phi_inst && func.layout.is_inst_inserted(user))
        .collect();
    for user in users {
        if func.dfg.is_phi(user) {
            func.dfg.edit_phi(user, |phi| {
                for (input, from) in phi.args_mut() {
                    if *input == value && domtree.dominates(dest, *from) {
                        *input = routed;
                    }
                }
            });
        } else if domtree.dominates(dest, func.layout.inst_block(user)) {
            let mut inst = func.dfg.clone_inst(user);
            inst.for_each_value_mut(&mut |operand| {
                if *operand == value {
                    *operand = routed;
                }
            });
            func.dfg.replace_inst(user, inst);
        }
    }
}

/// Threads every predecessor of `block` that can be. All are chosen before
/// any edge moves: retargeting one simplifies the block's phis that become
/// trivial, which can turn the condition into a constant.
fn thread_block(editor: &mut CfgEditor<'_>, domtree: &DomTree, block: BlockId) -> bool {
    let Some(cand) = candidate(editor, domtree, block) else {
        return false;
    };
    let threads: Vec<_> = editor
        .cfg()
        .preds_of(block)
        .filter_map(|&pred| {
            let (edge_idx, dest) = threadable_edge(editor, block, &cand, pred)?;
            Some((pred, edge_idx, dest))
        })
        .collect();
    if threads.is_empty() {
        return false;
    }
    for &(value, dest) in &cand.escapes {
        route_through_phi(editor.func_mut(), domtree, block, value, dest);
    }
    for &(pred, edge_idx, dest) in &threads {
        thread_edge(editor, block, &cand, pred, edge_idx, dest);
    }
    true
}

/// The edge `pred -> block` and the successor its constant condition
/// selects, when `pred` enters once, does not already branch there, and may
/// run the block's body on its other successors' paths.
fn threadable_edge(
    editor: &CfgEditor<'_>,
    block: BlockId,
    cand: &Candidate,
    pred: BlockId,
) -> Option<(usize, BlockId)> {
    let func = editor.func();
    if pred == block {
        return None;
    }
    let cond = func.dfg.cast_phi(cand.cond_phi)?;
    let incoming = cond
        .args()
        .iter()
        .find(|(_, from)| *from == pred)
        .map(|(value, _)| *value)?;
    let imm = if cand.tag_of_phi {
        let make = func
            .dfg
            .downcast::<&data::EnumMake>(func.dfg.value_inst(incoming)?)?;
        Immediate::EnumTag {
            enum_ty: make.variant().enum_ty(),
            value: I256::from(u64::from(make.variant().index())),
        }
    } else {
        func.dfg.value_imm(incoming)?
    };
    let dest = cand
        .cases
        .iter()
        .find(|(key, _)| *key == imm)
        .map(|&(_, dest)| dest)
        .or(cand.default)?;
    if dest == pred {
        return None;
    }
    let term = func.layout.last_inst_of(pred)?;
    let dests = func.dfg.branch_info(term)?.dests();
    let mut edges = dests.iter().enumerate().filter(|(_, to)| **to == block);
    let (edge_idx, _) = edges.next()?;
    if edges.next().is_some()
        || dests.contains(&dest)
        || (dests.len() > 1 && !cand.body.iter().all(|&inst| func.dfg.can_speculate(inst)))
    {
        return None;
    }
    Some((edge_idx, dest))
}

fn thread_edge(
    editor: &mut CfgEditor<'_>,
    block: BlockId,
    cand: &Candidate,
    pred: BlockId,
    edge_idx: usize,
    dest: BlockId,
) {
    let func = editor.func_mut();

    // The block's values as `pred` would see them: its phis' incoming values
    // from `pred`, and its instructions recomputed at the end of `pred`.
    let mut map: FxHashMap<ValueId, ValueId> = FxHashMap::default();
    let phis: Vec<_> = func
        .layout
        .iter_inst(block)
        .take_while(|inst| func.dfg.is_phi(*inst))
        .collect();
    for phi_inst in phis {
        let phi = func.dfg.cast_phi(phi_inst).expect("phi");
        let incoming = phi
            .args()
            .iter()
            .find(|(_, from)| *from == pred)
            .map(|(value, _)| *value)
            .expect("a phi has an input for each predecessor");
        let result = func.dfg.inst_result(phi_inst).expect("a phi has a result");
        map.insert(result, incoming);
    }

    let pred_term = func.layout.last_inst_of(pred).expect("terminated block");
    for &inst in &cand.body {
        clone_inst_before(func, inst, pred_term, &mut map);
    }

    // The successor's phis take, from `pred`, what they took from the block.
    let dest_phis: Vec<_> = func
        .layout
        .iter_inst(dest)
        .take_while(|inst| func.dfg.is_phi(*inst))
        .collect();
    let phi_inputs: Vec<_> = dest_phis
        .into_iter()
        .map(|phi_inst| {
            let phi = func.dfg.cast_phi(phi_inst).expect("phi");
            let from_block = phi
                .args()
                .iter()
                .find(|(_, from)| *from == block)
                .map(|(value, _)| *value)
                .expect("a successor's phi has an input from the block");
            (
                phi_inst,
                map.get(&from_block).copied().unwrap_or(from_block),
            )
        })
        .collect();

    editor.retarget_out_edge(pred, edge_idx, dest, &phi_inputs);
}
