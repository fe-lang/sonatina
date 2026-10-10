//! Jump threading through blocks that branch on a phi of constants.
//!
//! A block `B` ending in `br c T F`, where `c` is a phi of `B`, sends every
//! path that enters from a predecessor `P` whose incoming `c` is a constant
//! to one known successor. The edge `P -> B` is retargeted straight to that
//! successor: `B`'s other instructions, which must be pure and few, are
//! recomputed at the end of `P` from `P`'s incoming values, and the
//! successor's phis take what `B` would have passed them. `B` is deleted
//! once no predecessor is left.
//!
//! A cursor loop's `Option` test is the motivating shape: the latch tests
//! the next cursor, enters a join that materializes the tag as `phi(1, 0)`,
//! and branches on the tag again. Threading leaves one branch, and the
//! header's cursor phi then takes the latch's value on the edge where the
//! latch's own comparison holds.
//!
//! A loop header is never threaded: retargeting an entry edge into the
//! loop's body would give the loop a second entry.

use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, InstId, Value, ValueId, inst::control_flow::BranchKind};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode},
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
    /// The successors for a nonzero and a zero condition.
    dests: [BlockId; 2],
    /// The pure instructions between the block's phis and its terminator.
    body: SmallVec<[InstId; MAX_DUPLICATED_INSTS]>,
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
    let BranchKind::Br(br) = func.dfg.branch_info(term)?.branch_kind() else {
        return None;
    };
    let (cond, nz_dest, z_dest) = (*br.cond(), *br.nz_dest(), *br.z_dest());
    if nz_dest == z_dest || nz_dest == block || z_dest == block {
        return None;
    }
    let Some(Value::Inst { inst: cond_phi, .. }) = func.dfg.get_value(cond) else {
        return None;
    };
    let cond_phi = *cond_phi;
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

    // What the block defines reaches nothing but its own instructions and
    // its successors' phis on the edges from it, so a threaded path needs
    // only the successors' phi inputs.
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
                let via_edge_from_block = (user_block == nz_dest || user_block == z_dest)
                    && func.dfg.cast_phi(user).is_some_and(|phi| {
                        phi.args()
                            .iter()
                            .all(|(value, from)| *value != result || *from == block)
                    });
                if !via_edge_from_block {
                    return None;
                }
            }
        }
    }

    Some(Candidate {
        cond_phi,
        dests: [nz_dest, z_dest],
        body,
    })
}

fn defined_in(func: &Function, value: ValueId, block: BlockId) -> bool {
    matches!(
        func.dfg.get_value(value),
        Some(Value::Inst { inst, .. }) if func.layout.is_inst_inserted(*inst)
            && func.layout.inst_block(*inst) == block
    )
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
    for &(pred, edge_idx, dest) in &threads {
        thread_edge(editor, block, &cand, pred, edge_idx, dest);
    }
    !threads.is_empty()
}

/// The edge `pred -> block` and the successor its constant condition
/// selects, when `pred` enters once and does not already branch there.
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
    let imm = func.dfg.value_imm(incoming)?;
    let dest = if imm.is_zero() {
        cand.dests[1]
    } else {
        cand.dests[0]
    };
    if dest == pred {
        return None;
    }
    let term = func.layout.last_inst_of(pred)?;
    let dests = func.dfg.branch_info(term)?.dests();
    let mut edges = dests.iter().enumerate().filter(|(_, to)| **to == block);
    let (edge_idx, _) = edges.next()?;
    if edges.next().is_some() || dests.contains(&dest) {
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
        let mut cloned = func.dfg.clone_inst(inst);
        cloned.for_each_value_mut(&mut |value| {
            if let Some(&mapped) = map.get(value) {
                *value = mapped;
            }
        });
        let attribution = func.inst_attribution(inst);
        let new_inst = func.dfg.make_inst_dyn(cloned);
        func.layout.insert_inst_before(new_inst, pred_term);
        let results: SmallVec<[ValueId; 2]> = func
            .dfg
            .inst_results(inst)
            .to_vec()
            .into_iter()
            .enumerate()
            .map(|(result_idx, old)| {
                let new = func.dfg.make_value(Value::Inst {
                    inst: new_inst,
                    result_idx: result_idx.try_into().expect("too many instruction results"),
                    ty: func.dfg.value_ty(old),
                });
                map.insert(old, new);
                new
            })
            .collect();
        func.dfg.attach_results(new_inst, &results);
        func.apply_inst_attribution(new_inst, &attribution);
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
