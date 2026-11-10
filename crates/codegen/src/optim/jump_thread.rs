//! Jump threading through blocks whose branch condition is known on an edge
//! into them.
//!
//! A block `B` ending in `br c T F` or `br_table c ...` sends every path that
//! enters from a predecessor `P` knowing `c` to one successor. `P` knows `c`
//! when:
//!
//! - `c` is computed in `B` from its phis, and folds to a constant given
//!   their incoming values from `P`: a phi whose incoming value is a
//!   constant, `is_zero` of one, or `enum.tag` of a phi whose incoming value
//!   is an `enum.make`;
//! - `c` is defined above `B`, cannot be undef, and the edge `P -> B`, or an
//!   edge that every path into `P` takes, leaves a branch on `c`.
//!
//! The edge `P -> B` is retargeted straight to that successor: `B`'s other
//! instructions, which must be pure and few, are recomputed at the end of `P`
//! from `P`'s incoming values, and the successor's phis take what `B` would
//! have passed them. `B` is deleted once no predecessor is left. When `P` has
//! other successors, the recomputed instructions also run on their paths, so
//! they must be speculatable. A use of `B`'s values beyond its successors'
//! phis then takes the value of whichever of `B` and the threaded
//! predecessors its path last left, through new phis where paths meet.
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
//! Testing one condition twice is the dominating shape:
//! `if c { a } else { b }` followed by `if c { x } else { y }` joins after
//! the first test and tests `c` again. Each arm of the first test then goes
//! straight to its arm of the second.
//!
//! A loop header is never threaded: retargeting an entry edge into the
//! loop's body would give the loop a second entry.

use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, I256, Immediate, InstId, ValueId,
    builder::SsaBuilder,
    inst::{
        control_flow::{BrTable, BranchKind},
        data,
    },
};

use super::simplify_expr::{
    ConstantFacts, ExprFactProvider, SimplifiedResult, simplify_inst_with_facts,
};
use crate::{
    analysis::definedness::value_may_be_undef,
    cfg_edit::{CfgEditor, CleanupMode, clone_inst_before, defined_in, remove_phi_incoming_from},
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
                // A block left without predecessors goes at once: the phis
                // that repairing its uses added to its successors have no
                // input from it.
                let reachable = editor.cfg().reachable_blocks();
                let unreachable: Vec<_> = editor
                    .func()
                    .layout
                    .iter_block()
                    .filter(|block| !reachable[*block])
                    .collect();
                editor.delete_blocks_unreachable(&unreachable);
                domtree.compute(editor.cfg());
                changed = true;
            }
        }
        changed
    }
}

/// A block that may be threaded.
struct Candidate {
    cond: Cond,
    /// The successor for each condition value with one of its own; `br`
    /// sends zero to its zero destination.
    cases: SmallVec<[(Immediate, BlockId); 4]>,
    /// The successor for any other condition value.
    default: Option<BlockId>,
    /// The pure instructions between the block's phis and its terminator.
    body: SmallVec<[InstId; MAX_DUPLICATED_INSTS]>,
}

/// What a candidate's predecessor knows its condition by.
enum Cond {
    /// A phi of the block, or its body's result: the predecessor's incoming
    /// constants, folded through the body.
    Local(ValueId),
    /// A branch on a condition defined above the block that the edge from
    /// the predecessor, or every path into the predecessor, leaves.
    Dominating(ValueId),
}

/// What a branch condition is on an edge.
enum Known {
    Is(Immediate),
    /// None of these values.
    Not(SmallVec<[Immediate; 4]>),
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
                table_cases(func, table)?,
                *table.default(),
            ),
            BranchKind::Jump(_) => return None,
        };
    let dests: SmallVec<[BlockId; 4]> =
        cases.iter().map(|&(_, dest)| dest).chain(default).collect();
    if dests.iter().all(|&dest| dest == dests[0]) || dests.contains(&block) {
        return None;
    }
    let cond = if defined_in(func, cond, block) {
        Cond::Local(cond)
    } else {
        // A condition that may be undef is chosen apart at each branch on
        // it, so an earlier branch tells nothing of this one. A block every
        // path into which knows the condition is left to branch folding.
        if value_may_be_undef(func, cond, &mut FxHashMap::default(), |_| None)
            || known_into(func, editor.cfg(), domtree, cond, block).is_some()
        {
            return None;
        }
        Cond::Dominating(cond)
    };

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

    Some(Candidate {
        cond,
        cases,
        default,
        body,
    })
}

fn table_cases(func: &Function, table: &BrTable) -> Option<SmallVec<[(Immediate, BlockId); 4]>> {
    table
        .table()
        .iter()
        .map(|&(key, dest)| Some((func.dfg.value_imm(key)?, dest)))
        .collect()
}

/// What `pred` computes `cond`, a value of `block`, to be: the constants
/// among `block`'s phis' incoming values from `pred`, folded through its
/// body. The tag of an incoming `enum.make` is a constant too.
fn incoming_cond(
    func: &Function,
    block: BlockId,
    cand: &Candidate,
    cond: ValueId,
    pred: BlockId,
) -> Option<Immediate> {
    let mut facts = ConstantFacts {
        func,
        known: FxHashMap::default(),
    };
    let mut tags = FxHashMap::default();
    for phi_inst in func.layout.iter_inst(block) {
        let Some(phi) = func.dfg.cast_phi(phi_inst) else {
            break;
        };
        let incoming = phi
            .args()
            .iter()
            .find(|(_, from)| *from == pred)
            .map(|&(value, _)| value)?;
        let result = func.dfg.inst_result(phi_inst)?;
        if let Some(imm) = func.dfg.value_imm(incoming) {
            facts.known.insert(result, imm);
        } else if let Some(make) = func
            .dfg
            .value_inst(incoming)
            .and_then(|inst| func.dfg.downcast::<&data::EnumMake>(inst))
        {
            tags.insert(
                result,
                Immediate::EnumTag {
                    enum_ty: make.variant().enum_ty(),
                    value: I256::from(u64::from(make.variant().index())),
                },
            );
        }
    }
    for &inst in &cand.body {
        let &[result] = func.dfg.inst_results(inst) else {
            continue;
        };
        let imm = match func.dfg.downcast::<&data::EnumTag>(inst) {
            Some(tag) => tags.get(tag.value()).copied(),
            None => match simplify_inst_with_facts(func, inst, &facts).result(0) {
                SimplifiedResult::Const(imm) => Some(imm),
                SimplifiedResult::Copy(value) => facts.known_imm(value),
                SimplifiedResult::NoChange => None,
            },
        };
        if let Some(imm) = imm {
            facts.known.insert(result, imm);
        }
    }
    facts.known_imm(cond)
}

/// What `cond` is on the edge `from -> to`, when `from` branches on it.
fn known_on_edge(func: &Function, cond: ValueId, from: BlockId, to: BlockId) -> Option<Known> {
    let term = func.layout.last_inst_of(from)?;
    match func.dfg.branch_info(term)?.branch_kind() {
        BranchKind::Br(br) if *br.cond() == cond => {
            match (*br.nz_dest() == to, *br.z_dest() == to) {
                (true, false) => Some(Known::Not(smallvec![Immediate::zero(
                    func.dfg.value_ty(cond)
                )])),
                (false, true) => Some(Known::Is(Immediate::zero(func.dfg.value_ty(cond)))),
                _ => None,
            }
        }
        BranchKind::BrTable(table) if *table.scrutinee() == cond => {
            let cases = table_cases(func, table)?;
            let mut into = cases.iter().filter(|(_, dest)| *dest == to);
            match (into.next(), into.next(), *table.default() == Some(to)) {
                (Some(&(key, _)), None, false) => Some(Known::Is(key)),
                (None, _, true) => {
                    Some(Known::Not(cases.into_iter().map(|(key, _)| key).collect()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// What `cond` is on every path into `block`: decided by the edge into it
/// from its one predecessor, or else into its immediate dominator. The paths
/// into the entry block include the function's start, which knows nothing.
fn known_into(
    func: &Function,
    cfg: &ControlFlowGraph,
    domtree: &DomTree,
    cond: ValueId,
    mut block: BlockId,
) -> Option<Known> {
    loop {
        if func.layout.entry_block() == Some(block)
            || defined_in(func, cond, block)
            || !domtree.is_reachable(block)
        {
            return None;
        }
        block = match *cfg.preds_as_slice(block) {
            [pred] => {
                if let Some(known) = known_on_edge(func, cond, pred, block) {
                    return Some(known);
                }
                pred
            }
            _ => domtree.idom_of(block)?,
        };
    }
}

/// The values of `block` used outside it, other than by its successors'
/// phis on edges from it.
fn escaping_values(func: &Function, block: BlockId) -> SmallVec<[ValueId; 4]> {
    func.layout
        .iter_inst(block)
        .flat_map(|inst| func.dfg.inst_results(inst).iter().copied())
        .filter(|&value| {
            func.dfg.users(value).any(|&user| {
                func.layout.is_inst_inserted(user)
                    && func.layout.inst_block(user) != block
                    && !func.dfg.cast_phi(user).is_some_and(|phi| {
                        phi.args()
                            .iter()
                            .all(|(input, from)| *input != value || *from == block)
                    })
            })
        })
        .collect()
}

/// Threads every predecessor of `block` that can be. All are chosen, and
/// the block's values computed at their ends, before any edge moves:
/// retargeting one simplifies the block's phis that become trivial.
fn thread_block(editor: &mut CfgEditor<'_>, domtree: &DomTree, block: BlockId) -> bool {
    let Some(cand) = candidate(editor, domtree, block) else {
        return false;
    };
    let edges: Vec<_> = editor
        .cfg()
        .preds_of(block)
        .filter_map(|&pred| {
            let (edge_idx, dest) = threadable_edge(editor, domtree, block, &cand, pred)?;
            Some((pred, edge_idx, dest))
        })
        .collect();
    if edges.is_empty() {
        return false;
    }
    let threads: Vec<_> = edges
        .into_iter()
        .map(|(pred, edge_idx, dest)| Thread {
            pred,
            edge_idx,
            dest,
            values: values_at_end_of(editor.func_mut(), block, &cand, pred),
        })
        .collect();
    let escaping = escaping_values(editor.func(), block);
    if !escaping.is_empty() {
        repair_uses(editor, block, &escaping, &threads);
    }
    for thread in &threads {
        retarget(editor, block, thread);
    }
    true
}

/// A predecessor's edge into a threaded block, the successor it goes to
/// instead, and the block's values as the predecessor computes them.
struct Thread {
    pred: BlockId,
    edge_idx: usize,
    dest: BlockId,
    values: FxHashMap<ValueId, ValueId>,
}

/// Gives each use of `values`, defined in `block`, outside it the value its
/// path last defined once `threads` move: `block`'s own or that of a
/// threaded predecessor, with phis where paths from several meet.
fn repair_uses(editor: &mut CfgEditor<'_>, block: BlockId, values: &[ValueId], threads: &[Thread]) {
    // The CFG with the threads' edges moved, as far as the entry reaches.
    let target = |from: BlockId, to: BlockId| {
        threads
            .iter()
            .find(|thread| thread.pred == from && to == block)
            .map_or(to, |thread| thread.dest)
    };
    let func = editor.func();
    let cfg = editor.cfg();
    let mut reachable = SecondaryMap::<BlockId, bool>::default();
    let mut stack: Vec<_> = func.layout.entry_block().into_iter().collect();
    while let Some(from) = stack.pop() {
        if !std::mem::replace(&mut reachable[from], true) {
            stack.extend(cfg.succs_of(from).map(|&to| target(from, to)));
        }
    }
    let mut ssa = SsaBuilder::new();
    for from in func.layout.iter_block().filter(|&from| reachable[from]) {
        let mut seen = SmallVec::<[BlockId; 4]>::new();
        for &to in cfg.succs_of(from) {
            let to = target(from, to);
            if !seen.contains(&to) {
                seen.push(to);
                ssa.append_pred(to, from);
            }
        }
    }

    let func = editor.func_mut();
    ssa.seal_all(func);
    let reached = |func: &Function, user: InstId| {
        func.layout.is_inst_inserted(user) && {
            let at = func.layout.inst_block(user);
            at != block && reachable[at]
        }
    };
    for &value in values {
        let var = ssa.declare_var(func.dfg.value_ty(value));
        ssa.def_var(var, value, block);
        for thread in threads {
            ssa.def_var(var, thread.values[&value], thread.pred);
        }
        let users: Vec<_> = func
            .dfg
            .users(value)
            .copied()
            .filter(|&user| reached(func, user))
            .collect();
        for user in users {
            if func.dfg.is_phi(user) {
                let froms: SmallVec<[BlockId; 2]> = func
                    .dfg
                    .cast_phi(user)
                    .expect("phi")
                    .args()
                    .iter()
                    .filter(|&&(input, from)| input == value && from != block && reachable[from])
                    .map(|&(_, from)| from)
                    .collect();
                for from in froms {
                    let reaching = ssa.use_var(func, var, from);
                    func.dfg.edit_phi(user, |phi| {
                        for (input, at) in phi.args_mut() {
                            if *input == value && *at == from {
                                *input = reaching;
                            }
                        }
                    });
                }
            } else {
                let reaching = ssa.use_var(func, var, func.layout.inst_block(user));
                let mut inst = func.dfg.clone_inst(user);
                inst.for_each_value_mut(&mut |operand| {
                    if *operand == value {
                        *operand = reaching;
                    }
                });
                func.dfg.replace_inst(user, inst);
            }
        }
    }
}

/// The edge `pred -> block` and the successor its known condition selects,
/// when `pred` enters once, does not already branch there, and may run the
/// block's body on its other successors' paths.
fn threadable_edge(
    editor: &CfgEditor<'_>,
    domtree: &DomTree,
    block: BlockId,
    cand: &Candidate,
    pred: BlockId,
) -> Option<(usize, BlockId)> {
    let func = editor.func();
    if pred == block {
        return None;
    }
    let known = match cand.cond {
        Cond::Local(cond) => Known::Is(incoming_cond(func, block, cand, cond, pred)?),
        Cond::Dominating(cond) => known_on_edge(func, cond, pred, block)
            .or_else(|| known_into(func, editor.cfg(), domtree, cond, pred))?,
    };
    let dest = match known {
        Known::Is(imm) => cand
            .cases
            .iter()
            .find(|(key, _)| *key == imm)
            .map(|&(_, dest)| dest)
            .or(cand.default)?,
        Known::Not(values) => cand
            .cases
            .iter()
            .all(|(key, _)| values.contains(key))
            .then_some(cand.default)??,
    };
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

/// The values of `block` as `pred` would see them: its phis' incoming values
/// from `pred`, and its body recomputed at the end of `pred`.
fn values_at_end_of(
    func: &mut Function,
    block: BlockId,
    cand: &Candidate,
    pred: BlockId,
) -> FxHashMap<ValueId, ValueId> {
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
    map
}

/// Moves `thread`'s edge into `block` to its successor. The successor's phis
/// take, from the predecessor, what they took from the block, unless the
/// repair of the block's uses gave them an input from it already.
fn retarget(editor: &mut CfgEditor<'_>, block: BlockId, thread: &Thread) {
    let func = editor.func_mut();
    let dest_phis: Vec<_> = func
        .layout
        .iter_inst(thread.dest)
        .take_while(|inst| func.dfg.is_phi(*inst))
        .collect();
    let phi_inputs: Vec<_> = dest_phis
        .into_iter()
        .map(|phi_inst| {
            let args = func.dfg.cast_phi(phi_inst).expect("phi").args();
            let input = args
                .iter()
                .find(|(_, from)| *from == thread.pred)
                .map(|&(value, _)| value)
                .unwrap_or_else(|| {
                    let from_block = args
                        .iter()
                        .find(|(_, from)| *from == block)
                        .map(|&(value, _)| value)
                        .expect("a successor's phi has an input from the block");
                    thread
                        .values
                        .get(&from_block)
                        .copied()
                        .unwrap_or(from_block)
                });
            (phi_inst, input)
        })
        .collect();
    remove_phi_incoming_from(func, thread.dest, thread.pred);
    editor.retarget_out_edge(thread.pred, thread.edge_idx, thread.dest, &phi_inputs);
}
