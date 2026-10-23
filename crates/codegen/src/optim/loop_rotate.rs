//! Loop rotation: test a loop's exit condition at the bottom of each iteration
//! instead of the top.
//!
//! A loop whose header ends in the exit test,
//!
//! ```text
//! preheader: ...; jump header
//! header:    x = phi (x0 preheader) (x1 latch); c = lt x n; br c body exit
//! body:      ...
//! latch:     ...; jump header
//! ```
//!
//! runs both the header's branch and the latch's jump back to it on every
//! iteration. Rotation copies the header's instructions to the end of the
//! preheader, where they guard the loop entry, and to the end of the latch,
//! where they test whether to run another iteration. The header is deleted:
//!
//! ```text
//! preheader: c0 = lt x0 n; br c0 body exit
//! body:      x = phi (x0 preheader) (x1 latch); ...
//! latch:     ...; c1 = lt x1 n; br c1 body exit
//! ```
//!
//! An iteration then ends in one conditional branch, which on the EVM saves
//! the `PUSH`/`JUMP` back to the header and its `JUMPDEST`. The copies run
//! exactly when the header did, the guard on entry and the latch's after each
//! iteration; only the code grows. A header value used in the loop takes a
//! phi in the body's first block, and one used after the exit takes a phi in
//! the exit block.
//!
//! As in LLVM's LoopRotate, the loop must have a single latch, the in-loop
//! successor must be entered only from the header, and the exit may also be
//! entered from inside the loop but not from elsewhere.

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, InstId, Value, ValueId,
    inst::control_flow::{Br, BranchKind, Phi},
};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode, clone_inst_before, defined_in, iter_phis_in_block},
    domtree::DomTree,
    loop_analysis::LoopTree,
};

/// The most non-phi header instructions copied into the preheader and latch.
const MAX_HEADER_INSTS: usize = 8;

#[derive(Default)]
pub struct LoopRotate;

impl LoopRotate {
    pub fn new() -> Self {
        Self
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        let mut domtree = DomTree::new();
        let mut lpt = LoopTree::new();
        domtree.compute(editor.cfg());
        lpt.compute(editor.cfg(), &domtree);
        // Inner loops first: rotating one gives it a preheader, which becomes
        // the single-entry body its outer loop needs.
        let headers: Vec<_> = lpt.loops().rev().map(|lp| lpt.loop_header(lp)).collect();

        let mut changed = false;
        let mut stale = false;
        for header in headers {
            if stale {
                domtree.compute(editor.cfg());
                lpt.compute(editor.cfg(), &domtree);
                stale = false;
            }
            if let Some(plan) = plan(&editor, &domtree, &lpt, header) {
                rotate(&mut editor, &plan);
                changed = true;
                stale = true;
            }
        }
        changed
    }
}

/// A loop that can be rotated, and where its header's values are used.
struct Plan {
    header: BlockId,
    latch: BlockId,
    /// The latch's back edge, when the latch has other successors.
    split_latch: Option<usize>,
    body: BlockId,
    exit: BlockId,
    /// Whether the header enters the body when its condition is nonzero.
    body_on_nonzero: bool,
    cond: ValueId,
    insts: SmallVec<[InstId; MAX_HEADER_INSTS]>,
    uses: Vec<OuterUse>,
    /// Header values that take a phi in the body, in header order.
    body_values: Vec<ValueId>,
    /// Header values that take a phi in the exit, in header order.
    exit_values: Vec<ValueId>,
}

/// A use of a header value outside the header, other than a phi input on an
/// edge from the header.
struct OuterUse {
    user: InstId,
    value: ValueId,
    /// The predecessor a phi user takes `value` from.
    pred: Option<BlockId>,
    /// Whether the use is dominated by the exit rather than the body.
    after_exit: bool,
}

fn plan(
    editor: &CfgEditor<'_>,
    domtree: &DomTree,
    lpt: &LoopTree,
    header: BlockId,
) -> Option<Plan> {
    let func = editor.func();
    let cfg = editor.cfg();
    let lp = lpt
        .loop_of_block(header)
        .filter(|&lp| lpt.loop_header(lp) == header)?;
    if func.layout.entry_block() == Some(header) {
        return None;
    }

    let mut latches = cfg
        .preds_of(header)
        .copied()
        .filter(|&pred| lpt.is_in_loop(pred, lp));
    let latch = latches.next()?;
    if latches.next().is_some() || latch == header {
        return None;
    }
    // A latch that also exits, such as a checked increment's overflow branch,
    // gets the back edge split off into a block that can end in the test.
    let latch_dests = func
        .dfg
        .branch_info(func.layout.last_inst_of(latch)?)?
        .dests();
    let mut back_edges = latch_dests
        .iter()
        .enumerate()
        .filter(|(_, dest)| **dest == header)
        .map(|(edge_idx, _)| edge_idx);
    let back_edge = back_edges.next()?;
    if back_edges.next().is_some() {
        return None;
    }
    let split_latch = (latch_dests.len() > 1).then_some(back_edge);
    // A reused preheader must jump to the header, so it can branch instead.
    let mut outside = cfg.preds_of(header).copied().filter(|&pred| pred != latch);
    let first_outside = outside.next()?;
    if outside.next().is_none()
        && cfg.succs_of(first_outside).count() == 1
        && !matches!(
            func.dfg
                .branch_info(func.layout.last_inst_of(first_outside)?)?
                .branch_kind(),
            BranchKind::Jump(_)
        )
    {
        return None;
    }

    let term = func.layout.last_inst_of(header)?;
    let BranchKind::Br(br) = func.dfg.branch_info(term)?.branch_kind() else {
        return None;
    };
    let (cond, nz_dest, z_dest) = (*br.cond(), *br.nz_dest(), *br.z_dest());
    let (body, exit, body_on_nonzero) =
        match (lpt.is_in_loop(nz_dest, lp), lpt.is_in_loop(z_dest, lp)) {
            (true, false) => (nz_dest, z_dest, true),
            (false, true) => (z_dest, nz_dest, false),
            _ => return None,
        };
    // The loop tree also counts unreachable blocks that branch into the loop
    // as members; an exit edge from one has no body version of a header value.
    if body == header
        || cfg.preds_of(body).any(|&pred| pred != header)
        || cfg.preds_of(exit).any(|&pred| {
            pred != header && !(lpt.is_in_loop(pred, lp) && domtree.dominates(body, pred))
        })
    {
        return None;
    }

    let mut insts = SmallVec::new();
    for inst in func.layout.iter_inst(header) {
        if inst == term {
            break;
        }
        if func.dfg.is_phi(inst) {
            continue;
        }
        // The copies run exactly where the header did, so a read would be
        // safe to copy; but the body could then no longer reuse the header's
        // one read through load forwarding. Calls are too large to copy.
        if insts.len() == MAX_HEADER_INSTS
            || func.dfg.is_call(inst)
            || !func.dfg.can_speculate(inst)
        {
            return None;
        }
        insts.push(inst);
    }

    // Every header value is defined by a phi or a copied instruction.
    let values: Vec<ValueId> = func
        .layout
        .iter_inst(header)
        .flat_map(|inst| func.dfg.inst_results(inst).iter().copied())
        .collect();
    let header_phi_input = |value: ValueId, from: BlockId| {
        let inst = func.dfg.value_inst(value)?;
        let phi = func.dfg.cast_phi(inst)?;
        phi.args()
            .iter()
            .find(|(_, pred)| *pred == from)
            .map(|(input, _)| *input)
    };
    // Every block of the loop but the header is dominated by the body, and a
    // value used past the exit edge is dominated by the exit.
    let after_exit = |block: BlockId| {
        if domtree.dominates(body, block) {
            Some(false)
        } else {
            domtree.dominates(exit, block).then_some(true)
        }
    };

    let mut uses = Vec::new();
    for &value in &values {
        for &user in func.dfg.users(value) {
            if !func.layout.is_inst_inserted(user) {
                continue;
            }
            let block = func.layout.inst_block(user);
            if block == header {
                continue;
            }
            if let Some(phi) = func.dfg.cast_phi(user) {
                for &(input, pred) in phi.args() {
                    if input == value && pred != header {
                        uses.push(OuterUse {
                            user,
                            value,
                            pred: Some(pred),
                            after_exit: after_exit(pred)?,
                        });
                    }
                }
            } else {
                uses.push(OuterUse {
                    user,
                    value,
                    pred: None,
                    after_exit: after_exit(block)?,
                });
            }
        }
    }

    // A header value needs a body phi when it is used in the loop, or reaches
    // the exit from inside the loop. Its latch-side input is the next header's
    // value: a header phi's input from the latch, which is a body phi in turn
    // if it is itself a header value.
    let is_header_value = |value: ValueId| defined_in(func, value, header);
    let exit_entered_from_loop = cfg.preds_of(exit).count() > 1;
    let mut exit_set = FxHashSet::default();
    let mut body_set = FxHashSet::default();
    let mut work = Vec::new();
    for use_ in &uses {
        if use_.after_exit {
            exit_set.insert(use_.value);
            work.push(use_.value);
            if exit_entered_from_loop {
                body_set.insert(use_.value);
            }
        } else {
            body_set.insert(use_.value);
            work.push(use_.value);
        }
    }
    // Copies, the condition and the edge inputs of the body and exit phis all
    // read header values as of the next header entry.
    for &inst in &insts {
        work.extend(func.dfg.inst(inst).collect_values());
    }
    work.push(cond);
    for block in [body, exit] {
        for phi in iter_phis_in_block(func, block) {
            work.extend(header_phi_input(func.dfg.inst_result(phi)?, header));
        }
    }
    let mut seen = FxHashSet::default();
    while let Some(value) = work.pop() {
        if !seen.insert(value) || !is_header_value(value) {
            continue;
        }
        if let Some(input) = header_phi_input(value, latch)
            && is_header_value(input)
        {
            body_set.insert(input);
            work.push(input);
        }
    }
    let body_values = values
        .iter()
        .copied()
        .filter(|value| body_set.contains(value))
        .collect();
    let exit_values = values
        .iter()
        .copied()
        .filter(|value| exit_set.contains(value))
        .collect();

    Some(Plan {
        header,
        latch,
        split_latch,
        body,
        exit,
        body_on_nonzero,
        cond,
        insts,
        uses,
        body_values,
        exit_values,
    })
}

fn rotate(editor: &mut CfgEditor<'_>, plan: &Plan) {
    let latch = match plan.split_latch {
        Some(edge_idx) => editor.split_out_edge(plan.latch, edge_idx),
        None => plan.latch,
    };
    let outside: SmallVec<[BlockId; 4]> = editor
        .cfg()
        .preds_of(plan.header)
        .copied()
        .filter(|&pred| pred != latch)
        .collect();
    let preheader = editor
        .create_or_reuse_loop_preheader(plan.header, &outside)
        .expect("a non-entry loop header has an outside predecessor");
    let exit_preds: SmallVec<[BlockId; 4]> = editor
        .cfg()
        .preds_of(plan.exit)
        .copied()
        .filter(|&pred| pred != plan.header)
        .collect();
    let func = editor.func_mut();
    let body_old_phis: Vec<_> = iter_phis_in_block(func, plan.body).collect();
    let exit_old_phis: Vec<_> = iter_phis_in_block(func, plan.exit).collect();

    let body_phis: FxHashMap<ValueId, ValueId> = plan
        .body_values
        .iter()
        .rev()
        .map(|&value| {
            let phi = func.dfg.make_phi(SmallVec::new());
            (value, prepend_phi(func, plan.body, phi, value))
        })
        .collect();

    // Header values as the guard sees them, and as the latch sees them for the
    // next iteration: the header phis' inputs, then the copied instructions.
    let mut on_entry = FxHashMap::default();
    let mut on_latch = FxHashMap::default();
    for phi_inst in iter_phis_in_block(func, plan.header).collect::<Vec<_>>() {
        let phi = func.dfg.cast_phi(phi_inst).expect("phi");
        let result = func.dfg.inst_result(phi_inst).expect("a phi has a result");
        for &(input, pred) in phi.args() {
            if pred == preheader {
                on_entry.insert(result, input);
            } else {
                // Only phis whose latch version is needed get one.
                let input = body_phis.get(&input).copied().unwrap_or(input);
                if !defined_in(func, input, plan.header) {
                    on_latch.insert(result, input);
                }
            }
        }
    }
    let preheader_term = func
        .layout
        .last_inst_of(preheader)
        .expect("terminated block");
    let latch_term = func.layout.last_inst_of(latch).expect("terminated block");
    for &inst in &plan.insts {
        clone_inst_before(func, inst, preheader_term, &mut on_entry);
        clone_inst_before(func, inst, latch_term, &mut on_latch);
    }
    let entry_value = |value: ValueId| on_entry.get(&value).copied().unwrap_or(value);
    let latch_value = |value: ValueId| {
        on_latch.get(&value).copied().unwrap_or_else(|| {
            assert!(
                !defined_in(func, value, plan.header),
                "header value {value:?} has no latch version"
            );
            value
        })
    };

    let body_args: Vec<_> = plan
        .body_values
        .iter()
        .map(|&value| {
            (
                body_phis[&value],
                [(entry_value(value), preheader), (latch_value(value), latch)],
            )
        })
        .collect();
    let exit_args: Vec<_> = plan
        .exit_values
        .iter()
        .map(|&value| {
            let mut args: SmallVec<[(ValueId, BlockId); 4]> =
                smallvec![(entry_value(value), preheader), (latch_value(value), latch)];
            args.extend(exit_preds.iter().map(|&pred| (body_phis[&value], pred)));
            (value, args)
        })
        .collect();
    let old_phi_args: Vec<_> = body_old_phis
        .iter()
        .chain(&exit_old_phis)
        .map(|&phi_inst| {
            let phi = func.dfg.cast_phi(phi_inst).expect("phi");
            let input = phi
                .args()
                .iter()
                .find(|(_, pred)| *pred == plan.header)
                .map(|(input, _)| *input)
                .expect("a successor phi has an input from the header");
            (phi_inst, entry_value(input), latch_value(input))
        })
        .collect();
    let cond = [entry_value(plan.cond), latch_value(plan.cond)];

    for (phi, args) in body_args {
        let phi = func.dfg.value_inst(phi).expect("a body phi result");
        for (input, pred) in args {
            func.dfg.append_phi_arg(phi, input, pred);
        }
    }
    let exit_phis: FxHashMap<ValueId, ValueId> = exit_args
        .into_iter()
        .rev()
        .map(|(value, args)| {
            let phi = func.dfg.make_phi(args.into_iter().collect());
            (value, prepend_phi(func, plan.exit, phi, value))
        })
        .collect();
    for (phi_inst, on_entry, on_latch) in old_phi_args {
        func.dfg.edit_phi(phi_inst, |phi| {
            phi.retain(|pred| pred != plan.header);
            phi.append_phi_arg(on_entry, preheader);
            phi.append_phi_arg(on_latch, latch);
        });
    }

    for use_ in &plan.uses {
        let new = if use_.after_exit {
            exit_phis[&use_.value]
        } else {
            body_phis[&use_.value]
        };
        if let Some(pred) = use_.pred {
            func.dfg.edit_phi(use_.user, |phi| {
                for (input, from) in phi.args_mut() {
                    if *input == use_.value && *from == pred {
                        *input = new;
                    }
                }
            });
        } else {
            let mut inst = func.dfg.clone_inst(use_.user);
            inst.for_each_value_mut(&mut |value| {
                if *value == use_.value {
                    *value = new;
                }
            });
            func.dfg.replace_inst(use_.user, inst);
        }
    }

    for (block, cond) in [(preheader, cond[0]), (latch, cond[1])] {
        let (nz_dest, z_dest) = if plan.body_on_nonzero {
            (plan.body, plan.exit)
        } else {
            (plan.exit, plan.body)
        };
        let term = func.layout.last_inst_of(block).expect("terminated block");
        let br = Br::new_unchecked(func.inst_set(), cond, nz_dest, z_dest);
        func.dfg.replace_inst(term, Box::new(br));
    }

    editor.recompute_cfg();
    editor.delete_blocks_unreachable(&[plan.header]);
}

/// Prepends `phi` to `block` as a phi of `value`'s type.
fn prepend_phi(func: &mut Function, block: BlockId, phi: Phi, value: ValueId) -> ValueId {
    let inst = func.dfg.make_inst(phi);
    let result = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty: func.dfg.value_ty(value),
    });
    func.dfg.attach_results(inst, &[result]);
    func.layout.prepend_inst(inst, block);
    result
}
