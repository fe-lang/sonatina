use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Immediate, InstId, ValueId,
    inst::{
        BinaryInstKind, InstClassKind,
        control_flow::{Br, BranchKind},
    },
};

use super::branch_canonicalize::{
    compare_value, insert_compare_before, remove_dead_single_result_inst,
};
use crate::range_analysis::imm_to_unsigned;

/// Strengthens the first of a run of bounds checks `lt (b + k) n`, on one
/// base `b` with constant offsets `k` and one constant bound `n`, to cover
/// the whole run, so that `RangeBranchSimplify` folds the later ones.
///
/// A run starts at a check that continues on its true edge and otherwise
/// fails to a block `f`. Each later block runs only right after the previous
/// one: that is its only predecessor, and it is not the entry block, which
/// the function's callers also enter. It makes no call, has no write,
/// allocation or control effect, and ends in a jump, a branch on a constant,
/// or a branch with one edge to `f` that passes `f` the same arguments: a
/// member of the run, or another check failing to `f` the same way. Where a
/// later check fails, failing at the first one instead skips only
/// instructions whose results nothing after `f` sees and that change
/// nothing, and reaches `f` the same way; where every check passes, the same
/// instructions run as before.
///
/// The first check becomes `lt b (n - k_max)` when the run checks `b < n`
/// itself and `n - 1 + k_max` does not wrap: then no member `b + k` of a
/// passing run wraps, so the run passes exactly when `b + k_max < n`. For
/// `n <= k_max` that is never, and the check becomes `lt b 0`. A run that
/// does not check `b < n` is left alone, since a member may wrap and pass:
/// with `b` the type's maximum, `b + 1` and `b + 2` both lie below `n`.
#[derive(Default)]
pub struct MergeIndexChecks;

impl MergeIndexChecks {
    pub fn run(&mut self, func: &mut Function, cfg: &ControlFlowGraph) -> bool {
        let mut offsets = FxHashMap::default();
        let mut fail_args =
            FxHashMap::<BlockId, FxHashMap<BlockId, SmallVec<[ValueId; 4]>>>::default();
        let mut walked = SecondaryMap::<BlockId, bool>::default();
        let mut merges = Vec::new();
        let mut blocks: Vec<_> = cfg.post_order().collect();
        blocks.reverse();

        for first in blocks {
            if walked[first] {
                continue;
            }
            let Some(head) = index_check(func, first, &mut offsets) else {
                continue;
            };
            let fail = head.fail;
            let args = fail_args.entry(fail).or_insert_with(|| {
                let mut args = FxHashMap::<_, SmallVec<_>>::default();
                for phi in func
                    .layout
                    .iter_inst(fail)
                    .map_while(|inst| func.dfg.cast_phi(inst))
                {
                    for &(value, pred) in phi.args() {
                        args.entry(pred).or_default().push(value);
                    }
                }
                args
            });
            let head_args = args.get(&first);

            // A check on the walk that fails to `fail` heads a run that is the
            // rest of this walk, so one walk serves them all and no block is
            // walked twice.
            let mut checks = vec![head];
            let mut block = checks[0].pass;
            while cfg.pred_num_of(block) == 1
                && cfg.entry() != Some(block)
                && func.layout.iter_inst(block).all(|inst| {
                    func.dfg.is_terminator(inst)
                        || (!func.dfg.is_call(inst) && {
                            let effects = func.dfg.effect_summary(inst);
                            !effects.may_mutate_state() && !effects.may_transfer_control()
                        })
                })
                && let Some(term) = func.layout.last_inst_of(block)
                && let Some(branch) = func.dfg.branch_info(term)
            {
                let (next, exits) = match branch.branch_kind() {
                    BranchKind::Jump(jump) => (*jump.dest(), false),
                    BranchKind::Br(br) => match func.dfg.value_imm(*br.cond()) {
                        Some(cond) if cond.is_zero() => (*br.z_dest(), false),
                        Some(_) => (*br.nz_dest(), false),
                        None if *br.z_dest() == fail => (*br.nz_dest(), true),
                        None if *br.nz_dest() == fail => (*br.z_dest(), true),
                        None => break,
                    },
                    BranchKind::BrTable(_) => break,
                };
                if next == fail || (exits && args.get(&block) != head_args) {
                    break;
                }
                if let Some(check) = index_check(func, block, &mut offsets)
                    && (check.pass, check.fail) == (next, fail)
                {
                    walked[block] = true;
                    checks.push(check);
                }
                block = next;
            }

            // The run of a check is the later checks on its base and bound. The
            // first check whose run merges takes in the rest; each before it
            // heads a run that does not.
            let mut groups = FxHashMap::default();
            let mut runs = Vec::<Vec<IndexCheck>>::new();
            for check in checks {
                let group = *groups.entry((check.base, check.bound)).or_insert_with(|| {
                    runs.push(Vec::new());
                    runs.len() - 1
                });
                runs[group].push(check);
            }
            for mut run in runs {
                let bound = run[0].bound;
                let (last, empty) = bound.overflowing_usub(Immediate::one(bound.ty()));
                let (mut k_max, mut checks_base) = (Immediate::zero(bound.ty()), false);
                let mut merge = None;
                for (index, check) in run.iter().enumerate().rev() {
                    if imm_to_unsigned(check.offset) > imm_to_unsigned(k_max) {
                        k_max = check.offset;
                    }
                    checks_base |= check.offset.is_zero();
                    if index + 1 < run.len()
                        && checks_base
                        && !k_max.is_zero()
                        && !empty
                        && !last.overflowing_uadd(k_max).1
                    {
                        merge = Some((index, k_max));
                    }
                }
                if let Some((index, k_max)) = merge {
                    merges.push((run.swap_remove(index), k_max));
                }
            }
        }

        let changed = !merges.is_empty();
        for (head, k_max) in merges {
            let limit = func.dfg.make_imm_value(head.bound.saturating_usub(k_max));
            let cond_ty = func.dfg.value_ty(head.cond);
            let cond = insert_compare_before(
                func,
                head.term,
                head.cmp,
                BinaryInstKind::Lt,
                head.base,
                limit,
                cond_ty,
            );
            func.dfg.replace_inst(
                head.term,
                Box::new(Br::new_unchecked(
                    func.inst_set(),
                    cond,
                    head.pass,
                    head.fail,
                )),
            );
            remove_dead_single_result_inst(func, head.cmp);
        }
        changed
    }
}

/// A branch that continues to `pass` when `base + offset < bound` and
/// otherwise leaves for `fail`.
struct IndexCheck {
    term: InstId,
    cond: ValueId,
    cmp: InstId,
    pass: BlockId,
    fail: BlockId,
    base: ValueId,
    offset: Immediate,
    bound: Immediate,
}

/// `block`'s branch as an [`IndexCheck`] on a constant bound, its base past
/// every `add` of a constant. `offsets` keeps each value's base and offset,
/// so that a chain of adds is followed once however many checks share it.
fn index_check(
    func: &Function,
    block: BlockId,
    offsets: &mut FxHashMap<ValueId, (ValueId, Immediate)>,
) -> Option<IndexCheck> {
    let term = func.layout.last_inst_of(block)?;
    let br = func.dfg.downcast::<&Br>(term)?;
    let (cmp, BinaryInstKind::Lt, index, bound) = compare_value(func, *br.cond())? else {
        return None;
    };
    let bound = func
        .dfg
        .value_imm(bound)
        .filter(|bound| bound.ty().is_integral())?;
    let (mut value, mut steps) = (index, Vec::new());
    let (base, mut offset) = loop {
        if let Some(&known) = offsets.get(&value) {
            break known;
        }
        if let Some(inst) = func.dfg.value_inst(value)
            && let InstClassKind::Binary(BinaryInstKind::Add) = func.dfg.inst(inst).kind()
            && let [lhs, rhs] = func.dfg.inst(inst).collect_values().as_slice()
            && let Some(step) = func.dfg.value_imm(*rhs)
        {
            steps.push((value, step));
            value = *lhs;
        } else {
            break (value, Immediate::zero(bound.ty()));
        }
    };
    for (value, step) in steps.into_iter().rev() {
        offset = offset + step;
        offsets.insert(value, (base, offset));
    }
    (br.nz_dest() != br.z_dest()).then_some(IndexCheck {
        term,
        cond: *br.cond(),
        cmp,
        pass: *br.nz_dest(),
        fail: *br.z_dest(),
        base,
        offset,
        bound,
    })
}
