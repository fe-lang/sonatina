use crate::bitset::BitSet;
use smallvec::SmallVec;
use sonatina_ir::{InstId, ValueId};

use super::{
    Planner,
    normalize::SpillAwareCostModel,
    normalize_search::{
        CostModel, NormalizePlan, SearchCfg, cost_for_steps, solve_optimal_operand_prep_plan,
    },
};

use super::super::{CONSUME_LAST_USE_MAX_SWAPS, sym_stack::StackItem};

fn commutative_plan_cmp_key(
    plan: &NormalizePlan,
    cost: &impl CostModel,
) -> (
    super::normalize_search::Cost,
    super::normalize_search::Cost,
    usize,
) {
    (
        cost_for_steps(&plan.steps, &plan.key_infos, cost),
        plan.cost,
        plan.steps.len(),
    )
}

impl<'a, 'ctx: 'a> Planner<'a, 'ctx> {
    fn inst_is_commutative(&self, inst: InstId) -> bool {
        use sonatina_ir::{
            InstDowncast,
            inst::{arith, cmp, logic},
        };

        let isb = self.ctx.func.inst_set();
        let inst = self.ctx.func.dfg.inst(inst);

        <&arith::Add as InstDowncast>::downcast(isb, inst).is_some()
            || <&arith::Mul as InstDowncast>::downcast(isb, inst).is_some()
            || <&logic::And as InstDowncast>::downcast(isb, inst).is_some()
            || <&logic::Or as InstDowncast>::downcast(isb, inst).is_some()
            || <&logic::Xor as InstDowncast>::downcast(isb, inst).is_some()
            || <&cmp::Eq as InstDowncast>::downcast(isb, inst).is_some()
            || <&cmp::Ne as InstDowncast>::downcast(isb, inst).is_some()
    }

    fn prepare_operands_maybe_commutative(
        &mut self,
        args: &mut SmallVec<[ValueId; 8]>,
        consume_last_use: &BitSet<ValueId>,
        commutative_pair: bool,
    ) {
        // If all operands are last-use values that are already in the required order on the
        // current stack top, avoid the operand-preparation machinery entirely. The instruction
        // will consume them directly.
        if !args.is_empty()
            && args.iter().all(|&v| consume_last_use.contains(v))
            && self.stack_prefix_matches(args)
        {
            return;
        }

        // For commutative binary ops, try both operand orders and choose the cheaper
        // operand-preparation plan. This is purely a bytecode optimization (SSA semantics are
        // unchanged).
        if commutative_pair && args.len() == 2 && args[0] != args[1] {
            // Fast path: if the operands are last-use and already occupy the top two stack slots
            // (in either order), use that order and consume them as-is.
            if consume_last_use.contains(args[0]) && consume_last_use.contains(args[1]) {
                if self.stack_prefix_matches(args) {
                    return;
                }
                let mut swapped: SmallVec<[ValueId; 8]> = args.clone();
                swapped.swap(0, 1);
                if self.stack_prefix_matches(&swapped) {
                    args.swap(0, 1);
                    return;
                }
            }

            let cost = SpillAwareCostModel::new(self.mem.spill_set());
            let search_cfg = self.operand_prep_search_cfg(args.len());

            let original_plan = solve_optimal_operand_prep_plan(
                self.ctx,
                self.stack,
                args.as_slice(),
                consume_last_use,
                &cost,
                search_cfg,
            );

            let mut swapped_args = args.clone();
            swapped_args.swap(0, 1);
            let swapped_plan = solve_optimal_operand_prep_plan(
                self.ctx,
                self.stack,
                swapped_args.as_slice(),
                consume_last_use,
                &cost,
                search_cfg,
            );

            let (plan, swapped) = match (original_plan, swapped_plan) {
                (Some(p), None) => (p, false),
                (None, Some(p)) => (p, true),
                (Some(p0), Some(p1)) => {
                    let c0 = commutative_plan_cmp_key(&p0, &cost);
                    let c1 = commutative_plan_cmp_key(&p1, &cost);
                    if c1 < c0 { (p1, true) } else { (p0, false) }
                }
                (None, None) => {
                    self.prepare_operands_greedy(args.as_slice(), consume_last_use);
                    return;
                }
            };

            if swapped {
                args.swap(0, 1);
            }
            if !self.apply_operand_prep_plan(&plan, args.as_slice()) {
                self.prepare_operands_greedy(args.as_slice(), consume_last_use);
            }
            return;
        }

        self.prepare_operands(args.as_slice(), consume_last_use);
    }

    pub(in super::super) fn prepare_operands_for_inst(
        &mut self,
        inst: InstId,
        args: &mut SmallVec<[ValueId; 8]>,
        consume_last_use: &BitSet<ValueId>,
    ) {
        self.prepare_operands_maybe_commutative(
            args,
            consume_last_use,
            self.inst_is_commutative(inst),
        );
    }

    pub(in super::super) fn prepare_operands_for_commutative_pair(
        &mut self,
        args: &mut SmallVec<[ValueId; 8]>,
        consume_last_use: &BitSet<ValueId>,
    ) {
        self.prepare_operands_maybe_commutative(args, consume_last_use, true);
    }

    fn stack_prefix_matches(&self, args: &[ValueId]) -> bool {
        if self.stack.len_above_func_ret() < args.len() {
            return false;
        }
        self.stack
            .iter()
            .take(args.len())
            .zip(args.iter().copied())
            .all(|(item, arg)| item == &StackItem::Value(arg))
    }

    fn operand_prep_search_cfg(&self, args_len: usize) -> SearchCfg {
        let max_len = if args_len > self.ctx.reach.swap_max {
            args_len.min(21)
        } else {
            self.ctx.reach.swap_max
        };
        SearchCfg {
            dup_max: self.ctx.reach.dup_max,
            swap_max: self.ctx.reach.swap_max,
            max_len,
            max_expansions: 50_000,
        }
    }

    pub(super) fn apply_operand_prep_plan(
        &mut self,
        plan: &super::normalize_search::NormalizePlan,
        args: &[ValueId],
    ) -> bool {
        let stack_before = self.stack.clone();
        let actions_before = self.actions.len();
        let mem_before = self.mem.snapshot();

        for step in plan.steps.iter().copied() {
            if !self.replay_normalize_step(step, &plan.key_infos) {
                *self.stack = stack_before;
                self.actions.truncate(actions_before);
                self.mem.restore(mem_before);
                return false;
            }
        }

        if !self.rename_immediate_slots_to_match(args) || !self.stack_prefix_matches(args) {
            *self.stack = stack_before;
            self.actions.truncate(actions_before);
            self.mem.restore(mem_before);
            return false;
        }

        true
    }

    pub(in super::super) fn prepare_operands(
        &mut self,
        args: &[ValueId],
        consume_last_use: &BitSet<ValueId>,
    ) {
        if args.is_empty() {
            return;
        }

        let cost = SpillAwareCostModel::new(self.mem.spill_set());
        let search_cfg = self.operand_prep_search_cfg(args.len());

        let Some(plan) = solve_optimal_operand_prep_plan(
            self.ctx,
            self.stack,
            args,
            consume_last_use,
            &cost,
            search_cfg,
        ) else {
            self.prepare_operands_greedy(args, consume_last_use);
            return;
        };

        if !self.apply_operand_prep_plan(&plan, args) {
            self.prepare_operands_greedy(args, consume_last_use);
        }
    }

    fn prepare_operands_greedy(&mut self, args: &[ValueId], consume_last_use: &BitSet<ValueId>) {
        // Iterate in reverse so the final stack order is `args[0]` on top, then `args[1]`, ...
        let mut prepared: usize = 0;
        let mut consumed_from_stack: BitSet<ValueId> = BitSet::default();
        for &v in args.iter().rev() {
            if self.ctx.func.dfg.value_is_imm(v) {
                let imm = self
                    .ctx
                    .func
                    .dfg
                    .value_imm(v)
                    .expect("imm value missing payload");
                self.stack.push_imm(v, imm, self.actions);
                prepared += 1;
                continue;
            }

            // If this is a last-use, prefer consuming an existing stack copy (stable-rotated
            // to the top) instead of duplicating it, but only when the swap chain is small.
            //
            // This is equivalent to a stable delete, except the pop is performed by the
            // instruction consuming its operands.
            if consume_last_use.contains(v)
                && !consumed_from_stack.contains(v)
                && let Some(pos) =
                    self.stack
                        .find_reachable_value_from(v, prepared, self.ctx.reach.swap_max)
                && pos <= CONSUME_LAST_USE_MAX_SWAPS
            {
                self.stack.stable_rotate_to_top(pos, self.actions);
                consumed_from_stack.insert(v);
                prepared += 1;
                continue;
            }

            if let Some(pos) = self.stack.find_reachable_value(v, self.ctx.reach.dup_max) {
                self.stack.dup(pos, self.actions);
                prepared += 1;
            } else if let Some(pos) =
                self.stack
                    .find_reachable_value_from(v, prepared, self.ctx.reach.swap_max)
            {
                self.stack.stable_rotate_to_top(pos, self.actions);
                self.stack.dup(0, self.actions);
                prepared += 1;
            } else {
                self.push_value_from_spill_slot_or_mark(v, v);
                prepared += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stackalloc::stackify::planner::normalize_search::{Cost, EstimatedCostModel, Step};

    #[test]
    fn commutative_plan_comparison_uses_emitted_step_cost() {
        let cost = EstimatedCostModel::default();
        let cheaper_emitted = NormalizePlan {
            cost: Cost { gas: 99, bytes: 99 },
            steps: vec![Step::Dup(0)],
            key_infos: Vec::new(),
            goal_keys: Vec::new(),
        };
        let pricier_emitted = NormalizePlan {
            cost: Cost::default(),
            steps: vec![Step::Swap(1), Step::Swap(1)],
            key_infos: Vec::new(),
            goal_keys: Vec::new(),
        };

        assert!(
            commutative_plan_cmp_key(&cheaper_emitted, &cost)
                < commutative_plan_cmp_key(&pricier_emitted, &cost)
        );
    }
}
