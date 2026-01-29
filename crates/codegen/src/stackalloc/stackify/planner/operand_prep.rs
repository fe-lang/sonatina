use crate::{
    bitset::BitSet,
    stackalloc::{Action, Actions},
};
use smallvec::SmallVec;
use sonatina_ir::{Function, InstId, ValueId};
use std::collections::{BinaryHeap, HashMap};

use super::{
    super::{CONSUME_LAST_USE_MAX_SWAPS, sym_stack::StackItem},
    MemPlan, Planner,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct OperandPrepMetric {
    /// Newly-discovered spill-set values (preferred to minimize).
    spill_requests: usize,
    /// Number of frame-slot loads emitted by operand preparation (preferred to minimize).
    mem_loads: usize,
    /// Number of `SWAP*` actions emitted by operand preparation (preferred to minimize).
    swaps: usize,
    /// Total actions emitted by operand preparation (tie-breaker).
    actions: usize,
}

struct BinaryOperandPrepPlan {
    actions: Actions,
    /// Stack above the function return barrier, after applying `actions`.
    final_stack: Vec<StackItem>,
    metric: OperandPrepMetric,
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

    pub(in super::super) fn prepare_operands_for_inst(
        &mut self,
        inst: InstId,
        args: &mut SmallVec<[ValueId; 8]>,
        consume_last_use: &BitSet<ValueId>,
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

        // For binary ops, solve operand preparation via a small exact search over `DUP*`/`SWAP*`
        // and choose the cheapest plan. This models "consume in place" correctly and avoids
        // redundant swap chains (common with the greedy per-operand preparation).
        if args.len() == 2 && args[0] != args[1] {
            let commutative = self.inst_is_commutative(inst);
            if self.try_prepare_operands_binary_via_search(args, consume_last_use, commutative) {
                return;
            }
        }

        // For commutative binary ops, try both operand orders and choose the cheaper
        // operand-preparation plan. This is purely a bytecode optimization (SSA semantics are
        // unchanged).
        if args.len() == 2 && args[0] != args[1] && self.inst_is_commutative(inst) {
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

            let original = self.simulate_operand_prep_metric(args, consume_last_use);

            let mut swapped: SmallVec<[ValueId; 8]> = args.clone();
            swapped.swap(0, 1);
            let swapped_metric = self.simulate_operand_prep_metric(&swapped, consume_last_use);

            if swapped_metric < original {
                args.swap(0, 1);
            }
        }
        self.prepare_operands(args, consume_last_use);
    }

    fn try_prepare_operands_binary_via_search(
        &mut self,
        args: &mut SmallVec<[ValueId; 8]>,
        consume_last_use: &BitSet<ValueId>,
        commutative: bool,
    ) -> bool {
        debug_assert_eq!(args.len(), 2);
        let order = [args[0], args[1]];
        let mut best: Option<(BinaryOperandPrepPlan, bool)> = self
            .search_binary_operand_prep(order, consume_last_use)
            .map(|p| (p, false));

        if commutative {
            let swapped_order = [args[1], args[0]];
            if let Some(swapped) = self.search_binary_operand_prep(swapped_order, consume_last_use)
            {
                let better = match &best {
                    None => true,
                    Some((cur, _)) => swapped.metric < cur.metric,
                };
                if better {
                    best = Some((swapped, true));
                }
            }
        }

        let Some((plan, swapped)) = best else {
            return false;
        };

        if swapped {
            args.swap(0, 1);
        }
        self.actions.extend_from_slice(&plan.actions);
        self.stack.replace_above_func_ret(plan.final_stack);
        true
    }

    fn search_binary_operand_prep(
        &self,
        target: [ValueId; 2],
        consume_last_use: &BitSet<ValueId>,
    ) -> Option<BinaryOperandPrepPlan> {
        const MAX_ACTIONS: usize = 12;

        let above_len = self.stack.len_above_func_ret();
        let initial: Vec<StackItem> = self.stack.iter().take(above_len).cloned().collect();

        // Only optimize when both operands can be produced without touching memory: either an
        // immediate, or already present within `SWAP16` reach.
        for v in target {
            if !self.ctx.func.dfg.value_is_imm(v) {
                let reachable = initial
                    .iter()
                    .take(self.ctx.reach.swap_max)
                    .any(|i| matches!(i, StackItem::Value(x) if *x == v));
                if !reachable {
                    return None;
                }
            }
        }

        let metric0 = OperandPrepMetric {
            spill_requests: 0,
            mem_loads: 0,
            swaps: 0,
            actions: 0,
        };

        fn preserve_needed(
            func: &Function,
            consume_last_use: &BitSet<ValueId>,
            v: ValueId,
        ) -> bool {
            !consume_last_use.contains(v) && !func.dfg.value_is_imm(v)
        }

        fn is_goal(
            func: &Function,
            state: &[StackItem],
            target: [ValueId; 2],
            consume_last_use: &BitSet<ValueId>,
        ) -> bool {
            if state.len() < 2 {
                return false;
            }
            if state[0] != StackItem::Value(target[0]) || state[1] != StackItem::Value(target[1]) {
                return false;
            }
            for v in target {
                if preserve_needed(func, consume_last_use, v) {
                    let copies = state
                        .iter()
                        .filter(|i| matches!(i, StackItem::Value(x) if *x == v))
                        .count();
                    if copies < 2 {
                        return false;
                    }
                }
            }
            true
        }

        #[derive(Clone)]
        struct HeapItem {
            metric: OperandPrepMetric,
            id: u64,
            state: Vec<StackItem>,
        }

        impl PartialEq for HeapItem {
            fn eq(&self, other: &Self) -> bool {
                self.metric == other.metric && self.id == other.id
            }
        }

        impl Eq for HeapItem {}

        impl PartialOrd for HeapItem {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for HeapItem {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                // Reverse the order for a min-heap; use a deterministic FIFO-ish tie-break.
                other
                    .metric
                    .cmp(&self.metric)
                    .then_with(|| other.id.cmp(&self.id))
            }
        }

        let mut best: HashMap<Vec<StackItem>, OperandPrepMetric> = HashMap::new();
        let mut prev: HashMap<Vec<StackItem>, (Vec<StackItem>, Action)> = HashMap::new();
        let mut heap: BinaryHeap<HeapItem> = BinaryHeap::new();

        best.insert(initial.clone(), metric0);
        heap.push(HeapItem {
            metric: metric0,
            id: 0,
            state: initial.clone(),
        });
        let mut next_id: u64 = 1;

        while let Some(item) = heap.pop() {
            let Some(&cur_best) = best.get(&item.state) else {
                continue;
            };
            if item.metric != cur_best || item.metric.actions > MAX_ACTIONS {
                continue;
            }

            if is_goal(self.ctx.func, &item.state, target, consume_last_use) {
                let mut actions: Vec<Action> = Vec::new();
                let mut cur = item.state.clone();
                while let Some((p, a)) = prev.get(&cur) {
                    actions.push(*a);
                    cur = p.clone();
                }
                actions.reverse();
                let mut out: Actions = Actions::new();
                out.extend(actions.into_iter());
                return Some(BinaryOperandPrepPlan {
                    actions: out,
                    final_stack: item.state,
                    metric: item.metric,
                });
            }

            // Neighbors: SWAP*, then DUP* for non-last-use operands, then PUSH for immediates.
            let max_swap = self
                .ctx
                .reach
                .swap_max
                .saturating_sub(1)
                .min(item.state.len().saturating_sub(1));
            for k in 1..=max_swap {
                let mut next_state = item.state.clone();
                next_state.swap(0, k);

                let next_metric = OperandPrepMetric {
                    swaps: item.metric.swaps + 1,
                    actions: item.metric.actions + 1,
                    ..item.metric
                };

                let update = best
                    .get(&next_state)
                    .map(|m| next_metric < *m)
                    .unwrap_or(true);
                if update {
                    best.insert(next_state.clone(), next_metric);
                    prev.insert(
                        next_state.clone(),
                        (item.state.clone(), Action::StackSwap(k as u8)),
                    );
                    heap.push(HeapItem {
                        metric: next_metric,
                        id: next_id,
                        state: next_state,
                    });
                    next_id += 1;
                }
            }

            for &v in target.iter() {
                let max_dup = self.ctx.reach.dup_max.min(item.state.len());
                if preserve_needed(self.ctx.func, consume_last_use, v)
                    && let Some(pos) = (0..max_dup).find(|&i| item.state[i] == StackItem::Value(v))
                {
                    let mut next_state = item.state.clone();
                    next_state.insert(0, StackItem::Value(v));

                    let next_metric = OperandPrepMetric {
                        actions: item.metric.actions + 1,
                        ..item.metric
                    };
                    let update = best
                        .get(&next_state)
                        .map(|m| next_metric < *m)
                        .unwrap_or(true);
                    if update {
                        best.insert(next_state.clone(), next_metric);
                        prev.insert(
                            next_state.clone(),
                            (item.state.clone(), Action::StackDup(pos as u8)),
                        );
                        heap.push(HeapItem {
                            metric: next_metric,
                            id: next_id,
                            state: next_state,
                        });
                        next_id += 1;
                    }
                }
            }

            for &v in target.iter() {
                if self.ctx.func.dfg.value_is_imm(v) {
                    let imm = self
                        .ctx
                        .func
                        .dfg
                        .value_imm(v)
                        .expect("imm value missing payload");
                    let mut next_state = item.state.clone();
                    next_state.insert(0, StackItem::Value(v));

                    let next_metric = OperandPrepMetric {
                        actions: item.metric.actions + 1,
                        ..item.metric
                    };
                    let update = best
                        .get(&next_state)
                        .map(|m| next_metric < *m)
                        .unwrap_or(true);
                    if update {
                        best.insert(next_state.clone(), next_metric);
                        prev.insert(next_state.clone(), (item.state.clone(), Action::Push(imm)));
                        heap.push(HeapItem {
                            metric: next_metric,
                            id: next_id,
                            state: next_state,
                        });
                        next_id += 1;
                    }
                }
            }
        }

        None
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

    fn simulate_operand_prep_metric(
        &self,
        args: &[ValueId],
        consume_last_use: &BitSet<ValueId>,
    ) -> OperandPrepMetric {
        let mut sim_stack = (*self.stack).clone();
        let mut sim_actions: Actions = Actions::new();
        let mut sim_spill_requests = self.mem.spill_requests().clone();
        let before_spill_requests = sim_spill_requests.len();

        let mut sim_free_slots = self.mem.free_slots().clone();
        let mut sim_slots = self.mem.slot_state().clone();

        {
            let mem = MemPlan::new(
                self.mem.spill_set(),
                &mut sim_spill_requests,
                self.ctx,
                &mut sim_free_slots,
                &mut sim_slots,
            );
            let mut planner = Planner::new(self.ctx, &mut sim_stack, &mut sim_actions, mem);
            planner.prepare_operands(args, consume_last_use);
        }

        let mem_loads = sim_actions
            .iter()
            .filter(|a| matches!(a, Action::MemLoadFrameSlot(_) | Action::MemLoadAbs(_)))
            .count();
        let swaps = sim_actions
            .iter()
            .filter(|a| matches!(a, Action::StackSwap(_)))
            .count();

        OperandPrepMetric {
            spill_requests: sim_spill_requests
                .len()
                .saturating_sub(before_spill_requests),
            mem_loads,
            swaps,
            actions: sim_actions.len(),
        }
    }

    pub(in super::super) fn prepare_operands(
        &mut self,
        args: &[ValueId],
        consume_last_use: &BitSet<ValueId>,
    ) {
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
            } else {
                self.push_value_from_spill_slot_or_mark(v, v);
                prepared += 1;
            }
        }
    }
}
