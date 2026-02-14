use crate::{
    bitset::BitSet,
    stackalloc::{Action, Actions},
};
use smallvec::SmallVec;
use sonatina_ir::{InstId, ValueId};
use std::collections::{BTreeMap, BinaryHeap, HashMap};

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

struct SearchOperandPrepPlan {
    actions: Actions,
    /// Stack above the function return barrier, after applying `actions`.
    final_stack: Vec<StackItem>,
    metric: OperandPrepMetric,
}

#[derive(Clone, Copy, Debug)]
struct OperandRequirement {
    needed_total: usize,
    is_immediate: bool,
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

        // For small arities, solve operand preparation via a bounded exact search over
        // `DUP*`/`SWAP*`/`PUSH*`. This models "consume in place" correctly and avoids redundant
        // swap chains (common with greedy per-operand preparation), especially around calls.
        if (2..=5).contains(&args.len()) {
            let commutative = self.inst_is_commutative(inst);
            if self.try_prepare_operands_small_via_search(args, consume_last_use, commutative) {
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

    fn try_prepare_operands_small_via_search(
        &mut self,
        args: &mut SmallVec<[ValueId; 8]>,
        consume_last_use: &BitSet<ValueId>,
        commutative: bool,
    ) -> bool {
        debug_assert!((2..=5).contains(&args.len()));

        let order: SmallVec<[ValueId; 4]> = args.iter().copied().collect();
        let mut best: Option<(SearchOperandPrepPlan, bool)> = self
            .search_small_operand_prep(&order, consume_last_use)
            .map(|p| (p, false));

        if commutative && args.len() == 2 && args[0] != args[1] {
            let mut swapped_order = order.clone();
            swapped_order.swap(0, 1);
            if let Some(swapped) = self.search_small_operand_prep(&swapped_order, consume_last_use)
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

    fn search_small_operand_prep(
        &self,
        target: &[ValueId],
        consume_last_use: &BitSet<ValueId>,
    ) -> Option<SearchOperandPrepPlan> {
        let max_actions = match target.len() {
            2 => 12,
            3 => 14,
            4 => 16,
            5 => 18,
            _ => return None,
        };

        let above_len = self.stack.len_above_func_ret();
        let initial: Vec<StackItem> = self.stack.iter().take(above_len).cloned().collect();
        let requirements = self.target_requirements(target, consume_last_use);

        // Only optimize when all non-immediate operands can be produced without touching memory.
        let max_dup = self.ctx.reach.dup_max.min(initial.len());
        for (&v, req) in &requirements {
            if req.is_immediate {
                continue;
            }

            let total_existing = initial
                .iter()
                .filter(|i| matches!(i, StackItem::Value(x) if *x == v))
                .count();
            let reachable_by_swap = initial
                .iter()
                .take(self.ctx.reach.swap_max)
                .any(|i| matches!(i, StackItem::Value(x) if *x == v));
            if !reachable_by_swap {
                return None;
            }

            if total_existing < req.needed_total {
                let reachable_by_dup = (0..max_dup).any(|i| initial[i] == StackItem::Value(v));
                if !reachable_by_dup {
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

        fn is_goal(
            state: &[StackItem],
            target: &[ValueId],
            requirements: &BTreeMap<ValueId, OperandRequirement>,
        ) -> bool {
            if state.len() < target.len() {
                return false;
            }
            if !state
                .iter()
                .take(target.len())
                .zip(target.iter().copied())
                .all(|(item, want)| item == &StackItem::Value(want))
            {
                return false;
            }

            for (&v, req) in requirements {
                let copies = state
                    .iter()
                    .filter(|i| matches!(i, StackItem::Value(x) if *x == v))
                    .count();
                if copies < req.needed_total {
                    return false;
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
            if item.metric != cur_best || item.metric.actions > max_actions {
                continue;
            }

            if is_goal(&item.state, target, &requirements) {
                let mut actions: Vec<Action> = Vec::new();
                let mut cur = item.state.clone();
                while let Some((p, a)) = prev.get(&cur) {
                    actions.push(*a);
                    cur = p.clone();
                }
                actions.reverse();
                let mut out: Actions = Actions::new();
                out.extend(actions.into_iter());
                return Some(SearchOperandPrepPlan {
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

            for (&v, req) in &requirements {
                let current_copies = item
                    .state
                    .iter()
                    .filter(|i| matches!(i, StackItem::Value(x) if *x == v))
                    .count();
                if current_copies >= req.needed_total {
                    continue;
                }

                if req.is_immediate {
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
                    continue;
                }

                let max_dup = self.ctx.reach.dup_max.min(item.state.len());
                if let Some(pos) = (0..max_dup).find(|&i| item.state[i] == StackItem::Value(v)) {
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
        }

        None
    }

    fn target_requirements(
        &self,
        target: &[ValueId],
        consume_last_use: &BitSet<ValueId>,
    ) -> BTreeMap<ValueId, OperandRequirement> {
        let mut top_counts: BTreeMap<ValueId, usize> = BTreeMap::new();
        for &v in target {
            *top_counts.entry(v).or_insert(0) += 1;
        }

        top_counts
            .into_iter()
            .map(|(v, top_count)| {
                let is_immediate = self.ctx.func.dfg.value_is_imm(v);
                let preserve_needed = !is_immediate && !consume_last_use.contains(v);
                (
                    v,
                    OperandRequirement {
                        needed_total: top_count + usize::from(preserve_needed),
                        is_immediate,
                    },
                )
            })
            .collect()
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
                self.mem.spill_obj,
                &mut sim_free_slots,
                &mut sim_slots,
            );
            let mut planner = Planner::new(self.ctx, &mut sim_stack, &mut sim_actions, mem);
            planner.prepare_operands(args, consume_last_use);
        }

        let mem_loads = sim_actions
            .iter()
            .filter(|a| matches!(a, Action::MemLoadAbs(_) | Action::MemLoadObj(_)))
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
