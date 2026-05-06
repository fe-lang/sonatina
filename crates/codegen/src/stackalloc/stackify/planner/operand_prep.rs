use crate::bitset::BitSet;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{I256, Immediate, InstId, ValueId};
use std::collections::VecDeque;

use super::{
    Planner,
    normalize::SpillAwareCostModel,
    normalize_search::{
        Cost, CostModel, KeyInfo, NormalizePlan, SearchCfg, Step, cost_for_steps,
        operand_prep_effective_window, rebuild_operand_prep_plan, solve_greedy_operand_prep_plan,
        solve_optimal_operand_prep_plan,
    },
};

use super::super::{CONSUME_LAST_USE_MAX_SWAPS, sym_stack::StackItem};

const OPERAND_PREP_PLAN_CACHE_CAP: usize = 4096;
const OPERAND_PREP_QUERY_MASK_BITS: usize = u64::BITS as usize;

#[derive(Clone)]
struct UnaryOperandPrepCandidate {
    modeled_cost: Cost,
    emitted_cost: Cost,
    priority: u8,
    steps: SmallVec<[Step; 2]>,
}

impl UnaryOperandPrepCandidate {
    fn cmp_key(&self) -> (Cost, Cost, usize, u8) {
        (
            self.modeled_cost,
            self.emitted_cost,
            self.steps.len(),
            self.priority,
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum OperandPrepValueKey {
    Imm(Immediate),
    Val(ValueId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum OperandPrepCanonicalKey {
    Imm(I256),
    Val(ValueId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum OperandPrepStackKey {
    Value(OperandPrepValueKey),
    Ignored,
    FuncRetAddr,
    CallRetAddr,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct OperandPrepQueryKey {
    dup_max: u8,
    swap_max: u8,
    max_len: u8,
    max_expansions: u32,
    stack: SmallVec<[OperandPrepStackKey; 21]>,
    args: SmallVec<[OperandPrepValueKey; 8]>,
    last_use_mask: u64,
    spilled_arg_mask: u64,
    deep_preserve_mask: u64,
}

pub(super) struct OperandPrepPlanCache {
    map: FxHashMap<OperandPrepQueryKey, Vec<Step>>,
    order: VecDeque<OperandPrepQueryKey>,
}

impl OperandPrepPlanCache {
    fn new() -> Self {
        Self {
            map: FxHashMap::default(),
            order: VecDeque::new(),
        }
    }

    fn get(&self, key: &OperandPrepQueryKey) -> Option<&Vec<Step>> {
        self.map.get(key)
    }

    fn insert(&mut self, key: OperandPrepQueryKey, val: Vec<Step>) {
        if let Some(existing) = self.map.get_mut(&key) {
            *existing = val;
            return;
        }

        self.map.insert(key.clone(), val);
        self.order.push_back(key);

        while self.order.len() > OPERAND_PREP_PLAN_CACHE_CAP {
            let Some(old) = self.order.pop_front() else {
                break;
            };
            self.map.remove(&old);
        }
    }
}

impl Default for OperandPrepPlanCache {
    fn default() -> Self {
        Self::new()
    }
}

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
    fn use_operand_prep_query_cache(&self, args_len: usize) -> bool {
        // The exact solver already has its own structural cache. Keep unary uncached because
        // building and hashing the outer query key can cost more than it saves there. Binary
        // queries are common enough in template solving to benefit from cross-pass reuse.
        // Queries beyond the operand-prep solver's exact-state limits cannot use the cache path.
        (2..=21).contains(&args_len) && args_len <= OPERAND_PREP_QUERY_MASK_BITS
    }

    fn operand_prep_query_mask(
        &self,
        args: &[ValueId],
        predicate: impl Fn(ValueId) -> bool,
    ) -> u64 {
        args.iter()
            .take(OPERAND_PREP_QUERY_MASK_BITS)
            .enumerate()
            .fold(0u64, |mask, (idx, &arg)| {
                mask | (u64::from(predicate(arg)) << idx)
            })
    }

    fn operand_prep_deep_preserve_mask(
        &self,
        args: &[ValueId],
        consume_last_use: &BitSet<ValueId>,
        window_len: usize,
    ) -> u64 {
        let start_limit = self.stack.len_above_func_ret();
        if start_limit == window_len {
            return 0;
        }

        let mut mask = 0u64;
        for (idx, &arg) in args.iter().take(OPERAND_PREP_QUERY_MASK_BITS).enumerate() {
            if self.ctx.func.dfg.value_is_imm(arg) || consume_last_use.contains(arg) {
                continue;
            }

            let found_in_tail = (window_len..start_limit)
                .any(|depth| self.stack.item_at(depth) == Some(&StackItem::Value(arg)));
            if found_in_tail {
                mask |= 1u64 << idx;
            }
        }
        mask
    }

    fn operand_prep_value_key(&self, value: ValueId) -> OperandPrepValueKey {
        if let Some(imm) = self.ctx.func.dfg.value_imm(value) {
            OperandPrepValueKey::Imm(imm)
        } else {
            OperandPrepValueKey::Val(value)
        }
    }

    fn operand_prep_canonical_key(&self, value: ValueId) -> OperandPrepCanonicalKey {
        if let Some(imm) = self.ctx.func.dfg.value_imm(value) {
            OperandPrepCanonicalKey::Imm(imm.as_i256())
        } else {
            OperandPrepCanonicalKey::Val(value)
        }
    }

    fn operand_prep_stack_key(
        &self,
        item: &StackItem,
        relevant_values: &[(OperandPrepCanonicalKey, OperandPrepValueKey)],
    ) -> OperandPrepStackKey {
        match *item {
            StackItem::Value(value) => {
                let key = self.operand_prep_canonical_key(value);
                relevant_values
                    .iter()
                    .find_map(|&(relevant, arg_key)| {
                        (relevant == key).then_some(OperandPrepStackKey::Value(arg_key))
                    })
                    .unwrap_or(OperandPrepStackKey::Ignored)
            }
            StackItem::FuncRetAddr => OperandPrepStackKey::FuncRetAddr,
            StackItem::CallRetAddr => OperandPrepStackKey::CallRetAddr,
        }
    }

    fn operand_prep_query_key(
        &self,
        args: &[ValueId],
        consume_last_use: &BitSet<ValueId>,
        search_cfg: SearchCfg,
    ) -> OperandPrepQueryKey {
        let effective_window =
            operand_prep_effective_window(self.ctx, self.stack, args, search_cfg);
        let stack_len = self
            .stack
            .len_above_func_ret()
            .min(effective_window.start_len);
        let mut arg_keys: SmallVec<[OperandPrepValueKey; 8]> = SmallVec::new();
        let mut relevant_values: SmallVec<[(OperandPrepCanonicalKey, OperandPrepValueKey); 8]> =
            SmallVec::new();
        for &arg in args {
            let arg_key = self.operand_prep_value_key(arg);
            let canonical_key = self.operand_prep_canonical_key(arg);
            if !relevant_values
                .iter()
                .any(|&(relevant, _)| relevant == canonical_key)
            {
                relevant_values.push((canonical_key, arg_key));
            }
            arg_keys.push(arg_key);
        }
        OperandPrepQueryKey {
            dup_max: search_cfg.dup_max as u8,
            swap_max: search_cfg.swap_max as u8,
            max_len: effective_window.max_len as u8,
            max_expansions: search_cfg.max_expansions as u32,
            stack: self
                .stack
                .iter()
                .take(stack_len)
                .map(|item| self.operand_prep_stack_key(item, &relevant_values))
                .collect(),
            args: arg_keys,
            last_use_mask: self.operand_prep_query_mask(args, |arg| consume_last_use.contains(arg)),
            spilled_arg_mask: self.operand_prep_query_mask(args, |arg| {
                !self.ctx.func.dfg.value_is_imm(arg) && self.mem.spill_set().contains(arg)
            }),
            deep_preserve_mask: self.operand_prep_deep_preserve_mask(
                args,
                consume_last_use,
                effective_window.start_len,
            ),
        }
    }

    fn solve_operand_prep_cached(
        &mut self,
        args: &[ValueId],
        consume_last_use: &BitSet<ValueId>,
    ) -> Option<NormalizePlan> {
        let search_cfg = self.operand_prep_search_cfg(args.len());
        let cost = SpillAwareCostModel::new(self.mem.spill_set());

        if let [arg] = args
            && let Some(plan) =
                self.solve_unary_operand_prep_fast(*arg, consume_last_use, &cost, search_cfg)
        {
            return Some(plan);
        }

        let use_query_cache = self.use_operand_prep_query_cache(args.len());
        let cache_key = use_query_cache
            .then(|| self.operand_prep_query_key(args, consume_last_use, search_cfg));

        if let Some(hit) = cache_key.as_ref().and_then(|cache_key| {
            self.search_scratch
                .operand_prep_plan_cache
                .get(cache_key)
                .cloned()
        }) && let Some(plan) = rebuild_operand_prep_plan(
            self.ctx,
            self.stack,
            args,
            consume_last_use,
            &cost,
            search_cfg,
            hit,
        ) {
            return Some(plan);
        }

        let plan = solve_optimal_operand_prep_plan(
            self.ctx,
            self.stack,
            args,
            consume_last_use,
            &cost,
            search_cfg,
            self.search_scratch,
        );
        if let (Some(cache_key), Some(plan)) = (cache_key, &plan) {
            self.search_scratch
                .operand_prep_plan_cache
                .insert(cache_key, plan.steps.clone());
        }
        plan
    }

    fn solve_unary_operand_prep_fast(
        &self,
        arg: ValueId,
        consume_last_use: &BitSet<ValueId>,
        cost: &impl CostModel,
        search_cfg: SearchCfg,
    ) -> Option<NormalizePlan> {
        let key_info = self.unary_operand_prep_key_info(arg);
        let arg_imm = self.ctx.func.dfg.value_imm(arg);
        let arg_is_imm = arg_imm.is_some();
        let last_use = consume_last_use.contains(arg);
        let copy_count = self.unary_operand_prep_copy_count(arg, arg_imm);
        let top_matches = self
            .stack
            .top()
            .is_some_and(|item| self.unary_operand_prep_item_matches_arg(item, arg, arg_imm));
        let preserve_satisfied = arg_is_imm || last_use || copy_count >= 2;
        let surplus_last_use_penalty = cost.cost_pop().saturating_add(cost.cost_swap(1));

        let copy_cost = |base: Cost| {
            if last_use && copy_count != 0 {
                base.saturating_add(surplus_last_use_penalty)
            } else {
                base
            }
        };

        let mut candidates: SmallVec<[UnaryOperandPrepCandidate; 6]> = SmallVec::new();

        if top_matches && preserve_satisfied {
            candidates.push(UnaryOperandPrepCandidate {
                modeled_cost: Cost::default(),
                emitted_cost: Cost::default(),
                priority: 0,
                steps: SmallVec::new(),
            });
        }

        if let Some(imm) = arg_imm {
            let emitted_cost = cost.cost_push_imm(imm.as_i256());
            candidates.push(UnaryOperandPrepCandidate {
                modeled_cost: copy_cost(emitted_cost),
                emitted_cost,
                priority: 4,
                steps: smallvec::smallvec![Step::PushImm(0)],
            });
        }

        if let Some(pos) = self.unary_operand_prep_find_arg(arg, arg_imm, 0, search_cfg.dup_max) {
            let emitted_cost = cost.cost_dup(pos as u8);
            candidates.push(UnaryOperandPrepCandidate {
                modeled_cost: copy_cost(emitted_cost),
                emitted_cost,
                priority: 2,
                steps: smallvec::smallvec![Step::Dup(pos as u8)],
            });
        }

        if let Some(pos) = self.unary_operand_prep_find_arg(arg, arg_imm, 0, search_cfg.swap_max)
            && pos != 0
            && (arg_is_imm || last_use || copy_count >= 2)
        {
            let emitted_cost = cost.cost_swap(pos as u8);
            candidates.push(UnaryOperandPrepCandidate {
                modeled_cost: emitted_cost,
                emitted_cost,
                priority: 1,
                steps: smallvec::smallvec![Step::Swap(pos as u8)],
            });
        }

        if !arg_is_imm
            && !last_use
            && copy_count < 2
            && let Some(pos) = self.unary_operand_prep_find_arg(
                arg,
                arg_imm,
                search_cfg.dup_max,
                search_cfg.swap_max,
            )
        {
            let emitted_cost = cost.cost_swap(pos as u8).saturating_add(cost.cost_dup(0));
            candidates.push(UnaryOperandPrepCandidate {
                modeled_cost: emitted_cost,
                emitted_cost,
                priority: 3,
                steps: SmallVec::from_buf([Step::Swap(pos as u8), Step::Dup(0)]),
            });
        }

        if !arg_is_imm {
            let emitted_cost = cost.cost_load(arg);
            candidates.push(UnaryOperandPrepCandidate {
                modeled_cost: copy_cost(emitted_cost),
                emitted_cost,
                priority: 5,
                steps: smallvec::smallvec![Step::LoadVal(0)],
            });
        }

        let candidate = candidates
            .into_iter()
            .min_by(|lhs, rhs| lhs.cmp_key().cmp(&rhs.cmp_key()))?;

        Some(NormalizePlan {
            cost: candidate.modeled_cost,
            steps: candidate.steps.into_vec(),
            key_infos: smallvec::smallvec![key_info],
            goal_keys: smallvec::smallvec![0],
        })
    }

    fn unary_operand_prep_key_info(&self, arg: ValueId) -> KeyInfo {
        if let Some(imm) = self.ctx.func.dfg.value_imm(arg) {
            KeyInfo::Imm {
                canon: imm.as_i256(),
                rep_vid: arg,
                rep_imm: imm,
            }
        } else {
            KeyInfo::Val { vid: arg }
        }
    }

    fn unary_operand_prep_item_matches_arg(
        &self,
        item: &StackItem,
        arg: ValueId,
        arg_imm: Option<Immediate>,
    ) -> bool {
        let StackItem::Value(value) = *item else {
            return false;
        };

        if let Some(arg_imm) = arg_imm {
            return self
                .ctx
                .func
                .dfg
                .value_imm(value)
                .is_some_and(|imm| imm.as_i256() == arg_imm.as_i256());
        }

        value == arg
    }

    fn unary_operand_prep_copy_count(&self, arg: ValueId, arg_imm: Option<Immediate>) -> usize {
        self.stack
            .iter()
            .take(self.stack.len_above_func_ret())
            .filter(|item| self.unary_operand_prep_item_matches_arg(item, arg, arg_imm))
            .count()
    }

    fn unary_operand_prep_find_arg(
        &self,
        arg: ValueId,
        arg_imm: Option<Immediate>,
        start: usize,
        max_depth: usize,
    ) -> Option<usize> {
        let limit = self.stack.len_above_func_ret().min(max_depth);
        if start >= limit {
            return None;
        }

        self.stack
            .iter()
            .skip(start)
            .take(limit - start)
            .position(|item| self.unary_operand_prep_item_matches_arg(item, arg, arg_imm))
            .map(|off| start + off)
    }

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

            let original_plan = self.solve_operand_prep_cached(args.as_slice(), consume_last_use);

            let mut swapped_args = args.clone();
            swapped_args.swap(0, 1);
            let swapped_plan =
                self.solve_operand_prep_cached(swapped_args.as_slice(), consume_last_use);
            let cost = SpillAwareCostModel::new(self.mem.spill_set());

            let (plan, swapped) = match (original_plan, swapped_plan) {
                (Some(plan), None) => (plan, false),
                (None, Some(plan)) => (plan, true),
                (Some(original), Some(swapped)) => {
                    let original_cost = commutative_plan_cmp_key(&original, &cost);
                    let swapped_cost = commutative_plan_cmp_key(&swapped, &cost);
                    if swapped_cost < original_cost {
                        (swapped, true)
                    } else {
                        (original, false)
                    }
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
            debug_assert!(self.stack_prefix_matches(args.as_slice()));
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

        if let Some(plan) = self.solve_operand_prep_cached(args, consume_last_use)
            && self.apply_operand_prep_plan(&plan, args)
        {
            debug_assert!(self.stack_prefix_matches(args));
            return;
        }

        self.prepare_operands_greedy(args, consume_last_use);
        debug_assert!(self.stack_prefix_matches(args));
    }

    fn prepare_operands_greedy(&mut self, args: &[ValueId], consume_last_use: &BitSet<ValueId>) {
        let search_cfg = self.operand_prep_search_cfg(args.len());
        let cost = SpillAwareCostModel::new(self.mem.spill_set());
        if let Some(plan) = solve_greedy_operand_prep_plan(
            self.ctx,
            self.stack,
            args,
            consume_last_use,
            true,
            &cost,
            search_cfg,
        ) && self.apply_operand_prep_plan(&plan, args)
        {
            return;
        }

        self.prepare_operands_greedy_fallback(args, consume_last_use);
    }

    fn prepare_operands_greedy_fallback(
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

            // If this is a last-use, prefer consuming an existing stack copy instead of
            // duplicating it, but only when the swap chain is small.
            if consume_last_use.contains(v)
                && !consumed_from_stack.contains(v)
                && let Some(pos) =
                    self.stack
                        .find_reachable_value_from(v, prepared, self.ctx.reach.swap_max)
                && pos <= CONSUME_LAST_USE_MAX_SWAPS
            {
                if prepared == 0 {
                    self.stack.swap(pos, self.actions);
                } else {
                    self.stack.stable_rotate_to_top(pos, self.actions);
                }
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
                if prepared == 0 {
                    self.stack.stable_rotate_to_top(pos, self.actions);
                    self.stack.dup(0, self.actions);
                } else {
                    // `find_reachable_value_from(..., swap_max)` can only expose the single
                    // SWAP-only slot beyond DUP reach. Once a prepared prefix already exists,
                    // restoring that prefix after rotating the source to the top would require
                    // one more SWAP level than the source itself provides, so a stack-only
                    // fallback would corrupt operand order.
                    self.push_value_from_spill_slot_or_mark(v, v);
                }
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
    use crate::{
        cfg_scc::CfgSccAnalysis,
        domtree::DomTree,
        liveness::Liveness,
        stackalloc::{
            Action,
            stackify::{
                builder::StackifyReachability,
                planner::{
                    MemPlan, NormalizeSearchScratch, Planner,
                    normalize_search::{Cost, EstimatedCostModel, KeyInfo, Step},
                    test_utils::build_stackify_test_context,
                },
                slots::{FreeSlotPools, SpillSlotPools},
                spill::SpillSet,
                sym_stack::SymStack,
            },
        },
    };
    use cranelift_entity::SecondaryMap;
    use sonatina_ir::{I256, Immediate, Type, Value, cfg::ControlFlowGraph};
    use sonatina_parser::parse_module;

    #[test]
    fn commutative_plan_comparison_uses_emitted_step_cost() {
        let cost = EstimatedCostModel::default();
        let cheaper_emitted = NormalizePlan {
            cost: Cost { gas: 99, bytes: 99 },
            steps: vec![Step::Dup(0)],
            key_infos: SmallVec::new(),
            goal_keys: SmallVec::new(),
        };
        let pricier_emitted = NormalizePlan {
            cost: Cost::default(),
            steps: vec![Step::Swap(1), Step::Swap(1)],
            key_infos: SmallVec::new(),
            goal_keys: SmallVec::new(),
        };

        assert!(
            commutative_plan_cmp_key(&cheaper_emitted, &cost)
                < commutative_plan_cmp_key(&pricier_emitted, &cost)
        );
    }

    #[test]
    fn operand_prep_query_key_tracks_immediate_payloads() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let imm = func.dfg.make_imm_value(Immediate::I8(1));

            let key_before = {
                let mut cfg = ControlFlowGraph::new();
                cfg.compute(func);
                let entry = cfg.entry().expect("missing entry block");

                let mut liveness = Liveness::new();
                liveness.compute(func, &cfg);

                let mut dom = DomTree::new();
                dom.compute(&cfg);

                let mut scc = CfgSccAnalysis::new();
                scc.compute(&cfg);

                let reach = StackifyReachability::new(16);
                let ctx =
                    build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

                let spill_set = BitSet::default();
                let mut spill_requests = BitSet::default();
                let mut object_spill_requests = BitSet::default();
                let forced_object_spills = BitSet::default();
                let spill_obj = SecondaryMap::new();
                let mut free_slots = FreeSlotPools::default();
                let mut slots = SpillSlotPools::default();
                let mem = MemPlan::new(
                    SpillSet::new(&spill_set),
                    &mut spill_requests,
                    &ctx,
                    &spill_obj,
                    &ctx.exact_local_addr,
                    &mut object_spill_requests,
                    &forced_object_spills,
                    &mut free_slots,
                    &mut slots,
                );

                let mut stack = SymStack::entry_stack(func, false);
                let mut actions = crate::stackalloc::Actions::new();
                let mut search_scratch = NormalizeSearchScratch::default();
                let planner =
                    Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
                let search_cfg = planner.operand_prep_search_cfg(1);
                planner.operand_prep_query_key(&[imm], &BitSet::default(), search_cfg)
            };

            func.dfg.immediates.remove(&Immediate::I8(1));
            func.dfg.values[imm] = Value::Immediate {
                imm: Immediate::I8(2),
                ty: Type::I8,
            };
            func.dfg.immediates.insert(Immediate::I8(2), imm);

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let spill_set = BitSet::default();
            let mut spill_requests = BitSet::default();
            let mut object_spill_requests = BitSet::default();
            let forced_object_spills = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut object_spill_requests,
                &forced_object_spills,
                &mut free_slots,
                &mut slots,
            );

            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            let mut search_scratch = NormalizeSearchScratch::default();
            let planner = Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
            let search_cfg = planner.operand_prep_search_cfg(1);
            let key_after = planner.operand_prep_query_key(&[imm], &BitSet::default(), search_cfg);

            assert_ne!(key_before, key_after);
        });
    }

    #[test]
    fn operand_prep_query_cache_rebuilds_current_immediate_key_infos() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let old_imm = func.dfg.make_imm_value(Immediate::I8(1));
            let current_imm = func.dfg.make_value(Value::Immediate {
                imm: Immediate::I8(1),
                ty: Type::I8,
            });
            let imm2 = func.dfg.make_imm_value(Immediate::I8(2));
            let imm3 = func.dfg.make_imm_value(Immediate::I8(3));

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let spill_set = BitSet::default();
            let mut spill_requests = BitSet::default();
            let mut object_spill_requests = BitSet::default();
            let forced_object_spills = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut object_spill_requests,
                &forced_object_spills,
                &mut free_slots,
                &mut slots,
            );

            let old_args = [old_imm, imm2, imm3];
            let current_args = [current_imm, imm2, imm3];
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            let mut search_scratch = NormalizeSearchScratch::default();
            let mut planner =
                Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
            let search_cfg = planner.operand_prep_search_cfg(current_args.len());
            let old_key = planner.operand_prep_query_key(&old_args, &BitSet::default(), search_cfg);
            let current_key =
                planner.operand_prep_query_key(&current_args, &BitSet::default(), search_cfg);

            assert_eq!(old_key, current_key);

            planner
                .search_scratch
                .operand_prep_plan_cache
                .insert(old_key, vec![Step::PushImm(0)]);

            let plan = planner
                .solve_operand_prep_cached(&current_args, &BitSet::default())
                .expect("cache hit should rebuild a plan");

            let [
                KeyInfo::Imm {
                    rep_vid, rep_imm, ..
                },
                ..,
            ] = plan.key_infos.as_slice()
            else {
                panic!("expected first cached key info to be immediate")
            };

            assert_eq!(*rep_vid, current_imm);
            assert_eq!(*rep_imm, Immediate::I8(1));
        });
    }

    #[test]
    fn operand_prep_query_masks_cap_at_u64_width() {
        let params = (0..65)
            .map(|idx| format!("v{idx}.i256"))
            .collect::<Vec<_>>()
            .join(", ");
        let src = format!(
            r#"
target = "evm-ethereum-osaka"

func public %f({params}) {{
block0:
    return;
}}
"#
        );

        let parsed = parse_module(&src).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let spill_set = BitSet::default();
            let mut spill_requests = BitSet::default();
            let mut object_spill_requests = BitSet::default();
            let forced_object_spills = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut object_spill_requests,
                &forced_object_spills,
                &mut free_slots,
                &mut slots,
            );

            let args: Vec<_> = func.arg_values.iter().copied().collect();
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            let mut search_scratch = NormalizeSearchScratch::default();
            let planner = Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
            let search_cfg = planner.operand_prep_search_cfg(args.len());

            assert!(!planner.use_operand_prep_query_cache(1));
            assert!(planner.use_operand_prep_query_cache(2));
            assert!(planner.use_operand_prep_query_cache(3));
            assert!(!planner.use_operand_prep_query_cache(args.len()));
            assert_eq!(planner.operand_prep_query_mask(&args, |_| true), u64::MAX);
            assert_eq!(
                planner.operand_prep_deep_preserve_mask(
                    &args,
                    &BitSet::default(),
                    search_cfg.max_len,
                ),
                u64::MAX << search_cfg.max_len
            );
        });
    }

    #[test]
    fn operand_prep_query_key_ignores_irrelevant_slots_below_effective_window() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let imm_args = [
                func.dfg.make_imm_value(Immediate::I8(1)),
                func.dfg.make_imm_value(Immediate::I8(2)),
            ];
            let top0 = func.dfg.make_undef_value(Type::I256);
            let top1 = func.dfg.make_undef_value(Type::I256);
            let ignored_a = func.dfg.make_undef_value(Type::I256);
            let ignored_b = func.dfg.make_undef_value(Type::I256);

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);
            let spill_set = BitSet::default();
            let spill_obj = SecondaryMap::new();

            let query_key = |values: &[ValueId]| {
                let mut spill_requests = BitSet::default();
                let mut free_slots = FreeSlotPools::default();
                let mut slots = SpillSlotPools::default();
                let mem = MemPlan::new(
                    SpillSet::new(&spill_set),
                    &mut spill_requests,
                    &ctx,
                    &spill_obj,
                    &ctx.exact_local_addr,
                    &mut free_slots,
                    &mut slots,
                );
                let mut stack = SymStack::entry_stack(func, false);
                for &value in values.iter().rev() {
                    stack.push_value(value);
                }
                let mut actions = crate::stackalloc::Actions::new();
                let mut search_scratch = NormalizeSearchScratch::default();
                let planner =
                    Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
                let search_cfg = planner.operand_prep_search_cfg(imm_args.len());
                planner.operand_prep_query_key(&imm_args, &BitSet::default(), search_cfg)
            };

            let lhs = query_key(&[top0, top1, ignored_a]);
            let rhs = query_key(&[top0, top1, ignored_b]);
            assert_eq!(lhs, rhs);
        });
    }

    #[test]
    fn operand_prep_query_key_ignores_irrelevant_slots_inside_effective_window() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let source = func.dfg.make_undef_value(Type::I256);
            let ignored_a = func.dfg.make_undef_value(Type::I256);
            let ignored_b = func.dfg.make_undef_value(Type::I256);
            let args = [source];

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);
            let spill_set = BitSet::default();
            let spill_obj = SecondaryMap::new();

            let query_key = |top: ValueId| {
                let mut spill_requests = BitSet::default();
                let mut free_slots = FreeSlotPools::default();
                let mut slots = SpillSlotPools::default();
                let mem = MemPlan::new(
                    SpillSet::new(&spill_set),
                    &mut spill_requests,
                    &ctx,
                    &spill_obj,
                    &ctx.exact_local_addr,
                    &mut free_slots,
                    &mut slots,
                );
                let mut stack = SymStack::entry_stack(func, false);
                stack.push_value(source);
                stack.push_value(top);
                let mut actions = crate::stackalloc::Actions::new();
                let mut search_scratch = NormalizeSearchScratch::default();
                let planner =
                    Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
                let search_cfg = planner.operand_prep_search_cfg(args.len());
                planner.operand_prep_query_key(&args, &BitSet::default(), search_cfg)
            };

            let lhs = query_key(ignored_a);
            let rhs = query_key(ignored_b);

            assert_eq!(lhs, rhs);
            assert_eq!(lhs.stack[0], OperandPrepStackKey::Ignored);
            assert_eq!(
                lhs.stack[1],
                OperandPrepStackKey::Value(OperandPrepValueKey::Val(source))
            );
        });
    }

    #[test]
    fn operand_prep_query_key_keeps_canonical_immediate_sources_relevant() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let arg = func.dfg.make_imm_value(Immediate::I8(1));
            let stack_source = func.dfg.make_imm_value(Immediate::I256(I256::from(1)));
            let ignored = func.dfg.make_undef_value(Type::I256);
            let args = [arg];

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);
            let spill_set = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut spill_requests = BitSet::default();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut free_slots,
                &mut slots,
            );
            let mut stack = SymStack::entry_stack(func, false);
            stack.push_value(stack_source);
            stack.push_value(ignored);
            let mut actions = crate::stackalloc::Actions::new();
            let mut search_scratch = NormalizeSearchScratch::default();
            let planner = Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
            let search_cfg = planner.operand_prep_search_cfg(args.len());
            let key = planner.operand_prep_query_key(&args, &BitSet::default(), search_cfg);

            assert_eq!(key.stack[0], OperandPrepStackKey::Ignored);
            assert_eq!(
                key.stack[1],
                OperandPrepStackKey::Value(OperandPrepValueKey::Imm(Immediate::I8(1)))
            );
        });
    }

    #[test]
    fn operand_prep_query_key_tracks_relevant_source_inside_effective_window() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let source = func.dfg.make_undef_value(Type::I256);
            let imm = func.dfg.make_imm_value(Immediate::I8(3));
            let top = func.dfg.make_undef_value(Type::I256);
            let unrelated = func.dfg.make_undef_value(Type::I256);
            let ignored = func.dfg.make_undef_value(Type::I256);
            let args = [source, imm];

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);
            let spill_set = BitSet::default();
            let spill_obj = SecondaryMap::new();

            let query_key = |values: &[ValueId]| {
                let mut spill_requests = BitSet::default();
                let mut free_slots = FreeSlotPools::default();
                let mut slots = SpillSlotPools::default();
                let mem = MemPlan::new(
                    SpillSet::new(&spill_set),
                    &mut spill_requests,
                    &ctx,
                    &spill_obj,
                    &ctx.exact_local_addr,
                    &mut free_slots,
                    &mut slots,
                );
                let mut stack = SymStack::entry_stack(func, false);
                for &value in values.iter().rev() {
                    stack.push_value(value);
                }
                let mut actions = crate::stackalloc::Actions::new();
                let mut search_scratch = NormalizeSearchScratch::default();
                let planner =
                    Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
                let search_cfg = planner.operand_prep_search_cfg(args.len());
                planner.operand_prep_query_key(&args, &BitSet::default(), search_cfg)
            };

            let no_source = query_key(&[top, unrelated, ignored]);
            let with_source = query_key(&[top, source, ignored]);
            assert_ne!(no_source, with_source);
        });
    }

    #[test]
    fn operand_prep_query_cache_replays_across_ignored_live_values() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f() {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let imm = func.dfg.make_imm_value(Immediate::I8(7));
            let source = func.dfg.make_undef_value(Type::I256);
            let ignored_a = func.dfg.make_undef_value(Type::I256);
            let ignored_b = func.dfg.make_undef_value(Type::I256);
            let args = [imm, source];
            let mut last_use = BitSet::default();
            last_use.insert(source);

            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(16);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);
            let spill_set = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut search_scratch = NormalizeSearchScratch::default();
            let mut solve_with = |ignored: ValueId| {
                let mut spill_requests = BitSet::default();
                let mut free_slots = FreeSlotPools::default();
                let mut slots = SpillSlotPools::default();
                let mem = MemPlan::new(
                    SpillSet::new(&spill_set),
                    &mut spill_requests,
                    &ctx,
                    &spill_obj,
                    &ctx.exact_local_addr,
                    &mut free_slots,
                    &mut slots,
                );
                let mut stack = SymStack::entry_stack(func, false);
                stack.push_value(ignored);
                stack.push_value(source);
                let mut actions = crate::stackalloc::Actions::new();
                let mut planner =
                    Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
                let plan = planner
                    .solve_operand_prep_cached(&args, &last_use)
                    .expect("expected operand-prep plan");
                let steps = plan.steps.clone();

                assert!(planner.apply_operand_prep_plan(&plan, &args));
                (
                    steps,
                    planner.search_scratch.operand_prep_plan_cache.map.len(),
                )
            };

            let (lhs_steps, lhs_cache_len) = solve_with(ignored_a);
            let (rhs_steps, rhs_cache_len) = solve_with(ignored_b);

            assert_eq!(lhs_cache_len, 1);
            assert_eq!(rhs_cache_len, 1);
            assert_eq!(lhs_steps, rhs_steps);
        });
    }

    #[test]
    fn unary_operand_prep_fast_path_handles_preserve_and_consume_cases() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i256, v2.i256) {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(2);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);
            let spill_set = BitSet::default();
            let spill_obj = SecondaryMap::new();

            let solve_steps = |mut stack: SymStack, arg: ValueId, last_use: &BitSet<ValueId>| {
                let mut spill_requests = BitSet::default();
                let mut free_slots = FreeSlotPools::default();
                let mut slots = SpillSlotPools::default();
                let mem = MemPlan::new(
                    SpillSet::new(&spill_set),
                    &mut spill_requests,
                    &ctx,
                    &spill_obj,
                    &ctx.exact_local_addr,
                    &mut free_slots,
                    &mut slots,
                );

                let mut actions = crate::stackalloc::Actions::new();
                let mut search_scratch = NormalizeSearchScratch::default();
                let mut planner =
                    Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
                let plan = planner
                    .solve_operand_prep_cached(&[arg], last_use)
                    .expect("unary fast path should produce a plan");
                let steps = plan.steps.clone();

                assert!(planner.apply_operand_prep_plan(&plan, &[arg]));
                steps
            };

            let arg = func.arg_values[0];
            let stack = SymStack::entry_stack(func, false);
            assert_eq!(
                solve_steps(stack, arg, &BitSet::default()),
                vec![Step::Dup(0)]
            );

            let mut stack = SymStack::entry_stack(func, false);
            let mut setup_actions = crate::stackalloc::Actions::new();
            stack.dup(0, &mut setup_actions);
            assert!(
                solve_steps(stack, arg, &BitSet::default()).is_empty(),
                "already-prepared non-last-use operand with a preserved copy should be a no-op"
            );

            let arg = func.arg_values[2];
            let mut last_use = BitSet::default();
            last_use.insert(arg);
            let stack = SymStack::entry_stack(func, false);
            assert_eq!(solve_steps(stack, arg, &last_use), vec![Step::Swap(2)]);

            let stack = SymStack::entry_stack(func, false);
            assert_eq!(
                solve_steps(stack, arg, &BitSet::default()),
                vec![Step::Swap(2), Step::Dup(0)]
            );
        });
    }

    #[test]
    fn greedy_swap_fallback_spills_instead_of_rotating_prepared_prefix() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i256, v2.i256) {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(2);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let spill_set = BitSet::default();
            let mut spill_requests = BitSet::default();
            let mut object_spill_requests = BitSet::default();
            let forced_object_spills = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut object_spill_requests,
                &forced_object_spills,
                &mut free_slots,
                &mut slots,
            );

            let args = [func.arg_values[1], func.arg_values[0]];
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            {
                let mut search_scratch = NormalizeSearchScratch::default();
                let mut planner =
                    Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
                planner.prepare_operands_greedy(&args, &BitSet::default());
                assert!(planner.stack_prefix_matches(&args));
            }

            assert!(
                !actions
                    .iter()
                    .any(|action| matches!(action, Action::StackSwap(_))),
                "prepared-prefix fallback must not rotate the existing prefix: {actions:?}"
            );
            assert!(
                actions
                    .iter()
                    .any(|action| matches!(action, Action::MemLoadObj(_))),
                "expected greedy fallback to materialize the second operand from spill/load state: {actions:?}"
            );
            assert!(
                spill_requests.contains(func.arg_values[1]),
                "expected deep prepared operand to request a spill"
            );
        });
    }

    #[test]
    fn greedy_prefix_free_swap_path_uses_single_swap() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i256, v2.i256) {
block0:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.modify(func_ref, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let entry = cfg.entry().expect("missing entry block");

            let mut liveness = Liveness::new();
            liveness.compute(func, &cfg);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut scc = CfgSccAnalysis::new();
            scc.compute(&cfg);

            let reach = StackifyReachability::new(2);
            let ctx = build_stackify_test_context(func, &cfg, &dom, &liveness, entry, scc, reach);

            let spill_set = BitSet::default();
            let mut spill_requests = BitSet::default();
            let mut object_spill_requests = BitSet::default();
            let forced_object_spills = BitSet::default();
            let spill_obj = SecondaryMap::new();
            let mut free_slots = FreeSlotPools::default();
            let mut slots = SpillSlotPools::default();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut object_spill_requests,
                &forced_object_spills,
                &mut free_slots,
                &mut slots,
            );

            let args = [func.arg_values[2]];
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            {
                let mut search_scratch = NormalizeSearchScratch::default();
                let mut planner =
                    Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
                planner.prepare_operands_greedy(&args, &BitSet::default());
                assert!(planner.stack_prefix_matches(&args));
            }

            assert_eq!(
                actions.as_slice(),
                &[Action::StackSwap(2), Action::StackDup(0)],
                "prefix-free copy should use one SWAP before DUP"
            );
            assert!(
                spill_requests.is_empty(),
                "prefix-free SWAP fallback must not request a spill"
            );

            let mut last_use = BitSet::default();
            last_use.insert(func.arg_values[2]);
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            let mut object_spill_requests = BitSet::default();
            let forced_object_spills = BitSet::default();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut object_spill_requests,
                &forced_object_spills,
                &mut free_slots,
                &mut slots,
            );
            {
                let mut search_scratch = NormalizeSearchScratch::default();
                let mut planner =
                    Planner::new(&ctx, &mut stack, &mut actions, mem, &mut search_scratch);
                planner.prepare_operands_greedy(&args, &last_use);
                assert!(planner.stack_prefix_matches(&args));
            }

            assert_eq!(
                actions.as_slice(),
                &[Action::StackSwap(2)],
                "prefix-free last-use consume should use one SWAP"
            );
        });
    }
}
