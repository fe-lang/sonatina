use crate::bitset::BitSet;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{Immediate, InstId, ValueId};
use std::{
    collections::VecDeque,
    sync::{Mutex, OnceLock},
};

use super::{
    OperandPrepMode, Planner,
    normalize::SpillAwareCostModel,
    normalize_search::{
        CostModel, NormalizePlan, SearchCfg, Step, cost_for_steps, rebuild_operand_prep_plan,
        solve_optimal_operand_prep_plan,
    },
};

use super::super::{CONSUME_LAST_USE_MAX_SWAPS, sym_stack::StackItem};

const OPERAND_PREP_PLAN_CACHE_CAP: usize = 4096;
const OPERAND_PREP_QUERY_MASK_BITS: usize = u64::BITS as usize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum OperandPrepValueKey {
    Imm(Immediate),
    Val(ValueId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum OperandPrepStackKey {
    Value(OperandPrepValueKey),
    FuncRetAddr,
    CallRetAddr,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct OperandPrepQueryKey {
    func_ptr: usize,
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

struct OperandPrepPlanCache {
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

fn operand_prep_plan_cache() -> &'static Mutex<OperandPrepPlanCache> {
    static CACHE: OnceLock<Mutex<OperandPrepPlanCache>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(OperandPrepPlanCache::new()))
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
        search_cfg: SearchCfg,
    ) -> u64 {
        let start_limit = self.stack.len_above_func_ret();
        let window_len = start_limit.min(search_cfg.max_len);
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

    fn operand_prep_stack_key(&self, item: &StackItem) -> OperandPrepStackKey {
        match *item {
            StackItem::Value(value) => {
                OperandPrepStackKey::Value(self.operand_prep_value_key(value))
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
        let stack_len = self.stack.len_above_func_ret().min(search_cfg.max_len);
        OperandPrepQueryKey {
            func_ptr: self.ctx.func as *const _ as usize,
            dup_max: search_cfg.dup_max as u8,
            swap_max: search_cfg.swap_max as u8,
            max_len: search_cfg.max_len as u8,
            max_expansions: search_cfg.max_expansions as u32,
            stack: self
                .stack
                .iter()
                .take(stack_len)
                .map(|item| self.operand_prep_stack_key(item))
                .collect(),
            args: args
                .iter()
                .map(|&arg| self.operand_prep_value_key(arg))
                .collect(),
            last_use_mask: self.operand_prep_query_mask(args, |arg| consume_last_use.contains(arg)),
            spilled_arg_mask: self.operand_prep_query_mask(args, |arg| {
                !self.ctx.func.dfg.value_is_imm(arg) && self.mem.spill_set().contains(arg)
            }),
            deep_preserve_mask: self.operand_prep_deep_preserve_mask(
                args,
                consume_last_use,
                search_cfg,
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
        let use_query_cache = self.use_operand_prep_query_cache(args.len());
        let cache_key = use_query_cache
            .then(|| self.operand_prep_query_key(args, consume_last_use, search_cfg));

        if let Some(hit) = cache_key.as_ref().and_then(|cache_key| {
            let cache = operand_prep_plan_cache().lock().unwrap();
            cache.get(cache_key).cloned()
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
        );
        if let (Some(cache_key), Some(plan)) = (cache_key, &plan) {
            operand_prep_plan_cache()
                .lock()
                .unwrap()
                .insert(cache_key, plan.steps.clone());
        }
        plan
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
        mode: OperandPrepMode,
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

            if mode == OperandPrepMode::TemplateSim
                && !args.iter().any(|&arg| consume_last_use.contains(arg))
            {
                let mut swapped = args.clone();
                swapped.swap(0, 1);
                if !self.stack_prefix_matches(args) && self.stack_prefix_matches(&swapped) {
                    args.swap(0, 1);
                }
                self.prepare_operands(args.as_slice(), consume_last_use, mode);
                return;
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
                    self.prepare_operands_greedy(args.as_slice(), consume_last_use, mode);
                    return;
                }
            };

            if swapped {
                args.swap(0, 1);
            }
            if !self.apply_operand_prep_plan(&plan, args.as_slice()) {
                self.prepare_operands_greedy(
                    args.as_slice(),
                    consume_last_use,
                    OperandPrepMode::Exact,
                );
            }
            debug_assert!(self.stack_prefix_matches(args.as_slice()));
            return;
        }

        self.prepare_operands(args.as_slice(), consume_last_use, mode);
    }

    pub(in super::super) fn prepare_operands_for_inst(
        &mut self,
        inst: InstId,
        args: &mut SmallVec<[ValueId; 8]>,
        consume_last_use: &BitSet<ValueId>,
        mode: OperandPrepMode,
    ) {
        self.prepare_operands_maybe_commutative(
            args,
            consume_last_use,
            self.inst_is_commutative(inst),
            mode,
        );
    }

    pub(in super::super) fn prepare_operands_for_commutative_pair(
        &mut self,
        args: &mut SmallVec<[ValueId; 8]>,
        consume_last_use: &BitSet<ValueId>,
        mode: OperandPrepMode,
    ) {
        self.prepare_operands_maybe_commutative(args, consume_last_use, true, mode);
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
        mode: OperandPrepMode,
    ) {
        if args.is_empty() {
            return;
        }

        if mode == OperandPrepMode::TemplateSim
            && !args.iter().any(|&arg| consume_last_use.contains(arg))
        {
            self.prepare_operands_greedy(args, consume_last_use, mode);
            debug_assert!(self.stack_prefix_matches(args));
            return;
        }

        if let Some(plan) = self.solve_operand_prep_cached(args, consume_last_use)
            && self.apply_operand_prep_plan(&plan, args)
        {
            debug_assert!(self.stack_prefix_matches(args));
            return;
        }

        self.prepare_operands_greedy(args, consume_last_use, OperandPrepMode::Exact);
        debug_assert!(self.stack_prefix_matches(args));
    }

    fn prepare_operands_greedy(
        &mut self,
        args: &[ValueId],
        consume_last_use: &BitSet<ValueId>,
        mode: OperandPrepMode,
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
            } else if mode == OperandPrepMode::Exact
                && let Some(pos) =
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
                    MemPlan, Planner,
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
    use sonatina_ir::{Immediate, Type, Value, cfg::ControlFlowGraph};
    use sonatina_parser::parse_module;

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
                let spill_obj = SecondaryMap::new();
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
                let mut actions = crate::stackalloc::Actions::new();
                let planner = Planner::new(&ctx, &mut stack, &mut actions, mem);
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
            let spill_obj = SecondaryMap::new();
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
            let mut actions = crate::stackalloc::Actions::new();
            let planner = Planner::new(&ctx, &mut stack, &mut actions, mem);
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
            let spill_obj = SecondaryMap::new();
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

            let old_args = [old_imm, imm2, imm3];
            let current_args = [current_imm, imm2, imm3];
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            let mut planner = Planner::new(&ctx, &mut stack, &mut actions, mem);
            let search_cfg = planner.operand_prep_search_cfg(current_args.len());
            let old_key = planner.operand_prep_query_key(&old_args, &BitSet::default(), search_cfg);
            let current_key =
                planner.operand_prep_query_key(&current_args, &BitSet::default(), search_cfg);

            assert_eq!(old_key, current_key);

            operand_prep_plan_cache()
                .lock()
                .unwrap()
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
            let spill_obj = SecondaryMap::new();
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

            let args: Vec<_> = func.arg_values.iter().copied().collect();
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            let planner = Planner::new(&ctx, &mut stack, &mut actions, mem);
            let search_cfg = planner.operand_prep_search_cfg(args.len());

            assert!(!planner.use_operand_prep_query_cache(1));
            assert!(planner.use_operand_prep_query_cache(2));
            assert!(planner.use_operand_prep_query_cache(3));
            assert!(!planner.use_operand_prep_query_cache(args.len()));
            assert_eq!(planner.operand_prep_query_mask(&args, |_| true), u64::MAX);
            assert_eq!(
                planner.operand_prep_deep_preserve_mask(&args, &BitSet::default(), search_cfg),
                u64::MAX << search_cfg.max_len
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
            let spill_obj = SecondaryMap::new();
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

            let args = [func.arg_values[1], func.arg_values[0]];
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            {
                let mut planner = Planner::new(&ctx, &mut stack, &mut actions, mem);
                planner.prepare_operands_greedy(&args, &BitSet::default(), OperandPrepMode::Exact);
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
    fn greedy_swap_fallback_still_dupes_when_no_prefix_is_prepared() {
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
            let spill_obj = SecondaryMap::new();
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

            let args = [func.arg_values[2]];
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            {
                let mut planner = Planner::new(&ctx, &mut stack, &mut actions, mem);
                planner.prepare_operands_greedy(&args, &BitSet::default(), OperandPrepMode::Exact);
                assert!(planner.stack_prefix_matches(&args));
            }

            assert_eq!(
                actions.as_slice(),
                &[
                    Action::StackSwap(1),
                    Action::StackSwap(2),
                    Action::StackDup(0)
                ],
                "expected prefix-free greedy fallback to keep using SWAP + DUP"
            );
            assert!(
                spill_requests.is_empty(),
                "prefix-free SWAP fallback must not request a spill"
            );

            let mut last_use = BitSet::default();
            last_use.insert(func.arg_values[2]);
            let mut stack = SymStack::entry_stack(func, false);
            let mut actions = crate::stackalloc::Actions::new();
            let mem = MemPlan::new(
                SpillSet::new(&spill_set),
                &mut spill_requests,
                &ctx,
                &spill_obj,
                &ctx.exact_local_addr,
                &mut free_slots,
                &mut slots,
            );
            {
                let mut planner = Planner::new(&ctx, &mut stack, &mut actions, mem);
                planner.prepare_operands_greedy(&args, &last_use, OperandPrepMode::Exact);
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
