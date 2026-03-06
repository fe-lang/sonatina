use sonatina_ir::ValueId;

use super::{
    Planner,
    normalize_search::{
        Cost, CostModel, EstimatedCostModel, SearchCfg, solve_optimal_normalize_plan,
        solve_optimal_repair_normalize_plan,
    },
};

use super::super::sym_stack::{StackItem, SymStack};
use std::sync::{
    OnceLock,
    atomic::{AtomicUsize, Ordering},
};

impl<'a, 'ctx: 'a> Planner<'a, 'ctx> {
    pub(super) fn rename_immediate_slots_to_match(&mut self, desired: &[ValueId]) -> bool {
        for (depth, &want) in desired.iter().enumerate() {
            if self.ctx.func.dfg.value_is_imm(want) {
                let want_imm = self
                    .ctx
                    .func
                    .dfg
                    .value_imm(want)
                    .expect("imm value missing payload")
                    .as_i256();
                let Some(StackItem::Value(cur)) = self.stack.item_at(depth) else {
                    return false;
                };
                let cur_imm = self
                    .ctx
                    .func
                    .dfg
                    .value_imm(*cur)
                    .expect("expected immediate value on stack")
                    .as_i256();
                if cur_imm != want_imm {
                    return false;
                }
                self.stack.rename_value_at_depth(depth, want);
            }
        }

        true
    }

    pub(super) fn normalize_to_exact(&mut self, desired: &[ValueId]) {
        // Contract: rewrite the current symbolic stack (above the function return barrier, if any)
        // so that it matches `desired` exactly (top-first).
        if matches_exact(self.stack, desired) {
            return;
        }
        if self.try_normalize_to_exact(desired) {
            return;
        }
        self.flush_rebuild(desired);
    }

    pub(super) fn apply_normalize_plan(
        &mut self,
        plan: &super::normalize_search::NormalizePlan,
        desired: &[ValueId],
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

        if !self.rename_immediate_slots_to_match(desired) || !matches_exact(self.stack, desired) {
            *self.stack = stack_before;
            self.actions.truncate(actions_before);
            self.mem.restore(mem_before);
            return false;
        }

        true
    }

    fn try_normalize_to_exact(&mut self, desired: &[ValueId]) -> bool {
        let limit = self.stack.len_above_func_ret();
        let debug = normalize_debug_enabled();
        if debug {
            eprintln!(
                "normalize_to_exact: start_len={} desired_len={} spilled={}",
                limit,
                desired.len(),
                self.mem.spill_set().bitset().len()
            );
        }

        let cost = SpillAwareCostModel::new(self.mem.spill_set());
        let search_cfg = SearchCfg {
            dup_max: self.ctx.reach.dup_max,
            swap_max: self.ctx.reach.swap_max,
            // Bound intermediate length to the stack reach window (+ optional slack).
            max_len: self.ctx.reach.swap_max,
            max_expansions: 50_000,
        };

        let mut plan =
            if limit <= self.ctx.reach.swap_max && desired.len() <= self.ctx.reach.swap_max {
                solve_optimal_normalize_plan(self.ctx, self.stack, desired, &cost, search_cfg)
            } else {
                None
            };

        if plan.is_none() {
            let base_len = common_suffix_len_semantic(self.ctx.func, self.stack, desired);
            let start_repair = limit.saturating_sub(base_len);
            let goal_repair = desired.len().saturating_sub(base_len);

            if debug {
                eprintln!(
                    "normalize_to_exact: repair_window base_len={base_len} start_repair={start_repair} goal_repair={goal_repair}"
                );
            }

            if start_repair <= self.ctx.reach.swap_max && goal_repair <= self.ctx.reach.swap_max {
                plan = solve_optimal_repair_normalize_plan(
                    self.ctx, self.stack, desired, base_len, &cost, search_cfg,
                );
            }
        }

        let Some(plan) = plan else {
            if debug {
                eprintln!("normalize_to_exact: solver returned None (falling back)");
                dump_failed_normalization(self.stack, desired);
            }
            return false;
        };

        if debug {
            let mut pops = 0usize;
            let mut dups = 0usize;
            let mut swaps = 0usize;
            let mut pushes = 0usize;
            let mut loads = 0usize;
            for &s in &plan.steps {
                match s {
                    super::normalize_search::Step::Pop => pops += 1,
                    super::normalize_search::Step::Dup(_) => dups += 1,
                    super::normalize_search::Step::Swap(_) => swaps += 1,
                    super::normalize_search::Step::PushImm(_) => pushes += 1,
                    super::normalize_search::Step::LoadVal(_) => loads += 1,
                }
            }
            eprintln!(
                "normalize_to_exact: plan steps={} pop={} dup={} swap={} push={} load={}",
                plan.steps.len(),
                pops,
                dups,
                swaps,
                pushes,
                loads
            );
        }

        let ok = self.apply_normalize_plan(&plan, desired);
        if debug && !ok {
            eprintln!("normalize_to_exact: plan replay failed");
        }
        ok
    }

    fn flush_rebuild(&mut self, desired: &[ValueId]) {
        let base_len = common_suffix_len_semantic(self.ctx.func, self.stack, desired);

        // Pop everything above the common base suffix.
        while self.stack.len_above_func_ret() > base_len {
            self.stack.pop(self.actions);
        }

        // Rebuild the remaining prefix bottom-to-top (push reverse so final is top-first).
        for &v in desired[..desired.len().saturating_sub(base_len)]
            .iter()
            .rev()
        {
            if self.ctx.func.dfg.value_is_imm(v) {
                let imm = self
                    .ctx
                    .func
                    .dfg
                    .value_imm(v)
                    .expect("imm value missing payload");
                self.stack.push_imm(v, imm, self.actions);
            } else {
                self.push_value_from_spill_slot_or_mark(v, v);
            }
        }

        assert!(
            self.rename_immediate_slots_to_match(desired),
            "flush_rebuild failed to restore immediate value ids"
        );
        debug_assert!(matches_exact(self.stack, desired));
    }

    /// Delete everything between the current top value and the function return barrier, preserving
    /// the top value.
    ///
    /// This is a specialized cleanup used at internal returns. When there is more than one value
    /// between `[ret_val]` and `FuncRetAddr`, we swap the return value down as close as possible
    /// (up to `SWAP16`) and then pop a run of intermediates, repeating until the barrier is
    /// directly below the top.
    pub(super) fn delete_between_top_and_func_ret(&mut self) {
        loop {
            let Some(barrier_pos) = self.stack.func_ret_index() else {
                break;
            };
            if barrier_pos <= 1 {
                break;
            }
            let between = barrier_pos.saturating_sub(1);
            let swap_depth = between.min(self.ctx.reach.dup_max);
            debug_assert!(swap_depth >= 1);
            self.stack.swap(swap_depth, self.actions);
            self.stack.pop_n(swap_depth, self.actions);
        }
    }
}

pub(super) struct SpillAwareCostModel<'a> {
    base: EstimatedCostModel,
    spilled: super::super::spill::SpillSet<'a>,
    new_spill_penalty: Cost,
}

impl<'a> SpillAwareCostModel<'a> {
    pub(super) fn new(spilled: super::super::spill::SpillSet<'a>) -> Self {
        Self {
            base: EstimatedCostModel::default(),
            spilled,
            // Approximate "new spill" overhead (store at def + reloads elsewhere).
            new_spill_penalty: Cost { gas: 15, bytes: 7 },
        }
    }
}

impl CostModel for SpillAwareCostModel<'_> {
    fn cost_pop(&self) -> Cost {
        self.base.cost_pop()
    }

    fn cost_dup(&self, pos: u8) -> Cost {
        self.base.cost_dup(pos)
    }

    fn cost_swap(&self, depth: u8) -> Cost {
        self.base.cost_swap(depth)
    }

    fn cost_push_imm(&self, imm: sonatina_ir::I256) -> Cost {
        self.base.cost_push_imm(imm)
    }

    fn cost_load(&self, v: ValueId) -> Cost {
        let base = self.base.cost_load(v);
        if self.spilled.contains(v) {
            base
        } else {
            base.saturating_add(self.new_spill_penalty)
        }
    }
}

fn matches_exact(stack: &SymStack, desired: &[ValueId]) -> bool {
    let limit = stack.len_above_func_ret();
    limit == desired.len()
        && stack
            .iter()
            .take(limit)
            .zip(desired.iter().copied())
            .all(|(item, v)| item == &StackItem::Value(v))
}

fn normalize_debug_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        matches!(
            std::env::var("SONATINA_STACKIFY_NORMALIZE_DEBUG")
                .as_deref()
                .ok(),
            Some("1") | Some("true") | Some("yes")
        )
    })
}

fn dump_failed_normalization(stack: &SymStack, desired: &[ValueId]) {
    static DUMPS: AtomicUsize = AtomicUsize::new(0);
    if DUMPS.fetch_add(1, Ordering::Relaxed) >= 3 {
        return;
    }

    let start: Vec<StackItem> = stack
        .iter()
        .take(stack.len_above_func_ret())
        .cloned()
        .collect();
    eprintln!("normalize_to_exact: start={start:?}");
    eprintln!("normalize_to_exact: desired={desired:?}");
}

fn common_suffix_len_semantic(
    func: &sonatina_ir::Function,
    stack: &SymStack,
    desired: &[ValueId],
) -> usize {
    let limit = stack.len_above_func_ret();
    let max = limit.min(desired.len());
    let mut k = 0usize;

    for off in 0..max {
        let depth = limit - 1 - off;
        let want = desired[desired.len() - 1 - off];

        let Some(item) = stack.item_at(depth) else {
            break;
        };
        let StackItem::Value(cur) = item else {
            break;
        };
        let cur = *cur;

        if func.dfg.value_is_imm(want) {
            if !func.dfg.value_is_imm(cur) {
                break;
            }
            let Some(want_imm) = func.dfg.value_imm(want) else {
                break;
            };
            let Some(cur_imm) = func.dfg.value_imm(cur) else {
                break;
            };
            if want_imm.as_i256() != cur_imm.as_i256() {
                break;
            }
        } else if cur != want {
            break;
        }

        k += 1;
    }

    k
}
