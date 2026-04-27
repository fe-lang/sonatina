use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, Immediate, InstId, ValueId};
use std::collections::BTreeMap;

use crate::{bitset::BitSet, isa::evm::immediate_u32, stackalloc::Actions};

use super::{
    alloc::StackifyAlloc,
    block_sim::{BlockSimMode, BlockSimState, BrTableEdgeKind, PlannerActionSink, run_block_sim},
    builder::{StackifyContext, StackifyReachability},
    planner::{self, NormalizeSearchScratch, OperandPrepMode, OperandPrepMode::Exact, Planner},
    slots::{FreeSlotPools, FreeSlots, SlotPool, SpillSlotPools},
    spill::SpillSet,
    sym_stack::{StackItem, SymStack},
    templates::BlockTemplate,
    trace::StackifyObserver,
};

use sonatina_ir::{
    InstDowncast,
    inst::{cast, data, evm},
};

pub(super) struct IterationPlanner<'a, 'ctx, O: StackifyObserver> {
    ctx: &'a StackifyContext<'ctx>,
    spill: SpillSet<'a>,
    slots: &'a mut SpillSlotPools,
    templates: &'a SecondaryMap<BlockId, BlockTemplate>,
    terminal_chain_blocks: &'a SecondaryMap<BlockId, bool>,
    alloc: &'a mut StackifyAlloc,
    spill_requests: &'a mut BitSet<ValueId>,
    inherited_stack: BTreeMap<BlockId, (BlockId, SymStack)>,
    planned_blocks: BitSet<BlockId>,
    search_scratch: NormalizeSearchScratch,
    observer: &'a mut O,
}

impl<'a, 'ctx, O: StackifyObserver> IterationPlanner<'a, 'ctx, O> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        ctx: &'a StackifyContext<'ctx>,
        spill: SpillSet<'a>,
        slots: &'a mut SpillSlotPools,
        templates: &'a SecondaryMap<BlockId, BlockTemplate>,
        terminal_chain_blocks: &'a SecondaryMap<BlockId, bool>,
        alloc: &'a mut StackifyAlloc,
        spill_requests: &'a mut BitSet<ValueId>,
        inherited_stack: BTreeMap<BlockId, (BlockId, SymStack)>,
        observer: &'a mut O,
    ) -> Self {
        Self {
            ctx,
            spill,
            slots,
            templates,
            terminal_chain_blocks,
            alloc,
            spill_requests,
            inherited_stack,
            planned_blocks: BitSet::default(),
            search_scratch: NormalizeSearchScratch::default(),
            observer,
        }
    }

    fn with_actions_planner<R>(
        &mut self,
        stack: &mut SymStack,
        actions: &mut Actions,
        free_slots: &mut FreeSlotPools,
        f: impl FnOnce(&mut Planner) -> R,
    ) -> R {
        let mem = planner::MemPlan::new(
            self.spill,
            &mut *self.spill_requests,
            self.ctx,
            &self.alloc.spill_obj,
            &self.alloc.exact_local_addr,
            free_slots,
            &mut *self.slots,
        );
        let mut planner = Planner::new(self.ctx, stack, actions, mem, &mut self.search_scratch);
        f(&mut planner)
    }

    pub(super) fn plan_blocks(&mut self) {
        for &block in self.ctx.dom.rpo() {
            if block != self.ctx.entry && !self.ctx.dom.is_reachable(block) {
                continue;
            }

            self.observer
                .on_block_header(self.ctx.func, block, &self.templates[block]);
            self.plan_block(block);
        }
    }

    fn plan_block(&mut self, block: BlockId) {
        let mut free_slots: FreeSlotPools = FreeSlotPools::default();
        let mut prologue: Actions = Actions::new();

        self.planned_blocks.insert(block);

        let (remaining_uses, live_future, live_out) =
            BlockSimState::block_live_sets(self.ctx, block);

        let inherited = self.inherited_stack.remove(&block);
        let stack = if self.terminal_chain_blocks[block] {
            SymStack::opaque_prefix_empty(self.ctx.has_internal_return)
        } else if let Some((pred, mut inh)) = inherited {
            // Dynamic entry stack (single predecessor).
            if block != self.ctx.entry {
                debug_assert_eq!(
                    self.ctx.cfg.pred_num_of(block),
                    1,
                    "inherited stack implies single-predecessor block"
                );
                self.observer.on_block_inherited(
                    self.ctx.func,
                    block,
                    pred,
                    &inh,
                    &live_future,
                    &live_out,
                );
                let has_phi_params = !self.ctx.phi_results[block].is_empty();
                let in_cycle = self
                    .ctx
                    .scc
                    .scc_of(block)
                    .map(|scc| self.ctx.scc.scc_data(scc).is_cycle)
                    .unwrap_or(false);

                // Single-predecessor, acyclic blocks without phis do not need exact entry
                // template normalization. Keeping the inherited stack avoids pointless bottom
                // reshuffling that can cascade into SWAP/POP churn.
                if has_phi_params || in_cycle {
                    let templates = self.templates;
                    self.with_actions_planner(
                        &mut inh,
                        &mut prologue,
                        &mut free_slots,
                        |planner| {
                            planner.plan_edge_fixup(templates, pred, block);
                        },
                    );
                }
                self.observer.on_block_prologue(&prologue);
            }
            inh
        } else {
            SymStack::from_template(&self.templates[block], self.ctx.has_internal_return)
        };

        let state = BlockSimState::with_live_sets(
            block,
            stack,
            free_slots,
            prologue,
            remaining_uses,
            live_future,
            live_out,
        );
        let state = run_block_sim(self, state);

        // If the block had no lowered instructions, inject prologue into the terminator.
        if !state.prologue.is_empty()
            && !state.injected_prologue
            && let Some(term) = self.ctx.func.layout.last_inst_of(block)
        {
            self.alloc.pre_actions[term].extend_from_slice(&state.prologue);
        }
    }
}

impl<'a, 'ctx, O: StackifyObserver> BlockSimMode<'ctx> for IterationPlanner<'a, 'ctx, O> {
    fn ctx(&self) -> &StackifyContext<'ctx> {
        self.ctx
    }

    fn operand_prep_mode(&self) -> OperandPrepMode {
        Exact
    }

    fn call_uses_stack_continuation(&self, inst: InstId) -> bool {
        call_has_local_return(self.ctx.func, inst)
    }

    fn scratch_slots(&self) -> &SlotPool {
        &self.slots.scratch
    }

    fn clear_inst_actions(&mut self, inst: InstId) {
        self.alloc.pre_actions[inst].clear();
        self.alloc.post_actions[inst].clear();
        self.alloc.brtable_actions[inst].clear();
    }

    fn pre_actions_len(&self, inst: InstId) -> usize {
        self.alloc.pre_actions[inst].len()
    }

    fn with_pre_actions<R>(&mut self, inst: InstId, f: impl FnOnce(&mut Actions) -> R) -> R {
        f(&mut self.alloc.pre_actions[inst])
    }

    fn take_pre_actions_for_br_table(&mut self, inst: InstId) -> Actions {
        std::mem::take(&mut self.alloc.pre_actions[inst])
    }

    fn with_planner<R>(
        &mut self,
        stack: &mut SymStack,
        free_slots: &mut FreeSlotPools,
        sink: PlannerActionSink<'_>,
        f: impl FnOnce(&mut Planner<'_, '_>) -> R,
    ) -> R {
        match sink {
            PlannerActionSink::Pre(inst) => {
                let mem = planner::MemPlan::new(
                    self.spill,
                    &mut *self.spill_requests,
                    self.ctx,
                    &self.alloc.spill_obj,
                    &self.alloc.exact_local_addr,
                    free_slots,
                    &mut *self.slots,
                );
                let mut planner = Planner::new(
                    self.ctx,
                    stack,
                    &mut self.alloc.pre_actions[inst],
                    mem,
                    &mut self.search_scratch,
                );
                f(&mut planner)
            }
            PlannerActionSink::Post(inst) => {
                let mem = planner::MemPlan::new(
                    self.spill,
                    &mut *self.spill_requests,
                    self.ctx,
                    &self.alloc.spill_obj,
                    &self.alloc.exact_local_addr,
                    free_slots,
                    &mut *self.slots,
                );
                let mut planner = Planner::new(
                    self.ctx,
                    stack,
                    &mut self.alloc.post_actions[inst],
                    mem,
                    &mut self.search_scratch,
                );
                f(&mut planner)
            }
            PlannerActionSink::BrTableCase {
                inst,
                case_idx,
                prefix,
            } => {
                let mut actions = Actions::new();
                if let Some(prefix) = prefix {
                    actions.extend_from_slice(prefix);
                }
                let mem = planner::MemPlan::new(
                    self.spill,
                    &mut *self.spill_requests,
                    self.ctx,
                    &self.alloc.spill_obj,
                    &self.alloc.exact_local_addr,
                    free_slots,
                    &mut *self.slots,
                );
                let result = {
                    let mut planner =
                        Planner::new(self.ctx, stack, &mut actions, mem, &mut self.search_scratch);
                    f(&mut planner)
                };
                debug_assert_eq!(self.alloc.brtable_actions[inst].len(), case_idx);
                self.alloc.brtable_actions[inst].push(actions);
                result
            }
        }
    }

    fn on_inst_start(
        &mut self,
        state: &mut BlockSimState,
        inst: InstId,
        last_use: &BitSet<ValueId>,
    ) {
        if !state.prologue.is_empty() && !state.injected_prologue {
            self.alloc.pre_actions[inst].extend_from_slice(&state.prologue);
            state.injected_prologue = true;
        }
        self.observer.on_inst_start(
            self.ctx.func,
            inst,
            &state.stack,
            state.live_future(),
            state.live_out(),
            last_use,
        );
    }

    fn on_alias_noop(&mut self, inst: InstId, args: &[ValueId], results: &[ValueId]) {
        self.observer.on_inst_actions("cleanup", &[], None);
        self.observer.on_inst_actions("pre", &[], None);
        self.observer
            .on_inst_normal(self.ctx.func, inst, args, results);
        self.observer.on_inst_actions("post", &[], None);
    }

    fn on_cleanup_actions(&mut self, inst: InstId, start: usize, end: usize) {
        self.observer
            .on_inst_actions("cleanup", &self.alloc.pre_actions[inst][start..end], None);
    }

    fn on_pre_actions(&mut self, inst: InstId, start: usize) {
        self.observer
            .on_inst_actions("pre", &self.alloc.pre_actions[inst][start..], None);
    }

    fn on_post_actions(&mut self, inst: InstId) {
        self.observer
            .on_inst_actions("post", &self.alloc.post_actions[inst], None);
    }

    fn on_normal_inst(&mut self, inst: InstId, args: &[ValueId], results: &[ValueId]) {
        self.observer
            .on_inst_normal(self.ctx.func, inst, args, results);
    }

    fn on_return(&mut self, inst: InstId, start: usize) {
        self.observer
            .on_inst_actions("return", &self.alloc.pre_actions[inst][start..], None);
        let ret_vals: SmallVec<[ValueId; 16]> = self
            .ctx
            .func
            .dfg
            .return_args(inst)
            .map(|args| args.iter().copied().collect())
            .unwrap_or_default();
        self.observer
            .on_inst_return(self.ctx.func, inst, ret_vals.as_slice());
    }

    fn on_jump(
        &mut self,
        state: &mut BlockSimState,
        inst: InstId,
        dest: BlockId,
        _stack: SymStack,
        action_start: usize,
    ) {
        if self.terminal_chain_blocks[dest] {
        } else if self.ctx.cfg.pred_num_of(dest) == 1
            && dest != self.ctx.entry
            && !self.planned_blocks.contains(dest)
        {
            self.inherited_stack
                .entry(dest)
                .or_insert_with(|| (state.block, state.stack.clone()));
        } else {
            let templates = self.templates;
            let src = state.block;
            self.with_planner(
                &mut state.stack,
                &mut state.free_slots,
                PlannerActionSink::Pre(inst),
                |planner| planner.plan_edge_fixup(templates, src, dest),
            );
        }

        self.observer.on_inst_actions(
            "exit",
            &self.alloc.pre_actions[inst][action_start..],
            Some(dest),
        );
        self.observer.on_inst_jump(inst, dest);
    }

    fn on_branch(&mut self, inst: InstId, cond: ValueId, dests: &[BlockId]) {
        self.observer.on_inst_br(self.ctx.func, inst, cond, dests);
    }

    fn on_branch_edge(
        &mut self,
        state: &mut BlockSimState,
        _inst: InstId,
        succ: BlockId,
        stack: SymStack,
    ) {
        debug_assert_eq!(
            self.ctx.cfg.pred_num_of(succ),
            1,
            "no critical edges: branch target must be single-pred"
        );
        self.inherited_stack
            .entry(succ)
            .or_insert_with(|| (state.block, stack));
    }

    fn on_br_table_edge(
        &mut self,
        state: &mut BlockSimState,
        _inst: InstId,
        succ: BlockId,
        stack: SymStack,
        _kind: BrTableEdgeKind,
    ) {
        debug_assert_eq!(
            self.ctx.cfg.pred_num_of(succ),
            1,
            "no critical edges: br_table target must be single-pred"
        );
        self.inherited_stack
            .entry(succ)
            .or_insert_with(|| (state.block, stack));
    }

    fn on_br_table(&mut self, inst: InstId) {
        self.observer.on_inst_br_table(inst);
    }
}

pub(super) fn skip_pre_exit_cleanup(func: &Function, inst: InstId) -> bool {
    func.dfg.is_exit(inst) && !func.dfg.is_return(inst)
}

pub(super) fn count_block_uses(
    func: &Function,
    block: BlockId,
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
) -> (BTreeMap<ValueId, u32>, BitSet<ValueId>) {
    let mut counts: BTreeMap<ValueId, u32> = BTreeMap::new();
    for inst in func.layout.iter_inst(block) {
        if func.dfg.is_phi(inst) {
            continue;
        }
        for v in func.dfg.inst(inst).collect_values() {
            let v = value_aliases[v].unwrap_or(v);
            if func.dfg.value_is_imm(v) {
                continue;
            }
            *counts.entry(v).or_insert(0) += 1;
        }
    }
    let live_future: BitSet<ValueId> = counts.keys().copied().collect();
    (counts, live_future)
}

fn pop_dead_tops(
    stack: &mut SymStack,
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
    actions: &mut Actions,
) {
    while let Some(StackItem::Value(v)) = stack.top() {
        if live_future.contains(*v) || live_out.contains(*v) {
            break;
        }
        stack.pop(actions);
    }
}

pub(super) fn clean_dead_stack_prefix(
    reach: StackifyReachability,
    stack: &mut SymStack,
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
    actions: &mut Actions,
) {
    // Two local cleanups:
    // - pop any dead values that reach the top
    // - if a live value is on top and there is a contiguous dead chain directly beneath it,
    //   swap the live value down and pop the dead chain off the top.
    loop {
        let before_len = stack.len();
        pop_dead_tops(stack, live_future, live_out, actions);

        // If the top is not a normal value, don't try to reorder under it.
        let Some(StackItem::Value(top)) = stack.top() else {
            break;
        };
        if !live_future.contains(*top) && !live_out.contains(*top) {
            // Should have been handled by `pop_dead_tops`, but keep looping defensively.
            continue;
        }

        let is_dead = |v: ValueId| !live_future.contains(v) && !live_out.contains(v);
        let dead_run = stack
            .iter()
            .skip(1)
            .take_while(|&v| matches!(v, StackItem::Value(v) if is_dead(*v)))
            .count();
        if dead_run == 0 {
            break;
        }

        // Swap the top live value with the deepest dead value in the contiguous chain (within
        // SWAP16 reach), then pop that chunk off. Repeat until the chain is gone.
        let mut remaining = dead_run;
        while remaining > 0 {
            let swap_depth = remaining.min(reach.swap_max.saturating_sub(1));
            stack.swap(swap_depth, actions);
            stack.pop_n(swap_depth, actions);
            remaining -= swap_depth;
        }

        if stack.len() == before_len {
            break;
        }
    }
}

pub(super) fn operand_order_for_evm(
    func: &Function,
    inst: InstId,
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
) -> SmallVec<[ValueId; 8]> {
    let is = func.inst_set();
    let data = func.dfg.inst(inst);
    if let Some(malloc) = <&evm::EvmMalloc as InstDowncast>::downcast(is, data) {
        let size = *malloc.size();
        if func.dfg.value_is_imm(size) {
            // `evm_malloc` immediates are lowered as compile-time constants.
            return SmallVec::new();
        }

        return smallvec::smallvec![value_aliases[size].unwrap_or(size)];
    }

    if let Some(gep) = <&data::Gep as InstDowncast>::downcast(is, data) {
        let mut args: SmallVec<[ValueId; 8]> = SmallVec::new();
        let values = gep.values().as_slice();
        let Some((&base, indices)) = values.split_first() else {
            panic!("gep without operands");
        };
        args.push(value_aliases[base].unwrap_or(base));

        // GEP immediate indices are compile-time metadata for EVM lowering; they do not need to
        // be materialized as runtime stack operands unless they fail immediate-u32 folding.
        args.extend(
            indices
                .iter()
                .copied()
                .filter(|v| {
                    !func.dfg.value_is_imm(*v)
                        || func.dfg.value_imm(*v).and_then(immediate_u32).is_none()
                })
                .map(|v| value_aliases[v].unwrap_or(v)),
        );
        return args;
    }

    // This IR mostly already stores operands in the order expected by the EVM backend
    // (e.g. `mstore addr value`, `gt lhs rhs`, `shl bits value`).
    //
    // Keeping this as a dedicated hook makes the required operand conventions explicit.
    let mut args: SmallVec<[ValueId; 8]> = func
        .dfg
        .inst(inst)
        .collect_values()
        .into_iter()
        .map(|v| value_aliases[v].unwrap_or(v))
        .collect();

    // For internal calls, we want the continuation address to end up directly under the call
    // operands. We arrange the operands as a left rotation so that after the backend pushes the
    // continuation (at the `Action::PushContinuationOffset` marker), a single `SWAP{arity}` places
    // it under the operands and restores the callee ABI operand order.
    if call_has_local_return(func, inst) && !args.is_empty() {
        args.as_mut_slice().rotate_left(1);
    }

    args
}

fn call_has_local_return(func: &Function, inst: InstId) -> bool {
    func.dfg.call_info(inst).is_some_and(|call| {
        func.ctx()
            .func_effects(call.callee())
            .may_return_to_caller()
    })
}

pub(super) fn inst_is_noop_alias_cast(
    ctx: &super::builder::StackifyContext<'_>,
    inst: InstId,
    args: &[ValueId],
    res: Option<ValueId>,
) -> bool {
    let Some(res) = res else {
        return false;
    };
    if args != [res] {
        return false;
    }

    let is = ctx.func.inst_set();
    let data = ctx.func.dfg.inst(inst);
    <&cast::Bitcast as InstDowncast>::downcast(is, data).is_some()
        || <&cast::IntToPtr as InstDowncast>::downcast(is, data).is_some()
        || <&cast::PtrToInt as InstDowncast>::downcast(is, data).is_some()
}

pub(super) fn consume_operand_uses(
    func: &Function,
    args: &[ValueId],
    remaining_uses: &mut BTreeMap<ValueId, u32>,
    live_future: &mut BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
    scratch_slots: &SlotPool,
    free_scratch_slots: &mut FreeSlots,
) {
    for &v in args {
        if !func.dfg.value_is_imm(v)
            && let Some(n) = remaining_uses.get_mut(&v)
        {
            let before = *n;
            *n = n.saturating_sub(1);
            if before != 0 && *n == 0 {
                live_future.remove(v);
                if !live_out.contains(v) {
                    scratch_slots.release_if_assigned(v, free_scratch_slots);
                }
            }
        }
    }
}

pub(super) fn last_use_values_in_inst(
    func: &Function,
    args: &[ValueId],
    remaining_uses: &BTreeMap<ValueId, u32>,
    live_out: &BitSet<ValueId>,
) -> BitSet<ValueId> {
    let mut inst_counts: BTreeMap<ValueId, u32> = BTreeMap::new();
    for &v in args.iter() {
        if func.dfg.value_is_imm(v) {
            continue;
        }
        *inst_counts.entry(v).or_insert(0) += 1;
    }

    let mut last_use: BitSet<ValueId> = BitSet::default();
    for (v, count) in inst_counts {
        let rem = remaining_uses.get(&v).copied().unwrap_or(0);
        if rem == count && !live_out.contains(v) {
            last_use.insert(v);
        }
    }
    last_use
}

pub(super) fn improve_reachability_before_operands(
    func: &Function,
    args: &[ValueId],
    reach: StackifyReachability,
    stack: &mut SymStack,
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
    actions: &mut Actions,
) {
    const AGGRESSIVE_REACHABILITY_DEPTH: usize = 20;

    let mut protected_args: BitSet<ValueId> = BitSet::default();
    for &arg in args.iter() {
        if !func.dfg.value_is_imm(arg) {
            protected_args.insert(arg);
        }
    }

    // If at least one operand is on the stack but unreachable by `DUP16`, attempt a more
    // aggressive cleanup to bring it back into reach. This extends slightly past `SWAP16` reach
    // by allowing deletions that shift the stack (e.g. popping dead/cheap values above an
    // operand at depth 18-20).
    let mut needs_aggressive = false;
    for &arg in args.iter() {
        if !func.dfg.value_is_imm(arg)
            && stack.find_reachable_value(arg, reach.dup_max).is_none()
            && stack
                .find_reachable_value(arg, AGGRESSIVE_REACHABILITY_DEPTH)
                .is_some()
        {
            needs_aggressive = true;
            break;
        }
    }
    if !needs_aggressive {
        return;
    }

    // Bound the amount of cleanup we do per instruction to avoid pathological swap chains.
    const MAX_DELETIONS: usize = 8;
    let mut deletions: usize = 0;

    while deletions < MAX_DELETIONS {
        let mut progressed = false;

        for &arg in args.iter() {
            if !func.dfg.value_is_imm(arg)
                && stack.find_reachable_value(arg, reach.dup_max).is_none()
                && let Some(pos) = stack.find_reachable_value(arg, AGGRESSIVE_REACHABILITY_DEPTH)
                && let Some(victim) = choose_reachability_victim(
                    func,
                    stack,
                    pos,
                    &protected_args,
                    reach,
                    live_future,
                    live_out,
                )
            {
                stack.stable_delete_at_depth(victim + 1, actions);
                deletions += 1;
                progressed = true;
                break;
            }
        }

        if !progressed {
            break;
        }
    }
}

fn choose_reachability_victim(
    func: &Function,
    stack: &SymStack,
    above: usize,
    protected_args: &BitSet<ValueId>,
    reach: StackifyReachability,
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
) -> Option<usize> {
    let limit = stack.len_above_func_ret().min(reach.swap_max);
    let above = above.min(limit);

    // 1) Prefer deleting dead values, starting from the shallowest depth to minimize `SWAP*`
    // chains. This includes immediates: if they're dead, removing them cannot introduce new
    // rematerialization cost.
    for (i, item) in stack.iter().take(above).enumerate() {
        if let StackItem::Value(v) = item
            && !protected_args.contains(*v)
            && !live_future.contains(*v)
            && !live_out.contains(*v)
        {
            return Some(i);
        }
    }

    // 2) Then evict "cheap" immediates (they are always rematerializable).
    for (i, item) in stack.iter().take(above).enumerate() {
        if let StackItem::Value(v) = item
            && !protected_args.contains(*v)
            && func.dfg.value_is_imm(*v)
            && is_evictable_imm(func, *v)
        {
            return Some(i);
        }
    }

    // 3) Then delete redundant duplicates of non-operands (keeping the shallowest copy).
    let mut first_index: BTreeMap<ValueId, usize> = BTreeMap::new();
    for (i, item) in stack.iter().take(above).enumerate() {
        let StackItem::Value(v) = item else {
            continue;
        };
        first_index.entry(*v).or_insert(i);
    }

    for (i, item) in stack.iter().take(above).enumerate() {
        if let StackItem::Value(v) = item
            && !protected_args.contains(*v)
            && let Some(&first) = first_index.get(v)
            && first != i
        {
            return Some(i);
        }
    }

    None
}

fn is_evictable_imm(func: &Function, v: ValueId) -> bool {
    const MAX_PUSH_DATA_BYTES: usize = 2; // <= PUSH2
    let Some(imm) = func.dfg.value_imm(v) else {
        return false;
    };
    imm_push_data_len(imm) <= MAX_PUSH_DATA_BYTES
}

fn imm_push_data_len(imm: Immediate) -> usize {
    if imm.is_zero() {
        return 0;
    }

    fn shrink_len(bytes: &[u8]) -> usize {
        debug_assert!(!bytes.is_empty());

        let is_neg = (bytes[0] & 0x80) != 0;
        let skip = if is_neg { 0xff } else { 0x00 };

        let mut idx: usize = 0;
        while idx < bytes.len() && bytes[idx] == skip {
            idx += 1;
        }
        let mut len = bytes.len().saturating_sub(idx);
        if len == 0 {
            len = 1;
        }

        // Negative numbers need a leading 1 bit for sign-extension.
        if is_neg {
            let first = bytes.get(idx).copied().unwrap_or(0xff);
            if first < 0x80 {
                len = len.saturating_add(1);
            }
        }
        len
    }

    match imm {
        Immediate::I1(v) => v as usize,
        Immediate::I8(v) => shrink_len(&v.to_be_bytes()),
        Immediate::I16(v) => shrink_len(&v.to_be_bytes()),
        Immediate::I32(v) => shrink_len(&v.to_be_bytes()),
        Immediate::I64(v) => shrink_len(&v.to_be_bytes()),
        Immediate::I128(v) => shrink_len(&v.to_be_bytes()),
        Immediate::I256(v) => shrink_len(&v.to_u256().to_big_endian()),
        Immediate::EnumTag { value, .. } => shrink_len(&value.to_u256().to_big_endian()),
    }
}
