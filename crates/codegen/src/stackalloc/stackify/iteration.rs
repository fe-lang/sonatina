use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, Immediate, InstId, ValueId, inst::control_flow::BranchKind};
use std::collections::BTreeMap;

use crate::{bitset::BitSet, stackalloc::Actions};

use super::{
    DUP_MAX, SWAP_MAX,
    alloc::StackifyAlloc,
    builder::StackifyContext,
    planner::{self, Planner},
    slots::{FreeSlots, SlotState},
    spill::SpillSet,
    sym_stack::{StackItem, SymStack},
    templates::BlockTemplate,
    trace::StackifyObserver,
};

pub(super) struct IterationPlanner<'a, 'ctx, O: StackifyObserver> {
    ctx: &'a StackifyContext<'ctx>,
    spill: SpillSet<'a>,
    slots: &'a mut SlotState,
    templates: &'a SecondaryMap<BlockId, BlockTemplate>,
    alloc: &'a mut StackifyAlloc,
    spill_requests: &'a mut BitSet<ValueId>,
    inherited_stack: BTreeMap<BlockId, (BlockId, SymStack)>,
    observer: &'a mut O,
}

struct BlockPlanState {
    block: BlockId,
    free_slots: FreeSlots,
    prologue: Actions,
    injected_prologue: bool,
    remaining_uses: BTreeMap<ValueId, u32>,
    live_future: BitSet<ValueId>,
    live_out: BitSet<ValueId>,
    stack: SymStack,
}

enum InstOutcome {
    Continue,
    TerminateBlock,
}

impl<'a, 'ctx, O: StackifyObserver> IterationPlanner<'a, 'ctx, O> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        ctx: &'a StackifyContext<'ctx>,
        spill: SpillSet<'a>,
        slots: &'a mut SlotState,
        templates: &'a SecondaryMap<BlockId, BlockTemplate>,
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
            alloc,
            spill_requests,
            inherited_stack,
            observer,
        }
    }

    fn with_planner<R>(
        &mut self,
        stack: &mut SymStack,
        actions: &mut Actions,
        free_slots: &mut FreeSlots,
        f: impl FnOnce(&mut Planner) -> R,
    ) -> R {
        let mem = planner::MemPlan::new(
            self.spill,
            &mut *self.spill_requests,
            free_slots,
            &mut *self.slots,
            self.ctx.liveness,
        );
        let mut planner = Planner::new(self.ctx, stack, actions, mem);
        f(&mut planner)
    }

    fn with_pre_actions_planner<R>(
        &mut self,
        stack: &mut SymStack,
        inst: InstId,
        free_slots: &mut FreeSlots,
        f: impl FnOnce(&mut Planner) -> R,
    ) -> R {
        let actions = &mut self.alloc.pre_actions[inst];
        let mem = planner::MemPlan::new(
            self.spill,
            &mut *self.spill_requests,
            free_slots,
            &mut *self.slots,
            self.ctx.liveness,
        );
        let mut planner = Planner::new(self.ctx, stack, actions, mem);
        f(&mut planner)
    }

    fn with_post_actions_planner<R>(
        &mut self,
        stack: &mut SymStack,
        inst: InstId,
        free_slots: &mut FreeSlots,
        f: impl FnOnce(&mut Planner) -> R,
    ) -> R {
        let actions = &mut self.alloc.post_actions[inst];
        let mem = planner::MemPlan::new(
            self.spill,
            &mut *self.spill_requests,
            free_slots,
            &mut *self.slots,
            self.ctx.liveness,
        );
        let mut planner = Planner::new(self.ctx, stack, actions, mem);
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
        let mut free_slots: FreeSlots = FreeSlots::default();
        let mut prologue: Actions = Actions::new();
        let injected_prologue = false;

        // Track per-block remaining uses to implement `PopDeadTops`.
        let (remaining_uses, live_future) = count_block_uses(self.ctx.func, block);
        let mut live_out = self.ctx.liveness.block_live_outs(block).clone();
        live_out.union_with(&self.ctx.phi_out_sources[block]);

        let stack = if let Some((pred, mut inh)) = self.inherited_stack.remove(&block) {
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
                let templates = self.templates;
                self.with_planner(&mut inh, &mut prologue, &mut free_slots, |planner| {
                    planner.plan_edge_fixup(templates, pred, block);
                });
                self.observer.on_block_prologue(&prologue);
            }
            inh
        } else {
            SymStack::from_template(&self.templates[block], self.ctx.has_internal_return)
        };

        let mut state = BlockPlanState {
            block,
            free_slots,
            prologue,
            injected_prologue,
            remaining_uses,
            live_future,
            live_out,
            stack,
        };

        let empty_last_use: BitSet<ValueId> = BitSet::default();
        for inst in self.ctx.func.layout.iter_inst(block) {
            if self.ctx.func.dfg.is_phi(inst) {
                continue;
            }

            match self.plan_inst(&mut state, inst, &empty_last_use) {
                InstOutcome::Continue => {}
                InstOutcome::TerminateBlock => break,
            }
        }

        // If the block had no lowered instructions, inject prologue into the terminator.
        if !state.prologue.is_empty()
            && !state.injected_prologue
            && let Some(term) = self.ctx.func.layout.last_inst_of(block)
        {
            self.alloc.pre_actions[term].extend_from_slice(&state.prologue);
        }
    }

    fn plan_inst(
        &mut self,
        state: &mut BlockPlanState,
        inst: InstId,
        empty_last_use: &BitSet<ValueId>,
    ) -> InstOutcome {
        // Inject prologue actions once, at the first lowered instruction.
        if !state.prologue.is_empty() && !state.injected_prologue {
            self.alloc.pre_actions[inst].extend_from_slice(&state.prologue);
            state.injected_prologue = true;
        }

        let is_call = self.ctx.func.dfg.is_call(inst);
        let is_normal =
            self.ctx.func.dfg.branch_info(inst).is_none() && !self.ctx.func.dfg.is_return(inst);

        let mut args = SmallVec::<[ValueId; 8]>::new();
        let mut consume_last_use: BitSet<ValueId> = BitSet::default();
        if is_normal {
            args = operand_order_for_evm(self.ctx.func, inst);
            consume_last_use = last_use_values_in_inst(
                self.ctx.func,
                &args,
                &state.remaining_uses,
                &state.live_out,
            );
        }
        let last_use = if is_normal {
            &consume_last_use
        } else {
            empty_last_use
        };
        self.observer.on_inst_start(
            self.ctx.func,
            inst,
            &state.stack,
            &state.live_future,
            &state.live_out,
            last_use,
        );

        // Stable cleanup: pop dead values (and dead chains under the top live value).
        //
        // For calls, do this before pushing the continuation target so we can still
        // pop dead values that were on top of the caller's stack segment.
        let before_cleanup_len = self.alloc.pre_actions[inst].len();
        clean_dead_stack_prefix(
            &mut state.stack,
            &state.live_future,
            &state.live_out,
            &mut self.alloc.pre_actions[inst],
        );

        // Try to improve operand reachability before operand preparation:
        // - do nothing if all operands are already `DUP16`-reachable
        // - otherwise, if an operand is close (within a small depth window), delete dead values,
        //   redundant duplicates, and (small) immediates above it to pull it back into reach
        // This helps avoid unnecessary spill-set growth.
        if is_normal {
            improve_reachability_before_operands(
                self.ctx.func,
                &args,
                &mut state.stack,
                &state.live_future,
                &state.live_out,
                &mut self.alloc.pre_actions[inst],
            );
        }
        let after_cleanup_len = self.alloc.pre_actions[inst].len();
        self.observer.on_inst_actions(
            "cleanup",
            &self.alloc.pre_actions[inst][before_cleanup_len..after_cleanup_len],
            None,
        );

        // Calls push a continuation target before argument setup (the backend consumes
        // `Action::PushContinuationOffset`).
        if is_call {
            state
                .stack
                .push_call_continuation(&mut self.alloc.pre_actions[inst]);
        }

        if let Some(branch) = self.ctx.func.dfg.branch_info(inst) {
            match branch.branch_kind() {
                BranchKind::Jump(jump) => {
                    // Fix up the stack so the successor observes its chosen entry template
                    // (including any phi results).
                    let dest = *jump.dest();
                    let templates = self.templates;
                    let src = state.block;
                    self.with_pre_actions_planner(
                        &mut state.stack,
                        inst,
                        &mut state.free_slots,
                        |p| {
                            p.plan_edge_fixup(templates, src, dest);
                        },
                    );

                    self.observer.on_inst_actions(
                        "exit",
                        &self.alloc.pre_actions[inst][after_cleanup_len..],
                        Some(dest),
                    );
                    self.observer.on_inst_jump(inst, dest);
                    return InstOutcome::TerminateBlock;
                }
                BranchKind::Br(br) => {
                    // Ensure the branch condition is on top for the backend's JUMPI sequence.
                    // We intentionally do not canonicalize the transfer region here: branch
                    // targets are single-predecessor blocks (after critical-edge splitting)
                    // and will run an entry prologue to normalize to their templates.
                    let cond = *br.cond();
                    let consume_last_use = last_use_values_in_inst(
                        self.ctx.func,
                        &[cond],
                        &state.remaining_uses,
                        &state.live_out,
                    );

                    improve_reachability_before_operands(
                        self.ctx.func,
                        &[cond],
                        &mut state.stack,
                        &state.live_future,
                        &state.live_out,
                        &mut self.alloc.pre_actions[inst],
                    );
                    self.with_pre_actions_planner(
                        &mut state.stack,
                        inst,
                        &mut state.free_slots,
                        |p| {
                            p.prepare_operands(&[cond], &consume_last_use);
                        },
                    );

                    self.observer.on_inst_actions(
                        "pre",
                        &self.alloc.pre_actions[inst][after_cleanup_len..],
                        None,
                    );
                    let dests = branch.dests();
                    self.observer
                        .on_inst_br(self.ctx.func, inst, cond, dests.as_slice());

                    // The backend consumes the condition value for the actual branch.
                    let mut post_branch_stack = state.stack.clone();
                    post_branch_stack.pop_operand();

                    for succ in dests.iter().copied() {
                        debug_assert_eq!(
                            self.ctx.cfg.pred_num_of(succ),
                            1,
                            "no critical edges: branch target must be single-pred"
                        );
                        self.inherited_stack
                            .entry(succ)
                            .or_insert_with(|| (state.block, post_branch_stack.clone()));
                    }
                    return InstOutcome::TerminateBlock;
                }
                BranchKind::BrTable(table) => {
                    // Build per-case compare actions. As with `br`, we normalize successor entry
                    // stacks in their block prologues, so we keep the current stack order here.
                    let scrutinee = *table.scrutinee();

                    improve_reachability_before_operands(
                        self.ctx.func,
                        &[scrutinee],
                        &mut state.stack,
                        &state.live_future,
                        &state.live_out,
                        &mut self.alloc.pre_actions[inst],
                    );

                    // `br_table` lowering uses per-case `Allocator::read()` calls. Treat any
                    // actions accumulated for this terminator as a "one-time prefix" executed
                    // by the first case.
                    let base_actions = self.alloc.pre_actions[inst].clone();
                    self.alloc.pre_actions[inst].clear();

                    // The br_table lowering emits `EQ; JUMPI` for each case in order.
                    for (case_idx, &(case_val, dest)) in table.table().iter().enumerate() {
                        let mut case_actions = Actions::new();
                        let mut case_stack = state.stack.clone();

                        // Put [scrutinee, case_val] on stack for EQ (order doesn't matter).
                        if case_idx == 0 {
                            case_actions.extend_from_slice(&base_actions);
                        }
                        self.with_planner(
                            &mut case_stack,
                            &mut case_actions,
                            &mut state.free_slots,
                            |p| {
                                let consume_last_use = BitSet::<ValueId>::default();
                                p.prepare_operands(&[scrutinee, case_val], &consume_last_use);
                            },
                        );
                        self.alloc
                            .brtable_actions
                            .insert((inst, scrutinee, case_val), case_actions);

                        // Destination blocks inherit the base stack state (the compare chain
                        // restores it on all non-taken paths).
                        debug_assert_eq!(
                            self.ctx.cfg.pred_num_of(dest),
                            1,
                            "no critical edges: br_table target must be single-pred"
                        );
                        self.inherited_stack
                            .entry(dest)
                            .or_insert_with(|| (state.block, state.stack.clone()));
                    }

                    if let Some(default) = table.default() {
                        debug_assert_eq!(
                            self.ctx.cfg.pred_num_of(*default),
                            1,
                            "no critical edges: br_table default must be single-pred"
                        );
                        self.inherited_stack
                            .entry(*default)
                            .or_insert_with(|| (state.block, state.stack.clone()));
                    }

                    self.observer.on_inst_br_table(inst);
                    return InstOutcome::TerminateBlock;
                }
            }
        }

        if self.ctx.func.dfg.is_return(inst) {
            // Internal return: ensure only (return_val?, ret_addr) remain above the opaque caller
            // stack segment.
            self.with_pre_actions_planner(&mut state.stack, inst, &mut state.free_slots, |p| {
                p.plan_internal_return(inst);
            });
            self.observer.on_inst_actions(
                "return",
                &self.alloc.pre_actions[inst][after_cleanup_len..],
                None,
            );
            self.observer
                .on_inst_return(self.ctx.func, inst, self.ctx.func.dfg.as_return(inst));
            return InstOutcome::TerminateBlock;
        }

        // Normal instruction.
        self.with_pre_actions_planner(&mut state.stack, inst, &mut state.free_slots, |p| {
            p.prepare_operands_for_inst(inst, &mut args, &consume_last_use);
        });

        self.observer.on_inst_actions(
            "pre",
            &self.alloc.pre_actions[inst][after_cleanup_len..],
            None,
        );
        let res = self.ctx.func.dfg.inst_result(inst);
        self.observer
            .on_inst_normal(self.ctx.func, inst, &args, res);

        // Update remaining uses.
        for &v in args.iter() {
            if !self.ctx.func.dfg.value_is_imm(v)
                && let Some(n) = state.remaining_uses.get_mut(&v)
            {
                let before = *n;
                *n = n.saturating_sub(1);
                if before != 0 && *n == 0 {
                    state.live_future.remove(v);
                    if !state.live_out.contains(v) {
                        self.slots.release_if_assigned(v, &mut state.free_slots);
                    }
                }
            }
        }

        let arity = args.len();
        state.stack.pop_n_operands(arity);

        // Call consumes the temporary continuation target (not an SSA value).
        if is_call {
            state.stack.remove_call_ret_addr();
        }

        if let Some(res) = res {
            state.stack.push_value(res);
            let res_live = state.live_future.contains(res) || state.live_out.contains(res);
            if res_live {
                self.with_post_actions_planner(
                    &mut state.stack,
                    inst,
                    &mut state.free_slots,
                    |planner| {
                        planner.emit_store_if_spilled(res);
                    },
                );
            }
        }

        self.observer
            .on_inst_actions("post", &self.alloc.post_actions[inst], None);

        InstOutcome::Continue
    }
}

pub(super) fn count_block_uses(
    func: &Function,
    block: BlockId,
) -> (BTreeMap<ValueId, u32>, BitSet<ValueId>) {
    let mut counts: BTreeMap<ValueId, u32> = BTreeMap::new();
    for inst in func.layout.iter_inst(block) {
        if func.dfg.is_phi(inst) {
            continue;
        }
        for v in func.dfg.inst(inst).collect_values() {
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
            let swap_depth = remaining.min(SWAP_MAX - 1);
            stack.swap(swap_depth, actions);
            stack.pop_n(swap_depth, actions);
            remaining -= swap_depth;
        }

        if stack.len() == before_len {
            break;
        }
    }
}

pub(super) fn operand_order_for_evm(func: &Function, inst: InstId) -> SmallVec<[ValueId; 8]> {
    // This IR mostly already stores operands in the order expected by the EVM backend
    // (e.g. `mstore addr value`, `gt lhs rhs`, `shl bits value`).
    //
    // Keeping this as a dedicated hook makes the required operand conventions explicit.
    func.dfg.inst(inst).collect_values().into_iter().collect()
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
            && stack.find_reachable_value(arg, DUP_MAX).is_none()
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
                && stack.find_reachable_value(arg, DUP_MAX).is_none()
                && let Some(pos) = stack.find_reachable_value(arg, AGGRESSIVE_REACHABILITY_DEPTH)
                && let Some(victim) = choose_reachability_victim(
                    func,
                    stack,
                    pos,
                    &protected_args,
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
    live_future: &BitSet<ValueId>,
    live_out: &BitSet<ValueId>,
) -> Option<usize> {
    let limit = stack.len_above_func_ret().min(SWAP_MAX);
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
    }
}
