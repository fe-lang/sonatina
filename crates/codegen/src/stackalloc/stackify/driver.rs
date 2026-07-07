use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, InstId, ValueId};
use std::collections::BTreeMap;

use crate::{bitset::BitSet, stackalloc::Actions};

use super::{
    alloc::StackifyAlloc,
    block::{BlockPlanner, BlockSimState, PlannerActionSink},
    builder::StackifyContext,
    planner::{self, MemState, NormalizeSearchScratch, Planner},
    slots::{FreeSlotPools, SlotPool},
    sym_stack::SymStack,
    templates::{
        BlockTemplate, TransferOrder, canonical_transfer_order, choose_transfer, project_transfer,
    },
    trace::StackifyObserver,
    uses::UseTracker,
};

pub(super) struct FunctionPlanner<'a, 'ctx, O: StackifyObserver> {
    ctx: &'a StackifyContext<'ctx>,
    /// Memory-planning state (spill set, provisional object ids, spill/object requests, slot
    /// pools) handed to each `MemPlan` in one reborrow.
    mem: MemState<'a>,
    templates: &'a mut SecondaryMap<BlockId, BlockTemplate>,
    terminal_chain_blocks: &'a BitSet<BlockId>,
    carry_in: &'a SecondaryMap<BlockId, BitSet<ValueId>>,
    alloc: &'a mut StackifyAlloc,
    inherited_stack: BTreeMap<BlockId, (BlockId, SymStack)>,
    pending_edges: BTreeMap<BlockId, Vec<PendingEdge>>,
    planned_blocks: BitSet<BlockId>,
    search_scratch: &'a mut NormalizeSearchScratch,
    observer: &'a mut O,
}

struct PendingEdge {
    pred: BlockId,
    inst: InstId,
    stack: SymStack,
    free_slots: FreeSlotPools,
    action_start: usize,
    /// Index of this edge's `DeferredExit` event in the observer's trace (0 for `NullObserver`),
    /// used to backfill the exit fixup actions once the merge template is resolved.
    trace_token: usize,
}

impl<'a, 'ctx, O: StackifyObserver> FunctionPlanner<'a, 'ctx, O> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        ctx: &'a StackifyContext<'ctx>,
        mem: MemState<'a>,
        templates: &'a mut SecondaryMap<BlockId, BlockTemplate>,
        terminal_chain_blocks: &'a BitSet<BlockId>,
        carry_in: &'a SecondaryMap<BlockId, BitSet<ValueId>>,
        alloc: &'a mut StackifyAlloc,
        inherited_stack: BTreeMap<BlockId, (BlockId, SymStack)>,
        search_scratch: &'a mut NormalizeSearchScratch,
        observer: &'a mut O,
    ) -> Self {
        Self {
            ctx,
            mem,
            templates,
            terminal_chain_blocks,
            carry_in,
            alloc,
            inherited_stack,
            pending_edges: BTreeMap::new(),
            planned_blocks: BitSet::default(),
            search_scratch,
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
            &mut self.mem,
            self.ctx,
            &self.alloc.exact_local_addr,
            free_slots,
        );
        let mut planner = Planner::new(self.ctx, stack, actions, mem, &mut *self.search_scratch);
        f(&mut planner)
    }

    pub(super) fn plan_blocks(&mut self) {
        for &block in self.ctx.dom.rpo() {
            if block != self.ctx.entry && !self.ctx.dom.is_reachable(block) {
                continue;
            }

            self.plan_block(block);
        }

        debug_assert!(
            self.pending_edges.is_empty(),
            "unresolved stackify edges remain"
        );
    }

    fn plan_block(&mut self, block: BlockId) {
        let mut free_slots: FreeSlotPools = FreeSlotPools::default();
        let mut prologue: Actions = Actions::new();

        let uses = UseTracker::for_block(self.ctx, block);
        self.resolve_pending_edges(block);

        let inherited = self.inherited_stack.remove(&block);
        if self.terminal_chain_blocks.contains(block) {
            self.freeze_template(block, TransferOrder::new());
        } else if let Some((_pred, stack)) = inherited.as_ref() {
            self.freeze_template_from_stack(block, stack);
        } else if block != self.ctx.entry {
            self.freeze_template_canonical(block);
        }

        self.observer
            .on_block_header(self.ctx.func, block, &self.templates[block]);
        self.planned_blocks.insert(block);

        let stack = if self.terminal_chain_blocks.contains(block) {
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
                    uses.live_future(),
                    uses.live_out(),
                );
                let has_phi_params = !self.ctx.phi_results[block].is_empty();

                // Single-predecessor blocks without phis do not need exact entry
                // template normalization. Keeping the inherited stack avoids pointless bottom
                // reshuffling that can cascade into SWAP/POP churn.
                if has_phi_params {
                    let tmpl = self.templates[block].clone();
                    self.with_actions_planner(
                        &mut inh,
                        &mut prologue,
                        &mut free_slots,
                        |planner| {
                            planner.plan_edge_fixup_to_template(&tmpl, pred, block);
                        },
                    );
                }
                self.observer.on_block_prologue(&prologue);
            }
            inh
        } else {
            SymStack::from_template(&self.templates[block], self.ctx.has_internal_return)
        };

        let state = BlockSimState::new(block, stack, free_slots, prologue, uses);
        let state = BlockPlanner::new(self, state).run();

        // The block walk injects the prologue on every non-phi instruction (including the
        // terminator that every block has), so a non-empty prologue is always injected.
        debug_assert!(
            state.prologue.is_empty() || state.injected_prologue,
            "prologue was not injected during the block walk"
        );
    }

    fn resolve_pending_edges(&mut self, block: BlockId) {
        let Some(mut edges) = self.pending_edges.remove(&block) else {
            return;
        };
        debug_assert!(
            !self.inherited_stack.contains_key(&block),
            "pending merge edges cannot also inherit one stack"
        );
        debug_assert!(
            !self.planned_blocks.contains(block),
            "pending edge target already planned"
        );

        let projected: Vec<(BlockId, TransferOrder)> = edges
            .iter()
            .map(|edge| {
                (
                    edge.pred,
                    project_transfer(&edge.stack, &self.carry_in[block]),
                )
            })
            .collect();
        if !projected.is_empty() {
            self.freeze_template(block, choose_transfer(self.ctx, block, &projected));
        }

        let tmpl = self.templates[block].clone();
        for edge in edges.iter_mut() {
            debug_assert_eq!(
                self.alloc.pre_actions[edge.inst].len(),
                edge.action_start,
                "deferred edge action list changed before resolution"
            );
            self.with_planner(
                &mut edge.stack,
                &mut edge.free_slots,
                PlannerActionSink::Pre(edge.inst),
                |planner| planner.plan_edge_fixup_to_template(&tmpl, edge.pred, block),
            );
            self.observer.on_deferred_exit_actions(
                edge.trace_token,
                &self.alloc.pre_actions[edge.inst][edge.action_start..],
            );
        }
    }

    fn freeze_template_from_stack(&mut self, block: BlockId, stack: &SymStack) {
        self.freeze_template(block, project_transfer(stack, &self.carry_in[block]));
    }

    fn freeze_template_canonical(&mut self, block: BlockId) {
        let transfer = canonical_transfer_order(
            &self.carry_in[block],
            &self.ctx.dom_depth,
            &self.ctx.def_info,
        );
        self.freeze_template(block, transfer);
    }

    fn freeze_template(&mut self, block: BlockId, transfer: TransferOrder) {
        self.templates[block].freeze_transfer(transfer);
    }

    pub(super) fn ctx(&self) -> &StackifyContext<'ctx> {
        self.ctx
    }

    pub(super) fn scratch_slots(&self) -> &SlotPool {
        &self.mem.slots.scratch
    }

    pub(super) fn debug_assert_inst_actions_empty(&self, inst: InstId) {
        // Within one fixed-point iteration each inst is visited once on a fresh `StackifyAlloc`,
        // so its action buffers are always still empty when the walk reaches it.
        debug_assert!(
            self.alloc.pre_actions[inst].is_empty()
                && self.alloc.post_actions[inst].is_empty()
                && self.alloc.brtable_actions[inst].is_empty(),
            "inst action buffers are not empty at the start of the block walk"
        );
    }

    pub(super) fn pre_actions_len(&self, inst: InstId) -> usize {
        self.alloc.pre_actions[inst].len()
    }

    pub(super) fn with_pre_actions<R>(
        &mut self,
        inst: InstId,
        f: impl FnOnce(&mut Actions) -> R,
    ) -> R {
        f(&mut self.alloc.pre_actions[inst])
    }

    pub(super) fn with_planner<R>(
        &mut self,
        stack: &mut SymStack,
        free_slots: &mut FreeSlotPools,
        sink: PlannerActionSink,
        f: impl FnOnce(&mut Planner<'_, '_>) -> R,
    ) -> R {
        // Resolve the action buffer first: `Pre`/`Post` index into `alloc` (a field disjoint from
        // `alloc.exact_local_addr`, which `MemPlan` borrows), while `BrTableCase` accumulates into
        // a local buffer pushed onto `brtable_actions` after planning. Then construct the
        // `MemPlan`/`Planner` once for all three.
        let mut brtable_buf = Actions::new();
        let actions: &mut Actions = match sink {
            PlannerActionSink::Pre(inst) => &mut self.alloc.pre_actions[inst],
            PlannerActionSink::Post(inst) => &mut self.alloc.post_actions[inst],
            PlannerActionSink::BrTableCase { .. } => &mut brtable_buf,
        };
        let mem = planner::MemPlan::new(
            &mut self.mem,
            self.ctx,
            &self.alloc.exact_local_addr,
            free_slots,
        );
        let result = {
            let mut planner =
                Planner::new(self.ctx, stack, actions, mem, &mut *self.search_scratch);
            f(&mut planner)
        };
        if let PlannerActionSink::BrTableCase { inst, case_idx } = sink {
            debug_assert_eq!(self.alloc.brtable_actions[inst].len(), case_idx);
            self.alloc.brtable_actions[inst].push(brtable_buf);
        }
        result
    }

    pub(super) fn observer(&mut self) -> &mut O {
        &mut *self.observer
    }

    /// Split borrow of the observer and the (read-only) allocation, so the block walk can emit an
    /// action-group trace event over a slice of `alloc` while notifying the observer.
    pub(super) fn trace_actions(&mut self) -> (&mut O, &StackifyAlloc) {
        (&mut *self.observer, &*self.alloc)
    }

    /// Record a `jump` edge to `dest`, applying immediate normalization / inheritance / pending
    /// deferral as appropriate. Returns `true` when the edge was deferred (a pending merge edge):
    /// its exit + jump trace has already been emitted here (synchronously with capturing the
    /// deferred trace token), so the caller emits nothing further. Returns `false` for a resolved
    /// edge, so the caller emits the exit-normalization actions and the jump trace.
    pub(super) fn record_jump_edge(
        &mut self,
        state: &mut BlockSimState,
        inst: InstId,
        dest: BlockId,
        action_start: usize,
    ) -> bool {
        if self.terminal_chain_blocks.contains(dest) {
        } else if self.ctx.cfg.pred_num_of(dest) > 1
            && dest != self.ctx.entry
            && !self.planned_blocks.contains(dest)
        {
            debug_assert!(
                self.ctx.scc.is_reachable(dest),
                "pending edge target must be reachable"
            );
            self.pending_edges
                .entry(dest)
                .or_default()
                .push(PendingEdge {
                    pred: state.block,
                    inst,
                    stack: state.stack.clone(),
                    free_slots: state.free_slots.clone(),
                    action_start,
                    trace_token: self.observer.on_deferred_inst_jump(inst, dest),
                });
            return true;
        } else if self.ctx.cfg.pred_num_of(dest) == 1
            && dest != self.ctx.entry
            && !self.planned_blocks.contains(dest)
        {
            self.inherited_stack
                .entry(dest)
                .or_insert_with(|| (state.block, state.stack.clone()));
        } else {
            let tmpl = self.templates[dest].clone();
            let src = state.block;
            self.with_planner(
                &mut state.stack,
                &mut state.free_slots,
                PlannerActionSink::Pre(inst),
                |planner| planner.plan_edge_fixup_to_template(&tmpl, src, dest),
            );
        }
        false
    }

    pub(super) fn record_branch_edge(
        &mut self,
        state: &mut BlockSimState,
        succ: BlockId,
        stack: SymStack,
    ) {
        assert!(
            !self.planned_blocks.contains(succ),
            "multiway branch edge to already-planned block {succ:?}: run StackifyEdgeSplitter \
             before stackify to split in-cycle multiway edges"
        );
        debug_assert_eq!(
            self.ctx.cfg.pred_num_of(succ),
            1,
            "no critical edges: branch target must be single-pred"
        );
        self.inherited_stack
            .entry(succ)
            .or_insert_with(|| (state.block, stack));
    }

    pub(super) fn record_br_table_edge(
        &mut self,
        state: &mut BlockSimState,
        succ: BlockId,
        stack: SymStack,
    ) {
        assert!(
            !self.planned_blocks.contains(succ),
            "multiway br_table edge to already-planned block {succ:?}: run StackifyEdgeSplitter \
             before stackify to split in-cycle multiway edges"
        );
        debug_assert_eq!(
            self.ctx.cfg.pred_num_of(succ),
            1,
            "no critical edges: br_table target must be single-pred"
        );
        self.inherited_stack
            .entry(succ)
            .or_insert_with(|| (state.block, stack));
    }
}
