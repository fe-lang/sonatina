use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, InstId, ValueId};

use crate::{bitset::BitSet, stackalloc::Actions};

use super::{
    alloc::StackifyAlloc,
    block::{BlockPlanner, BlockSimState, PlannerActionSink},
    builder::StackifyContext,
    entry::{DeferredEdge, EdgeDisposition, EntryTable, RecordEdge, ResolvedEntry},
    planner::{self, MemState, NormalizeSearchScratch, Planner},
    slots::{FreeSlotPools, SlotPool},
    sym_stack::SymStack,
    trace::StackifyObserver,
    uses::UseTracker,
};

pub(super) struct FunctionPlanner<'a, 'ctx, O: StackifyObserver> {
    ctx: &'a StackifyContext<'ctx>,
    /// Memory-planning state (spill set, provisional object ids, spill/object requests, slot
    /// pools) handed to each `MemPlan` in one reborrow.
    mem: MemState<'a>,
    carry_in: &'a SecondaryMap<BlockId, BitSet<ValueId>>,
    alloc: &'a mut StackifyAlloc,
    /// The block-entry state machine: classification + `Pending -> Frozen` lifecycle, owning the
    /// frozen templates. Replaces the old `templates` / `inherited_stack` / `pending_edges` /
    /// `planned_blocks` / `terminal_chain_blocks` tables.
    entries: EntryTable,
    search_scratch: &'a mut NormalizeSearchScratch,
    observer: &'a mut O,
}

impl<'a, 'ctx, O: StackifyObserver> FunctionPlanner<'a, 'ctx, O> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        ctx: &'a StackifyContext<'ctx>,
        mem: MemState<'a>,
        carry_in: &'a SecondaryMap<BlockId, BitSet<ValueId>>,
        alloc: &'a mut StackifyAlloc,
        entries: EntryTable,
        search_scratch: &'a mut NormalizeSearchScratch,
        observer: &'a mut O,
    ) -> Self {
        Self {
            ctx,
            mem,
            carry_in,
            alloc,
            entries,
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

        self.entries.debug_assert_no_pending_edges();
    }

    fn plan_block(&mut self, block: BlockId) {
        let mut free_slots: FreeSlotPools = FreeSlotPools::default();

        let uses = UseTracker::for_block(self.ctx, block);
        let (stack, prologue) = self.resolve_entry(block, &uses, &mut free_slots);

        let state = BlockSimState::new(block, stack, free_slots, prologue, uses);
        let state = BlockPlanner::new(self, state).run();

        // The block walk injects the prologue on every non-phi instruction (including the
        // terminator that every block has), so a non-empty prologue is always injected.
        debug_assert!(
            state.prologue.is_empty() || state.injected_prologue,
            "prologue was not injected during the block walk"
        );
    }

    /// Resolve `block`'s entry: freeze its template (via the entry table's single transfer-selection
    /// point), plan the entry-specific fixups, and return the initial stack plus any prologue
    /// actions. This subsumes the old `resolve_pending_edges` + the template/stack selection that
    /// used to be inlined in `plan_block`.
    fn resolve_entry(
        &mut self,
        block: BlockId,
        uses: &UseTracker,
        free_slots: &mut FreeSlotPools,
    ) -> (SymStack, Actions) {
        let mut prologue = Actions::new();
        let resolved = self
            .entries
            .freeze_entry(self.ctx, &self.carry_in[block], block);

        // Merge templates fix up their deferred edges *before* the block header fires, reproducing
        // the old `resolve_pending_edges` ordering (deferred exit actions are traced ahead of
        // `on_block_header`).
        if let ResolvedEntry::Merge { deferred } = resolved {
            self.plan_deferred_edges(block, deferred);
            self.emit_block_header(block);
            let stack =
                SymStack::from_template(self.entries.template(block), self.ctx.has_internal_return);
            return (stack, prologue);
        }

        self.emit_block_header(block);

        let stack = match resolved {
            ResolvedEntry::Merge { .. } => unreachable!("merge resolved above"),
            ResolvedEntry::Opaque => SymStack::opaque_prefix_empty(self.ctx.has_internal_return),
            ResolvedEntry::Fallback => {
                SymStack::from_template(self.entries.template(block), self.ctx.has_internal_return)
            }
            ResolvedEntry::Entry { stack } => stack,
            ResolvedEntry::Inherited {
                pred,
                stack: mut inh,
            } => {
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

                // Single-predecessor blocks without phis do not need exact entry template
                // normalization. Keeping the inherited stack avoids pointless bottom reshuffling
                // that can cascade into SWAP/POP churn.
                if !self.ctx.phi_results[block].is_empty() {
                    let tmpl = self.entries.template(block).clone();
                    self.with_actions_planner(&mut inh, &mut prologue, free_slots, |planner| {
                        planner.plan_edge_fixup_to_template(&tmpl, pred, block);
                    });
                }
                self.observer.on_block_prologue(&prologue);
                inh
            }
        };

        (stack, prologue)
    }

    /// Fix each deferred merge edge up to the now-frozen template, in arrival order, backfilling the
    /// observer's deferred-exit trace. Mirrors the old `resolve_pending_edges` fixup loop.
    fn plan_deferred_edges(&mut self, block: BlockId, mut deferred: Vec<DeferredEdge>) {
        let tmpl = self.entries.template(block).clone();
        for edge in deferred.iter_mut() {
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

    fn emit_block_header(&mut self, block: BlockId) {
        self.observer
            .on_block_header(self.ctx.func, block, self.entries.template(block));
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

    /// Record a `jump` edge to `dest`. Returns `true` when the edge was deferred (a pending merge
    /// edge): its exit + jump trace has already been emitted synchronously with capturing the
    /// deferred trace token, so the caller emits nothing further. Returns `false` for an opaque,
    /// inherited, or fixed-up-now edge, so the caller emits the exit-normalization actions and the
    /// jump trace.
    pub(super) fn record_jump_edge(
        &mut self,
        state: &mut BlockSimState,
        inst: InstId,
        dest: BlockId,
        action_start: usize,
    ) -> bool {
        let disposition = self.entries.record_edge(
            self.ctx,
            self.observer,
            RecordEdge::Jump {
                inst,
                free_slots: &state.free_slots,
                action_start,
            },
            state.block,
            dest,
            &state.stack,
        );
        match disposition {
            EdgeDisposition::Deferred => true,
            EdgeDisposition::Recorded => false,
            EdgeDisposition::FixupNow(tmpl) => {
                let src = state.block;
                self.with_planner(
                    &mut state.stack,
                    &mut state.free_slots,
                    PlannerActionSink::Pre(inst),
                    |planner| planner.plan_edge_fixup_to_template(&tmpl, src, dest),
                );
                false
            }
        }
    }

    pub(super) fn record_branch_edge(
        &mut self,
        state: &mut BlockSimState,
        succ: BlockId,
        stack: &SymStack,
    ) {
        self.entries.record_edge(
            self.ctx,
            self.observer,
            RecordEdge::Multiway { label: "branch" },
            state.block,
            succ,
            stack,
        );
    }

    pub(super) fn record_br_table_edge(
        &mut self,
        state: &mut BlockSimState,
        succ: BlockId,
        stack: &SymStack,
    ) {
        self.entries.record_edge(
            self.ctx,
            self.observer,
            RecordEdge::Multiway { label: "br_table" },
            state.block,
            succ,
            stack,
        );
    }
}
