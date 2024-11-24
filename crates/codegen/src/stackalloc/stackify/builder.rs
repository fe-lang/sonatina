use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{cfg::ControlFlowGraph, BlockId, Function, ValueId};
use std::collections::BTreeMap;

use crate::{bitset::BitSet, domtree::DomTree, liveness::Liveness};

use super::{
    alloc::StackifyAlloc,
    iteration::IterationPlanner,
    slots::{FreeSlots, SlotState},
    spill::SpillSet,
    sym_stack::SymStack,
    templates::{
        compute_def_info, compute_dom_depth, compute_phi_out_sources, compute_phi_results,
        compute_templates, function_has_internal_return, DefInfo,
    },
    trace::{NullObserver, StackifyObserver},
};

pub(super) struct StackifyBuilder<'a> {
    func: &'a Function,
    cfg: &'a ControlFlowGraph,
    dom: &'a DomTree,
    liveness: &'a Liveness,
}

pub(super) struct StackifyContext<'a> {
    pub(super) func: &'a Function,
    pub(super) cfg: &'a ControlFlowGraph,
    pub(super) dom: &'a DomTree,
    pub(super) liveness: &'a Liveness,
    pub(super) entry: BlockId,
    pub(super) dom_depth: SecondaryMap<BlockId, u32>,
    pub(super) def_info: SecondaryMap<ValueId, Option<DefInfo>>,
    pub(super) phi_results: SecondaryMap<BlockId, SmallVec<[ValueId; 4]>>,
    pub(super) phi_out_sources: SecondaryMap<BlockId, BitSet<ValueId>>,
    pub(super) has_internal_return: bool,
}

impl<'a> StackifyBuilder<'a> {
    pub(super) fn new(
        func: &'a Function,
        cfg: &'a ControlFlowGraph,
        dom: &'a DomTree,
        liveness: &'a Liveness,
    ) -> Self {
        Self {
            func,
            cfg,
            dom,
            liveness,
        }
    }

    pub(super) fn compute(self) -> StackifyAlloc {
        let mut observer = NullObserver;
        self.compute_with_observer(&mut observer)
    }

    pub(super) fn compute_with_observer<O: StackifyObserver>(
        self,
        observer: &mut O,
    ) -> StackifyAlloc {
        let entry = match self.cfg.entry() {
            Some(b) => b,
            None => return StackifyAlloc::default(),
        };

        let ctx = StackifyContext {
            func: self.func,
            cfg: self.cfg,
            dom: self.dom,
            liveness: self.liveness,
            entry,
            dom_depth: compute_dom_depth(self.dom, entry),
            def_info: compute_def_info(self.func, entry),
            phi_results: compute_phi_results(self.func),
            phi_out_sources: compute_phi_out_sources(self.func, self.cfg),
            // Internal-return functions expect a caller-provided return address below their args.
            has_internal_return: function_has_internal_return(self.func),
        };

        // `spill_set` is discovered via a monotone fixed point:
        // - planning may demand a `MemLoadFrameSlot(v)` when `v` is unreachable by `DUP16`
        // - or when a flush/rebuild needs to reconstruct a stack template
        // In that case we add `v` to `spill_requests`, discard this iteration's plan, and retry.
        //
        // Once `v ∈ spill_set`, we emit a dominating store at its definition (or phi entry) and
        // remove it from transfer regions (`T(B)` excludes `spill_set`), so future iterations
        // can rely on loads being correct.
        let mut spill_set: BitSet<ValueId> = BitSet::default();
        let mut slots: SlotState = SlotState::default();

        loop {
            let checkpoint = observer.checkpoint();

            let (mut alloc, spill_requests) =
                Self::plan_iteration(&ctx, observer, SpillSet::new(&spill_set), &mut slots);

            if spill_requests.is_subset(&spill_set) {
                alloc.frame_size_slots = slots.frame_size_slots();
                alloc.slot_of = slots.take_slot_map();
                return alloc;
            }

            observer.rollback(checkpoint);
            spill_set.union_with(&spill_requests);
        }
    }

    fn plan_iteration<O: StackifyObserver>(
        ctx: &StackifyContext<'_>,
        observer: &mut O,
        spill: SpillSet<'_>,
        slots: &mut SlotState,
    ) -> (StackifyAlloc, BitSet<ValueId>) {
        // Function arguments that are in `spill_set` must have a stable slot from function entry.
        // We allocate these up-front (fresh; no reuse possible before entry).
        let mut arg_free_slots: FreeSlots = FreeSlots::default();
        for &arg in ctx.func.arg_values.iter() {
            if let Some(spilled) = spill.spilled(arg) {
                let _ = slots.ensure_slot(spilled, ctx.liveness, &mut arg_free_slots);
            }
        }

        let templates = compute_templates(ctx, spill);

        let mut alloc = StackifyAlloc {
            pre_actions: SecondaryMap::new(),
            post_actions: SecondaryMap::new(),
            brtable_actions: BTreeMap::new(),
            slot_of: SecondaryMap::new(),
            frame_size_slots: 0,
        };

        let mut spill_requests: BitSet<ValueId> = BitSet::default();

        // Blocks that are reached from multi-way branches inherit a dynamic stack and
        // run an entry normalization prologue (single-pred only; critical edges split).
        let mut inherited_stack: BTreeMap<BlockId, (BlockId, SymStack)> = BTreeMap::new();
        inherited_stack.insert(
            ctx.entry,
            (
                ctx.entry,
                SymStack::entry_stack(ctx.func, ctx.has_internal_return),
            ),
        );

        let mut planner = IterationPlanner::new(
            ctx,
            spill,
            slots,
            &templates,
            &mut alloc,
            &mut spill_requests,
            inherited_stack,
            observer,
        );
        planner.plan_blocks();

        (alloc, spill_requests)
    }
}
