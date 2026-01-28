use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, ValueId, cfg::ControlFlowGraph};
use std::collections::BTreeMap;

use crate::{
    bitset::BitSet,
    cfg_scc::CfgSccAnalysis,
    domtree::DomTree,
    liveness::{InstLiveness, Liveness},
    stackalloc::SpillSlotRef,
};

use super::{
    alloc::StackifyAlloc,
    flow_templates::solve_templates_from_flow,
    iteration::IterationPlanner,
    slots::{FreeSlotPools, SpillSlotPools, TRANSIENT_SLOT_TAG},
    spill::SpillSet,
    sym_stack::SymStack,
    templates::{
        DefInfo, compute_def_info, compute_dom_depth, compute_phi_out_sources, compute_phi_results,
        function_has_internal_return,
    },
    trace::{NullObserver, StackifyObserver},
};

#[derive(Clone, Copy, Debug)]
pub(super) struct StackifyReachability {
    pub(super) dup_max: usize,
    pub(super) swap_max: usize,
}

impl StackifyReachability {
    pub(super) fn new(reach_depth: u8) -> Self {
        assert!(
            (1..=super::DUP_MAX as u8).contains(&reach_depth),
            "stackify reach_depth must be in 1..={}",
            super::DUP_MAX
        );

        let dup_max = reach_depth as usize;
        let swap_max = (dup_max + 1).min(super::SWAP_MAX);

        Self { dup_max, swap_max }
    }
}

pub(super) struct StackifyBuilder<'a> {
    func: &'a Function,
    cfg: &'a ControlFlowGraph,
    dom: &'a DomTree,
    liveness: &'a Liveness,
    reach: StackifyReachability,
    values_live_across_calls_override: Option<BitSet<ValueId>>,
    values_persistent_across_calls_override: Option<BitSet<ValueId>>,
    scratch_live_values_override: Option<BitSet<ValueId>>,
    scratch_spill_slots: u32,
}

pub(super) struct StackifyContext<'a> {
    pub(super) func: &'a Function,
    pub(super) cfg: &'a ControlFlowGraph,
    pub(super) dom: &'a DomTree,
    pub(super) liveness: &'a Liveness,
    pub(super) values_live_across_calls: BitSet<ValueId>,
    pub(super) values_persistent_across_calls: BitSet<ValueId>,
    pub(super) scratch_live_values: BitSet<ValueId>,
    pub(super) scratch_spill_slots: u32,
    pub(super) entry: BlockId,
    pub(super) scc: CfgSccAnalysis,
    pub(super) dom_depth: SecondaryMap<BlockId, u32>,
    pub(super) def_info: SecondaryMap<ValueId, Option<DefInfo>>,
    pub(super) phi_results: SecondaryMap<BlockId, SmallVec<[ValueId; 4]>>,
    pub(super) phi_out_sources: SecondaryMap<BlockId, BitSet<ValueId>>,
    pub(super) has_internal_return: bool,
    pub(super) reach: StackifyReachability,
}

impl<'a> StackifyBuilder<'a> {
    pub(super) fn new(
        func: &'a Function,
        cfg: &'a ControlFlowGraph,
        dom: &'a DomTree,
        liveness: &'a Liveness,
        reach_depth: u8,
    ) -> Self {
        Self {
            func,
            cfg,
            dom,
            liveness,
            reach: StackifyReachability::new(reach_depth),
            values_live_across_calls_override: None,
            values_persistent_across_calls_override: None,
            scratch_live_values_override: None,
            scratch_spill_slots: 0,
        }
    }

    pub(super) fn with_values_live_across_calls(
        mut self,
        values_live_across_calls: BitSet<ValueId>,
    ) -> Self {
        self.values_live_across_calls_override = Some(values_live_across_calls);
        self
    }

    pub(super) fn with_values_persistent_across_calls(
        mut self,
        values_persistent_across_calls: BitSet<ValueId>,
    ) -> Self {
        self.values_persistent_across_calls_override = Some(values_persistent_across_calls);
        self
    }

    pub(super) fn with_scratch_live_values(mut self, scratch_live_values: BitSet<ValueId>) -> Self {
        self.scratch_live_values_override = Some(scratch_live_values);
        self
    }

    pub(super) fn with_scratch_spills(mut self, scratch_spill_slots: u32) -> Self {
        self.scratch_spill_slots = scratch_spill_slots;
        self
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

        let mut scc = CfgSccAnalysis::new();
        scc.compute(self.cfg);

        let values_live_across_calls =
            if let Some(values) = self.values_live_across_calls_override {
                values
            } else {
                let mut inst_liveness = InstLiveness::default();
                inst_liveness.compute(self.func, self.cfg, self.liveness);
                inst_liveness.call_live_values(self.func)
            };

        let values_persistent_across_calls = if let Some(values) =
            self.values_persistent_across_calls_override
        {
            values
        } else {
            values_live_across_calls.clone()
        };

        let scratch_live_values = if self.scratch_spill_slots == 0 {
            BitSet::default()
        } else if let Some(scratch_live_values) = self.scratch_live_values_override {
            scratch_live_values
        } else {
            let mut scratch_live_values = BitSet::default();
            for value in self.func.dfg.values.keys() {
                scratch_live_values.insert(value);
            }
            scratch_live_values
        };

        let ctx = StackifyContext {
            func: self.func,
            cfg: self.cfg,
            dom: self.dom,
            liveness: self.liveness,
            values_live_across_calls,
            values_persistent_across_calls,
            scratch_live_values,
            scratch_spill_slots: self.scratch_spill_slots,
            entry,
            scc,
            dom_depth: compute_dom_depth(self.dom, entry),
            def_info: compute_def_info(self.func, entry),
            phi_results: compute_phi_results(self.func),
            phi_out_sources: compute_phi_out_sources(self.func, self.cfg),
            // Internal-return functions expect a caller-provided return address below their args.
            has_internal_return: function_has_internal_return(self.func),
            reach: self.reach,
        };

        // `spill_set` is discovered via a monotone fixed point:
        // - planning may demand a `MemLoadFrameSlot(v)` when `v` is unreachable by `DUP16`
        // - or when a flush/rebuild needs to reconstruct a stack template
        // In that case we add `v` to `spill_requests`, discard this iteration's plan, and retry.
        //
        // Once `v ∈ spill_set`, we emit a dominating store at its definition (or phi entry) and
        // remove it from transfer regions (`T(B)` excludes `spill_set`), so future iterations
        // can rely on loads being correct.
        //
        // Seed with values live across calls to manage stack depth. During call preparation,
        // the stack holds transfer_values + CallRetAddr + args. If call-live values remain in
        // the transfer region, this can exceed DUP16/SWAP16 reach (16-17 items), making values
        // unreachable for the planner. Spilling them to memory keeps stack depth manageable.
        let mut spill_set: BitSet<ValueId> = ctx.values_live_across_calls.clone();
        let mut slots: SpillSlotPools = SpillSlotPools::default();

        loop {
            let checkpoint = observer.checkpoint();

            let (mut alloc, spill_requests) =
                Self::plan_iteration(&ctx, observer, SpillSet::new(&spill_set), &mut slots);

            if spill_requests.is_subset(&spill_set) {
                let persistent_frame_slots = slots.persistent.frame_size_slots();
                let transient_frame_slots = slots.transient.frame_size_slots();

                lower_encoded_frame_slots(&mut alloc, persistent_frame_slots);

                alloc.persistent_frame_slots = persistent_frame_slots;
                alloc.transient_frame_slots = transient_frame_slots;

                alloc.slot_of_value = merge_slot_maps(
                    slots.persistent.take_slot_map(),
                    slots.transient.take_slot_map(),
                    slots.scratch.take_slot_map(),
                );
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
        slots: &mut SpillSlotPools,
    ) -> (StackifyAlloc, BitSet<ValueId>) {
        // Function arguments that are in `spill_set` must have a stable slot from function entry.
        // We allocate these up-front (fresh; no reuse possible before entry).
        let mut arg_free_slots: FreeSlotPools = FreeSlotPools::default();
        for &arg in ctx.func.arg_values.iter() {
            if let Some(spilled) = spill.spilled(arg) {
                if ctx.values_persistent_across_calls.contains(arg) {
                    let _ = slots.persistent.ensure_slot(
                        spilled,
                        ctx.liveness,
                        &mut arg_free_slots.persistent,
                    );
                    continue;
                }

                if ctx.scratch_spill_slots != 0
                    && !ctx.scratch_live_values.contains(arg)
                    && slots
                        .scratch
                        .try_ensure_slot(
                            spilled,
                            ctx.liveness,
                            &mut arg_free_slots.scratch,
                            Some(ctx.scratch_spill_slots),
                        )
                        .is_some()
                {
                    continue;
                }

                let _ = slots.transient.ensure_slot(
                    spilled,
                    ctx.liveness,
                    &mut arg_free_slots.transient,
                );
            }
        }

        // Template solving may encounter temporary unreachable values while iterating toward a
        // fixed point, but those requests are not necessarily required under the final chosen
        // templates. Treat spill discovery as the responsibility of the final planning pass.
        let mut solver_spill_requests: BitSet<ValueId> = BitSet::default();
        let templates = solve_templates_from_flow(ctx, spill, &mut solver_spill_requests);

        let mut alloc = StackifyAlloc {
            pre_actions: SecondaryMap::new(),
            post_actions: SecondaryMap::new(),
            brtable_actions: BTreeMap::new(),
            slot_of_value: SecondaryMap::new(),
            persistent_frame_slots: 0,
            transient_frame_slots: 0,
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

fn merge_slot_maps(
    persistent: SecondaryMap<ValueId, Option<u32>>,
    transient: SecondaryMap<ValueId, Option<u32>>,
    scratch: SecondaryMap<ValueId, Option<u32>>,
) -> SecondaryMap<ValueId, Option<SpillSlotRef>> {
    let mut out: SecondaryMap<ValueId, Option<SpillSlotRef>> = SecondaryMap::new();

    for (v, slot) in persistent.iter() {
        if let Some(slot) = *slot {
            debug_assert!(out[v].is_none(), "spill slot already assigned");
            out[v] = Some(SpillSlotRef::Persistent(slot));
        }
    }
    for (v, slot) in transient.iter() {
        if let Some(slot) = *slot {
            debug_assert!(out[v].is_none(), "spill slot already assigned");
            out[v] = Some(SpillSlotRef::Transient(slot));
        }
    }
    for (v, slot) in scratch.iter() {
        if let Some(slot) = *slot {
            debug_assert!(out[v].is_none(), "spill slot already assigned");
            out[v] = Some(SpillSlotRef::Scratch(slot));
        }
    }

    out
}

fn lower_encoded_frame_slots(alloc: &mut StackifyAlloc, persistent_frame_slots: u32) {
    fn lower_actions(actions: &mut crate::stackalloc::Actions, persistent_frame_slots: u32) {
        for action in actions.iter_mut() {
            match action {
                crate::stackalloc::Action::MemLoadFrameSlot(slot)
                | crate::stackalloc::Action::MemStoreFrameSlot(slot) => {
                    if *slot & TRANSIENT_SLOT_TAG != 0 {
                        let local = *slot & !TRANSIENT_SLOT_TAG;
                        *slot = persistent_frame_slots
                            .checked_add(local)
                            .expect("frame slot offset overflow");
                    }
                }
                _ => {}
            }
        }
    }

    for (_, actions) in alloc.pre_actions.iter_mut() {
        lower_actions(actions, persistent_frame_slots);
    }
    for (_, actions) in alloc.post_actions.iter_mut() {
        lower_actions(actions, persistent_frame_slots);
    }
    for actions in alloc.brtable_actions.values_mut() {
        lower_actions(actions, persistent_frame_slots);
    }
}
