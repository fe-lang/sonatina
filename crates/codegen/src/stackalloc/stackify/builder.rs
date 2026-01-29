use cranelift_entity::{EntityRef, SecondaryMap};
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, ValueId, cfg::ControlFlowGraph};
use std::collections::BTreeMap;

use crate::{bitset::BitSet, cfg_scc::CfgSccAnalysis, domtree::DomTree, liveness::Liveness};

use super::{
    alloc::StackifyAlloc,
    flow_templates::solve_templates_from_flow,
    iteration::IterationPlanner,
    slots::{FreeSlotPools, SpillSlotPools},
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
    scratch_live_values_override: Option<BitSet<ValueId>>,
    scratch_spill_slots: u32,
}

pub(super) struct StackifyContext<'a> {
    pub(super) func: &'a Function,
    pub(super) cfg: &'a ControlFlowGraph,
    pub(super) dom: &'a DomTree,
    pub(super) liveness: &'a Liveness,
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
            scratch_live_values_override: None,
            scratch_spill_slots: 0,
        }
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
        let mut spill_set: BitSet<ValueId> = BitSet::default();
        let mut slots: SpillSlotPools = SpillSlotPools::default();

        loop {
            let checkpoint = observer.checkpoint();

            let (mut alloc, spill_requests) =
                Self::plan_iteration(&ctx, observer, SpillSet::new(&spill_set), &mut slots);

            if spill_requests.is_subset(&spill_set) {
                alloc.scratch_slot_of_value = slots.scratch.take_slot_map();
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
        let mut arg_free_slots: FreeSlotPools = FreeSlotPools::default();
        for &arg in ctx.func.arg_values.iter() {
            if let Some(spilled) = spill.spilled(arg) {
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
            }
        }

        let spill_obj = assign_spill_obj_ids(ctx.func, spill);

        // Template solving may encounter temporary unreachable values while iterating toward a
        // fixed point, but those requests are not necessarily required under the final chosen
        // templates. Treat spill discovery as the responsibility of the final planning pass.
        let mut solver_spill_requests: BitSet<ValueId> = BitSet::default();
        let templates =
            solve_templates_from_flow(ctx, spill, &spill_obj, &mut solver_spill_requests);

        let mut alloc = StackifyAlloc {
            pre_actions: SecondaryMap::new(),
            post_actions: SecondaryMap::new(),
            brtable_actions: BTreeMap::new(),
            spill_obj,
            scratch_slot_of_value: SecondaryMap::new(),
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

fn assign_spill_obj_ids(
    func: &Function,
    spill: SpillSet<'_>,
) -> SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>> {
    let mut map: SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>> =
        SecondaryMap::new();
    for v in func.dfg.values.keys() {
        let _ = &mut map[v];
    }

    let mut spilled: Vec<ValueId> = spill.bitset().iter().collect();
    spilled.sort_unstable_by_key(|v| v.as_u32());

    for (idx, v) in spilled.into_iter().enumerate() {
        map[v] = Some(crate::isa::evm::static_arena_alloc::StackObjId::new(idx));
    }
    map
}
