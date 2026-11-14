use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{Module, ValueId, cfg::ControlFlowGraph, module::FuncRef};
use std::sync::Mutex;
use tracing::{debug_span, trace_span};

use crate::{
    bitset::BitSet,
    domtree::DomTree,
    liveness::{InstLiveness, Liveness},
    module_analysis::CallGraphSchedule,
    stackalloc::{
        HOT_IMMEDIATE_SIZE_MIN_BLOCK_USES, HOT_IMMEDIATE_SIZE_MIN_MATERIALIZATION_BYTES,
        StackifyBuilder, StackifyEdgeSplitter, StackifySearchCache,
    },
};

use super::{
    super::{
        EvmBackend, ImmediateMaterializationMode,
        fixed_slots::{FixedSlotConflicts, FixedSlotSummaries, SlotBytes},
        memory_plan::MachineStackifyAnalysis,
    },
    placement::EvmMemoryPlacementPlan,
    verify::verify_machine_function,
};

const SECTION_SEARCH_PLAN_CACHE_CAP: usize = 16_384;

/// Search caches waiting for the next placement iteration. Active allocations
/// own their caches, so only completed functions count toward this section budget.
#[derive(Default)]
pub(crate) struct SectionStackifySearchCaches {
    caches: FxHashMap<FuncRef, StackifySearchCache>,
    retained_plans: usize,
    exhausted: bool,
}

impl SectionStackifySearchCaches {
    fn take(&mut self, func: FuncRef) -> StackifySearchCache {
        let cache = self.caches.remove(&func).unwrap_or_default();
        self.retained_plans -= cache.plan_count();
        cache
    }

    fn retain(&mut self, func: FuncRef, cache: StackifySearchCache) {
        let plans = cache.plan_count();
        if self.exhausted || plans == 0 {
            return;
        }
        // Fall back to fresh caches for an oversized section, releasing every
        // retained map and eviction queue. Keeping only some functions warm can
        // give identical functions different stack plans and prevent block merging.
        if self.retained_plans + plans > SECTION_SEARCH_PLAN_CACHE_CAP {
            *self = Self {
                exhausted: true,
                ..Self::default()
            };
            return;
        }
        self.retained_plans += plans;
        let previous = self.caches.insert(func, cache);
        debug_assert!(previous.is_none());
    }
}

/// `allocation_addrs` holds each function's machine values that name an
/// allocation on every path.
pub(crate) fn prepare_machine_stackify_analyses(
    module: &Module,
    schedule: &CallGraphSchedule,
    backend: &EvmBackend,
    placement: &EvmMemoryPlacementPlan,
    allocation_addrs: &FxHashMap<FuncRef, BitSet<ValueId>>,
    search_caches: &Mutex<SectionStackifySearchCaches>,
) -> Result<FxHashMap<FuncRef, MachineStackifyAnalysis>, String> {
    let _span = debug_span!("sonatina.codegen.evm.machine.prepare_stackify").entered();
    let fixed_slots =
        FixedSlotSummaries::compute(module, schedule, placement.arena_base, allocation_addrs);

    let mut analyses = FxHashMap::default();
    // The fixed-slot bytes a call to each analyzed function may write.
    let mut slot_writes: FxHashMap<FuncRef, SlotBytes> = FxHashMap::default();
    let mut scratch_arena_effects = FxHashSet::default();
    for &scc_ref in schedule.topo.iter().rev() {
        let components = schedule.members(scc_ref);

        let cycle_scratch_arena_effects = schedule.sccs.scc_info(scc_ref).is_cycle.then(|| {
            let mut effects = scratch_arena_effects.clone();
            effects.extend(components.iter().copied());
            effects
        });
        let analysis_scratch_arena_effects = cycle_scratch_arena_effects
            .as_ref()
            .unwrap_or(&scratch_arena_effects);

        let mut scc_results = sonatina_ir::parallel::map(&module.func_store, components, |&func| {
            let mut search_cache = search_caches.lock().unwrap().take(func);
            let analysis = module.func_store.modify(func, |function| {
                prepare_machine_stackify_analysis(
                    function,
                    func,
                    backend,
                    &fixed_slots,
                    &slot_writes,
                    analysis_scratch_arena_effects,
                    &mut search_cache,
                )
            });
            search_caches.lock().unwrap().retain(func, search_cache);
            let analysis = analysis?;
            let local_slot_writes = fixed_slots.local_writes(func, &analysis.alloc);
            // Optional final spills may be assigned to the shared arena after
            // stackification. Account for them before analyzing callers, even on
            // the first placement iteration when no reserve exists yet.
            let may_use_arena_spills = analysis
                .alloc
                .object_spills()
                .any(|(value, _)| !analysis.stable_final_spill_values.contains(value));
            Ok((func, analysis, local_slot_writes, may_use_arena_spills))
        })
        .into_iter()
        .collect::<Result<Vec<_>, String>>()?;
        scc_results.sort_unstable_by_key(|(func, ..)| func.as_u32());

        // Callees in this SCC are its members; the rest are analyzed already.
        let mut scc_slot_writes = components
            .iter()
            .flat_map(|&func| schedule.call_graph.callee_of(func))
            .filter_map(|callee| slot_writes.get(callee))
            .fold(0, |writes, callee_writes| writes | callee_writes);
        let mut scc_may_use_arena_spills = false;
        for (func, analysis, local_slot_writes, may_use_arena_spills) in scc_results {
            scc_may_use_arena_spills |= may_use_arena_spills;
            scc_slot_writes |= local_slot_writes;
            analyses.insert(func, analysis);
        }
        slot_writes.extend(components.iter().map(|&func| (func, scc_slot_writes)));

        let scc_touches_scratch_arena = scc_may_use_arena_spills
            || components
                .iter()
                .any(|func| placement.funcs[func].mem_plan.scratch_words != 0)
            || components.iter().any(|func| {
                schedule
                    .call_graph
                    .callee_of(*func)
                    .iter()
                    .any(|callee| scratch_arena_effects.contains(callee))
            });
        if scc_touches_scratch_arena {
            scratch_arena_effects.extend(components.iter().copied());
        }
    }

    Ok(analyses)
}

fn prepare_machine_stackify_analysis(
    function: &mut sonatina_ir::Function,
    func: FuncRef,
    backend: &EvmBackend,
    fixed_slots: &FixedSlotSummaries,
    slot_writes: &FxHashMap<FuncRef, SlotBytes>,
    scratch_arena_effects: &FxHashSet<FuncRef>,
    search_cache: &mut StackifySearchCache,
) -> Result<MachineStackifyAnalysis, String> {
    let _span = trace_span!("sonatina.codegen.evm.machine.prepare_stackify_func").entered();
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    // `StackifyEdgeSplitter` subsumes critical-edge splitting and additionally splits in-cycle
    // multiway edges, establishing stackify's edge preconditions (see `stackalloc::stackify`).
    // Split first, then compute domtree/liveness over the post-split CFG below.
    StackifyEdgeSplitter::run(function, &mut cfg);
    // The split is the last change to the function before emission, which verifies it again.
    verify_machine_function(func, function)?;

    let mut dom = DomTree::new();
    dom.compute(&cfg);

    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);

    let mut inst_liveness = InstLiveness::new();
    inst_liveness.compute(function, &cfg, &liveness);

    let FixedSlotConflicts {
        barred,
        stable_final_spill_values,
    } = {
        let _span = trace_span!("sonatina.codegen.evm.machine.fixed_slot_conflicts").entered();
        FixedSlotConflicts::compute(
            function,
            &cfg,
            func,
            fixed_slots,
            slot_writes,
            scratch_arena_effects,
            &inst_liveness,
        )
    };
    let mut builder = StackifyBuilder::new(
        function,
        &cfg,
        &dom,
        &liveness,
        backend.stackify_reach_depth,
    )
    .with_search_profile(backend.stackify_search_profile)
    .with_scratch_slots(barred)
    .with_hot_immediate_caching()
    .with_entry_stack_record(backend.record_lowering);

    if backend.immediate_materialization_mode == ImmediateMaterializationMode::Size {
        builder = builder
            .with_hot_immediate_min_block_uses(HOT_IMMEDIATE_SIZE_MIN_BLOCK_USES)
            .with_hot_immediate_min_materialization_bytes(
                HOT_IMMEDIATE_SIZE_MIN_MATERIALIZATION_BYTES,
            );
    }

    let (alloc, trace) = if backend.capture_stackify_trace {
        let (alloc, trace) = builder.compute_with_trace_and_search_cache(search_cache);
        (alloc, Some(trace))
    } else {
        (builder.compute_with_search_cache(search_cache), None)
    };

    Ok(MachineStackifyAnalysis {
        alloc,
        stable_final_spill_values,
        trace,
    })
}
