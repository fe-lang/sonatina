use cranelift_entity::{EntityRef, SecondaryMap};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    AccessKind, BlockId, Function, InstId, InstSetExt, Module, Value, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{
        Isa,
        evm::{Evm, space::MEMORY},
    },
    module::{FuncRef, ModuleCtx},
};

use crate::{
    bitset::BitSet,
    module_analysis::{CallGraphSchedule, SccRef},
};

use super::{
    super::{
        EvmBackend, heap_plan, malloc_plan,
        mem_effects::compute_func_mem_effects,
        memory_plan::{
            self, BackendSpillReserve, FinalScratchReserveRange, FuncPreAnalysis, StableMode,
            WORD_BYTES, expect_func_entry,
        },
        prepare::{
            ArenaBaseFacts, choose_arena_base, compute_return_escape_caller_clamp_words,
            function_free_ptr_slot_facts, value_imm_u32,
        },
        ptr_escape::PtrEscapeSummary,
        static_arena_alloc::{
            BlockLiveSegment, LiveRegion, PackedObject, StackObjId, compute_block_order,
            pack_objects_presorted,
        },
    },
    free_ptr_floor::{
        ProgramFreePtrFloorInput, compute_free_ptr_write_summaries,
        compute_program_free_ptr_floor_before_malloc,
    },
    heap_state::compute_exact_heap_base_before_malloc,
};

#[derive(Clone, Debug)]
pub(crate) struct EvmMemoryPlacementPlan {
    pub(crate) arena_base: u32,
    pub(crate) global_dyn_base: u32,
    pub(crate) scratch_peak_words: u32,
    pub(crate) stable_chain_peak_words: u32,
    pub(crate) funcs: FxHashMap<FuncRef, EvmFuncPlacementPlan>,
}

#[derive(Clone, Debug)]
pub(crate) struct EvmFuncPlacementPlan {
    pub(crate) final_scratch_reserve: FinalScratchReserveRange,
    pub(crate) mem_plan: memory_plan::SemanticFuncPlan,
    pub(crate) malloc_placements: FxHashMap<InstId, MallocPlacement>,
    pub(crate) free_ptr_floor_before_malloc: FxHashMap<InstId, Option<u32>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MallocPlacement {
    Fixed {
        base: u32,
    },
    Heap {
        min_base: u32,
        needs_dyn_sp_clamp: bool,
        update_free_ptr: bool,
    },
}

#[derive(Clone, Debug, Default)]
struct PrivateStaticMallocProgramPlan {
    funcs: FxHashMap<FuncRef, PrivateStaticMallocFuncPlan>,
}

impl PrivateStaticMallocProgramPlan {
    fn backend_spill_reserves(&self) -> FxHashMap<FuncRef, BackendSpillReserve> {
        self.funcs
            .iter()
            .filter_map(|(&func, plan)| {
                (plan.extra_scratch_words != 0).then_some((
                    func,
                    BackendSpillReserve {
                        scratch_words: plan.extra_scratch_words,
                        stable_words: 0,
                    },
                ))
            })
            .collect()
    }
}

#[derive(Clone, Debug, Default)]
struct PrivateStaticMallocFuncPlan {
    word_offsets: FxHashMap<InstId, u32>,
    extra_scratch_words: u32,
}

#[derive(Clone, Debug)]
struct PrivateStaticMallocCandidate {
    malloc: InstId,
    size_words: u32,
    region: LiveRegion,
}

struct PrivateStaticMallocProgramCtx<'a> {
    module: &'a Module,
    funcs: &'a [FuncRef],
    analyses: &'a FxHashMap<FuncRef, FuncPreAnalysis>,
    semantic_plan: &'a memory_plan::ProgramMemoryPlan,
    isa: &'a Evm,
    heap_facts: &'a FxHashMap<FuncRef, FuncHeapFacts>,
    has_persistent_mallocs: bool,
    free_ptr_slot_may_be_touched: bool,
}

struct PrivateStaticMallocFuncCtx<'a> {
    function: &'a Function,
    analysis: &'a FuncPreAnalysis,
    func_plan: &'a memory_plan::SemanticFuncPlan,
    module: &'a ModuleCtx,
    isa: &'a Evm,
    heap_facts: &'a FuncHeapFacts,
    has_persistent_mallocs: bool,
    free_ptr_slot_may_be_touched: bool,
}

#[derive(Clone, Copy)]
pub(crate) struct MemoryPlacementSection<'a> {
    pub(crate) schedule: &'a CallGraphSchedule,
    pub(crate) funcs: &'a [FuncRef],
    pub(crate) entry: FuncRef,
    pub(crate) includes: &'a [FuncRef],
}

pub(crate) fn compute_semantic_memory_placement(
    module: &Module,
    section: MemoryPlacementSection<'_>,
    analyses: &FxHashMap<FuncRef, FuncPreAnalysis>,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    fixed_slot_effects: &FxHashSet<FuncRef>,
    backend: &EvmBackend,
    backend_spill_reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
) -> EvmMemoryPlacementPlan {
    let schedule = section.schedule;
    let funcs = section.funcs;
    let mut semantic_plan = memory_plan::compute_semantic_program_memory_plan(
        module,
        schedule,
        analyses,
        ptr_escape,
        &backend.isa,
        &backend.arena_cost_model,
    );
    semantic_plan.apply_backend_spill_reserves(schedule, backend_spill_reserves);
    let final_scratch_reserves =
        final_scratch_reserve_ranges(funcs, &semantic_plan, backend_spill_reserves);

    let mem_effects = compute_func_mem_effects(
        module,
        schedule,
        &semantic_plan,
        fixed_slot_effects,
        &backend.isa,
    );

    let mut annotations: Vec<_> = funcs
        .par_iter()
        .copied()
        .map(|func| {
            let analysis = expect_func_entry(analyses, func, "pre-analysis");
            let (malloc_escape_kinds, transient_mallocs) =
                module.func_store.view(func, |function| {
                    let escape_kinds = malloc_plan::compute_malloc_escape_kinds_for_function(
                        function,
                        &module.ctx,
                        &backend.isa,
                        ptr_escape,
                        &analysis.prov,
                    );
                    let transient = malloc_plan::compute_transient_mallocs(
                        function,
                        &module.ctx,
                        &backend.isa,
                        ptr_escape,
                        &analysis.prov,
                        Some(&mem_effects),
                        &analysis.inst_liveness,
                    );
                    (escape_kinds, transient)
                });
            (func, malloc_escape_kinds, transient_mallocs)
        })
        .collect();
    annotations.sort_unstable_by_key(|(func, ..)| func.as_u32());
    for (func, malloc_escape_kinds, transient_mallocs) in annotations {
        if let Some(func_plan) = semantic_plan.funcs.get_mut(&func) {
            func_plan.malloc_escape_kinds = malloc_escape_kinds;
            func_plan.transient_mallocs = transient_mallocs;
        }
    }
    let has_dynamic_frames = semantic_plan
        .funcs
        .values()
        .any(memory_plan::SemanticFuncPlan::uses_dynamic_frame);
    let backend_spill_scratch_reserve_peak = backend_spill_reserves
        .values()
        .map(|reserve| reserve.scratch_words)
        .max()
        .unwrap_or(0);
    let has_persistent_mallocs = funcs.iter().copied().any(|func| {
        let Some(func_plan) = semantic_plan.funcs.get(&func) else {
            return false;
        };
        module.func_store.view(func, |function| {
            function.layout.iter_block().any(|block| {
                function.layout.iter_inst(block).any(|inst| {
                    matches!(
                        backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                        EvmInstKind::EvmMalloc(_)
                    ) && !func_plan.transient_mallocs.contains(&inst)
                })
            })
        })
    });
    let entry_may_have_live_frame = compute_entry_may_have_live_frame(schedule, &semantic_plan);
    let (free_ptr_slot_may_be_touched, free_ptr_write_summaries) =
        compute_program_free_ptr_slot_facts(module, schedule, backend, analyses);
    let mut heap_facts_results: Vec<_> = funcs
        .par_iter()
        .copied()
        .map(|func| {
            let func_plan = expect_func_entry(&semantic_plan.funcs, func, "semantic plan");
            let analysis = expect_func_entry(analyses, func, "pre-analysis");
            let facts = module.func_store.view(func, |function| {
                compute_func_heap_facts(
                    function,
                    func,
                    &module.ctx,
                    &backend.isa,
                    analysis,
                    func_plan,
                    &entry_may_have_live_frame,
                )
            });
            (func, facts)
        })
        .collect();
    heap_facts_results.sort_unstable_by_key(|(func, _)| func.as_u32());
    let heap_facts: FxHashMap<FuncRef, FuncHeapFacts> = heap_facts_results.into_iter().collect();

    let private_static_mallocs =
        compute_private_static_malloc_program_plan(PrivateStaticMallocProgramCtx {
            module,
            funcs,
            analyses,
            semantic_plan: &semantic_plan,
            isa: &backend.isa,
            heap_facts: &heap_facts,
            has_persistent_mallocs,
            free_ptr_slot_may_be_touched,
        });
    let private_static_reserves = private_static_mallocs.backend_spill_reserves();
    semantic_plan.apply_backend_spill_reserves(schedule, &private_static_reserves);
    let return_escape_caller_abs_words =
        compute_return_escape_caller_clamp_words(schedule, &semantic_plan, &FxHashMap::default());
    for (func, return_escape_caller_abs_words) in return_escape_caller_abs_words {
        if let Some(func_plan) = semantic_plan.funcs.get_mut(&func) {
            func_plan.return_escape_caller_abs_words = return_escape_caller_abs_words;
        }
    }

    let arena_base = choose_arena_base(
        module,
        funcs,
        backend,
        analyses,
        ArenaBaseFacts {
            has_dynamic_frames,
            has_stackify_fixed_slot_spills: !fixed_slot_effects.is_empty(),
            backend_spill_scratch_reserve_words: backend_spill_scratch_reserve_peak,
            has_persistent_mallocs,
        },
    );
    if has_dynamic_frames {
        semantic_plan.scratch_peak_words = semantic_plan
            .scratch_peak_words
            .max(backend_spill_scratch_reserve_peak);
    }
    semantic_plan.set_arena_base(arena_base);

    let mut malloc_bounds = heap_plan::compute_semantic_malloc_future_abs_words_with_extra(
        module,
        schedule,
        &semantic_plan,
        analyses,
        &backend.isa,
        &FxHashMap::default(),
    );
    for (&func, &reserve) in backend_spill_reserves {
        if let Some(bounds) = malloc_bounds.get_mut(&func)
            && let Some(func_plan) = semantic_plan.funcs.get(&func)
        {
            let reserve_abs_words = backend_spill_reserve_abs_words(func_plan, reserve);
            for bound in bounds.values_mut() {
                *bound = (*bound).max(reserve_abs_words);
            }
        }
    }
    for (func, bounds) in malloc_bounds {
        if let Some(func_plan) = semantic_plan.funcs.get_mut(&func) {
            func_plan.malloc_future_abs_words = bounds;
        }
    }

    let placement_ctx = MallocPlacementCtx {
        isa: &backend.isa,
        module: &module.ctx,
        global_dyn_base: semantic_plan.global_dyn_base,
        backend_spill_reserve_peak: backend_spill_scratch_reserve_peak,
        section_entry: section.entry,
        has_persistent_mallocs,
        free_ptr_slot_may_be_touched,
        private_static_mallocs: &private_static_mallocs,
    };
    let malloc_placements: FxHashMap<_, _> = funcs
        .iter()
        .copied()
        .map(|func| {
            let func_plan = expect_func_entry(&semantic_plan.funcs, func, "semantic plan");
            let malloc_placements = module.func_store.view(func, |function| {
                placement_ctx.compute_func_malloc_placements(
                    function,
                    func,
                    &heap_facts[&func],
                    func_plan,
                )
            });
            (func, malloc_placements)
        })
        .collect();
    let free_ptr_floor_before_malloc =
        compute_program_free_ptr_floor_before_malloc(ProgramFreePtrFloorInput {
            module,
            funcs,
            section_entry: section.entry,
            section_includes: section.includes,
            analyses,
            source_is: backend.isa.inst_set(),
            malloc_placements: &malloc_placements,
            free_ptr_write_summaries: &free_ptr_write_summaries,
        });
    let func_placements = funcs
        .iter()
        .copied()
        .map(|func| {
            let func_plan = expect_func_entry(&semantic_plan.funcs, func, "semantic plan");
            let malloc_placements = malloc_placements.get(&func).cloned().unwrap_or_default();
            let free_ptr_floor_before_malloc = free_ptr_floor_before_malloc
                .get(&func)
                .cloned()
                .unwrap_or_default();
            (
                func,
                EvmFuncPlacementPlan {
                    final_scratch_reserve: final_scratch_reserves
                        .get(&func)
                        .copied()
                        .unwrap_or_default(),
                    mem_plan: func_plan.clone(),
                    malloc_placements,
                    free_ptr_floor_before_malloc,
                },
            )
        })
        .collect();

    EvmMemoryPlacementPlan {
        arena_base: semantic_plan.arena_base,
        global_dyn_base: semantic_plan.global_dyn_base,
        scratch_peak_words: semantic_plan.scratch_peak_words,
        stable_chain_peak_words: semantic_plan.stable_chain_peak_words,
        funcs: func_placements,
    }
}

/// Per-function heap facts computed once and shared by malloc placement and
/// private-static malloc planning.
pub(crate) struct FuncHeapFacts {
    exact_heap_base_before_malloc: FxHashMap<InstId, bool>,
    terminal_private_mallocs: FxHashSet<InstId>,
    needs_dyn_sp_clamp: bool,
}

fn compute_func_heap_facts(
    function: &Function,
    func: FuncRef,
    module: &ModuleCtx,
    isa: &Evm,
    analysis: &FuncPreAnalysis,
    func_plan: &memory_plan::SemanticFuncPlan,
    entry_may_have_live_frame: &FxHashMap<FuncRef, bool>,
) -> FuncHeapFacts {
    let needs_dyn_sp_clamp = func_plan.uses_dynamic_frame()
        || entry_may_have_live_frame
            .get(&func)
            .copied()
            .unwrap_or(false);
    let exact_heap_base_before_malloc = compute_exact_heap_base_before_malloc(
        function,
        isa,
        &analysis.cfg,
        func_plan,
        &analysis.prov.value,
        !needs_dyn_sp_clamp,
    );
    let terminal_private_mallocs = TerminalPrivateMallocAnalysis::new(
        function,
        module,
        isa,
        &analysis.cfg,
        &exact_heap_base_before_malloc,
    )
    .compute();
    FuncHeapFacts {
        exact_heap_base_before_malloc,
        terminal_private_mallocs,
        needs_dyn_sp_clamp,
    }
}

struct MallocPlacementCtx<'a> {
    isa: &'a Evm,
    module: &'a ModuleCtx,
    global_dyn_base: u32,
    backend_spill_reserve_peak: u32,
    section_entry: FuncRef,
    has_persistent_mallocs: bool,
    free_ptr_slot_may_be_touched: bool,
    private_static_mallocs: &'a PrivateStaticMallocProgramPlan,
}

impl MallocPlacementCtx<'_> {
    fn compute_func_malloc_placements(
        &self,
        function: &Function,
        func: FuncRef,
        heap_facts: &FuncHeapFacts,
        func_plan: &memory_plan::SemanticFuncPlan,
    ) -> FxHashMap<InstId, MallocPlacement> {
        let mut out = FxHashMap::default();
        let needs_dyn_sp_clamp = heap_facts.needs_dyn_sp_clamp;
        let exact_heap_base_before_malloc = &heap_facts.exact_heap_base_before_malloc;
        let terminal_private_mallocs = &heap_facts.terminal_private_mallocs;
        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                if !matches!(
                    self.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                    EvmInstKind::EvmMalloc(_)
                ) {
                    continue;
                }

                let transient = func_plan.transient_mallocs.contains(&inst);
                let min_base = malloc_min_base(
                    func_plan,
                    self.global_dyn_base,
                    self.backend_spill_reserve_peak,
                    inst,
                );
                let exact_heap_base = exact_heap_base_before_malloc
                    .get(&inst)
                    .copied()
                    .unwrap_or(false);
                let fixed_by_terminal_or_program_rule = transient
                    && (terminal_private_mallocs.contains(&inst)
                        || (!self.free_ptr_slot_may_be_touched
                            && !needs_dyn_sp_clamp
                            && !self.has_persistent_mallocs));
                let fixed_by_exact_entry_rule = !fixed_by_terminal_or_program_rule
                    && transient
                    && exact_heap_base
                    && self.section_entry == func
                    && function.arg_values.is_empty()
                    && malloc_private_uses_are_compatible_with_fixed_base(
                        function,
                        self.module,
                        self.isa,
                        inst,
                        exact_heap_base,
                    );
                let private_static_base = self
                    .private_static_mallocs
                    .funcs
                    .get(&func)
                    .and_then(|plan| plan.word_offsets.get(&inst))
                    .map(|&word| func_plan.abs_addr_for_word(word));
                let placement = if fixed_by_terminal_or_program_rule {
                    MallocPlacement::Fixed { base: min_base }
                } else if transient && let Some(base) = private_static_base {
                    MallocPlacement::Fixed { base }
                } else if fixed_by_exact_entry_rule {
                    MallocPlacement::Fixed { base: min_base }
                } else {
                    MallocPlacement::Heap {
                        min_base,
                        needs_dyn_sp_clamp,
                        update_free_ptr: !transient,
                    }
                };
                out.insert(inst, placement);
            }
        }
        out
    }
}

fn final_scratch_reserve_ranges(
    funcs: &[FuncRef],
    semantic_plan: &memory_plan::ProgramMemoryPlan,
    backend_spill_reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
) -> FxHashMap<FuncRef, FinalScratchReserveRange> {
    funcs
        .iter()
        .copied()
        .map(|func| {
            let reserve = backend_spill_reserves
                .get(&func)
                .copied()
                .unwrap_or_default();
            let func_plan = expect_func_entry(&semantic_plan.funcs, func, "semantic plan");
            let start_word = func_plan
                .scratch_words
                .checked_sub(reserve.scratch_words)
                .expect("backend scratch spill reserve exceeds scratch words");
            (
                func,
                FinalScratchReserveRange {
                    start_word,
                    words: reserve.scratch_words,
                },
            )
        })
        .collect()
}

fn compute_private_static_malloc_program_plan(
    ctx: PrivateStaticMallocProgramCtx<'_>,
) -> PrivateStaticMallocProgramPlan {
    let funcs = ctx
        .funcs
        .iter()
        .copied()
        .filter_map(|func| {
            let function_plan = ctx.semantic_plan.funcs.get(&func)?;
            let analysis = expect_func_entry(ctx.analyses, func, "pre-analysis");
            let plan = ctx.module.func_store.view(func, |function| {
                compute_private_static_malloc_func_plan(PrivateStaticMallocFuncCtx {
                    function,
                    analysis,
                    func_plan: function_plan,
                    module: &ctx.module.ctx,
                    isa: ctx.isa,
                    heap_facts: &ctx.heap_facts[&func],
                    has_persistent_mallocs: ctx.has_persistent_mallocs,
                    free_ptr_slot_may_be_touched: ctx.free_ptr_slot_may_be_touched,
                })
            });
            (!plan.word_offsets.is_empty()).then_some((func, plan))
        })
        .collect();

    PrivateStaticMallocProgramPlan { funcs }
}

fn compute_private_static_malloc_func_plan(
    ctx: PrivateStaticMallocFuncCtx<'_>,
) -> PrivateStaticMallocFuncPlan {
    if !ctx.has_persistent_mallocs
        && !ctx.free_ptr_slot_may_be_touched
        && !ctx.heap_facts.needs_dyn_sp_clamp
    {
        return PrivateStaticMallocFuncPlan::default();
    }

    let exact_heap_base_before_malloc = &ctx.heap_facts.exact_heap_base_before_malloc;
    let terminal_private_mallocs = &ctx.heap_facts.terminal_private_mallocs;

    let mut candidates = Vec::new();
    for block in ctx.function.layout.iter_block() {
        for inst in ctx.function.layout.iter_inst(block) {
            if terminal_private_mallocs.contains(&inst) {
                continue;
            }
            if let Some(candidate) = private_static_malloc_candidate(
                ctx.function,
                ctx.analysis,
                ctx.func_plan,
                ctx.module,
                ctx.isa,
                inst,
                exact_heap_base_before_malloc
                    .get(&inst)
                    .copied()
                    .unwrap_or(false),
            ) {
                candidates.push(candidate);
            }
        }
    }
    if candidates.is_empty() {
        return PrivateStaticMallocFuncPlan::default();
    }

    let mut objects: Vec<_> = candidates
        .iter()
        .enumerate()
        .map(|(idx, candidate)| {
            let id = StackObjId::new(idx);
            PackedObject {
                id,
                size_words: candidate.size_words,
                region: candidate.region.clone(),
                min_offset_words: ctx.func_plan.scratch_words,
            }
        })
        .collect();
    objects.sort_unstable_by_key(|object| object.region.sort_key(object.id));
    let (offsets, peak_words) = pack_objects_presorted(&objects);
    let mut word_offsets = FxHashMap::default();
    for (idx, candidate) in candidates.iter().enumerate() {
        let id = StackObjId::new(idx);
        let Some(&offset) = offsets.get(&id) else {
            continue;
        };
        word_offsets.insert(candidate.malloc, offset);
    }

    PrivateStaticMallocFuncPlan {
        word_offsets,
        extra_scratch_words: peak_words
            .checked_sub(ctx.func_plan.scratch_words)
            .expect("private static malloc peak below scratch base"),
    }
}

fn private_static_malloc_candidate(
    function: &Function,
    analysis: &FuncPreAnalysis,
    func_plan: &memory_plan::SemanticFuncPlan,
    module: &ModuleCtx,
    isa: &Evm,
    inst: InstId,
    exact_heap_base: bool,
) -> Option<PrivateStaticMallocCandidate> {
    let EvmInstKind::EvmMalloc(malloc) = isa.inst_set().resolve_inst(function.dfg.inst(inst))
    else {
        return None;
    };
    if !func_plan.transient_mallocs.contains(&inst) {
        return None;
    }
    let size_bytes = value_imm_u32(function, *malloc.size())?;
    let size_words = aligned_malloc_words(size_bytes)?;
    if size_words == 0 {
        return None;
    }

    let malloc_uses = PrivateMallocUseAnalysis::new(function, module, isa, inst);
    malloc_uses.analyze_static_private_address_uses(size_bytes, exact_heap_base)?;
    if private_static_malloc_live_across_internal_call(function, analysis, &malloc_uses) {
        return None;
    }
    let region = private_static_malloc_live_region(function, analysis, &malloc_uses)?;
    Some(PrivateStaticMallocCandidate {
        malloc: inst,
        size_words,
        region,
    })
}

fn aligned_malloc_words(size_bytes: u32) -> Option<u32> {
    size_bytes
        .checked_add(WORD_BYTES - 1)
        .map(|size| size / WORD_BYTES)
}

fn private_static_malloc_live_across_internal_call(
    function: &Function,
    analysis: &FuncPreAnalysis,
    malloc_uses: &PrivateMallocUseAnalysis<'_>,
) -> bool {
    function.layout.iter_block().any(|block| {
        function.layout.iter_inst(block).any(|inst| {
            function.dfg.call_info(inst).is_some()
                && (malloc_uses.inst_uses_derived_value(inst)
                    || analysis
                        .inst_liveness
                        .live_out(inst)
                        .iter()
                        .any(|value| malloc_uses.is_derived_value(value)))
        })
    })
}

fn private_static_malloc_live_region(
    function: &Function,
    analysis: &FuncPreAnalysis,
    malloc_uses: &PrivateMallocUseAnalysis<'_>,
) -> Option<LiveRegion> {
    let blocks = compute_block_order(function, &analysis.block_order);
    let mut segments = SmallVec::<[BlockLiveSegment; 4]>::new();
    let mut first_rank: Option<u32> = None;
    let mut last_rank = 0;
    let mut next_rank = 0u32;
    let mut has_use = false;

    for block in blocks {
        let block_base_rank = next_rank;
        let mut segment_start = None;
        let mut segment_end = 0u32;
        let mut inst_idx = 0u32;
        for inst in function.layout.iter_inst(block) {
            let uses_candidate =
                inst != malloc_uses.malloc && malloc_uses.inst_uses_derived_value(inst);
            has_use |= uses_candidate;
            let live_after = analysis
                .inst_liveness
                .live_out(inst)
                .iter()
                .any(|value| malloc_uses.is_derived_value(value));
            if inst == malloc_uses.malloc || uses_candidate || live_after {
                segment_start.get_or_insert(inst_idx);
                segment_end = inst_idx.checked_add(1)?;
            }
            inst_idx = inst_idx.checked_add(1)?;
        }
        next_rank = next_rank.checked_add(inst_idx)?;

        if let Some(start_boundary) = segment_start
            && start_boundary != segment_end
        {
            segments.push(BlockLiveSegment {
                block,
                start_boundary,
                end_boundary: segment_end,
            });
            let start_rank = block_base_rank.checked_add(start_boundary)?;
            let end_rank = block_base_rank.checked_add(segment_end)?;
            first_rank = Some(first_rank.map_or(start_rank, |rank| rank.min(start_rank)));
            last_rank = last_rank.max(end_rank);
        }
    }

    if !has_use || segments.is_empty() {
        return None;
    }
    segments.sort_unstable_by_key(|segment| {
        (
            segment.block.as_u32(),
            segment.start_boundary,
            segment.end_boundary,
        )
    });

    Some(LiveRegion {
        segments,
        phi_edges: BitSet::default(),
        first_rank: first_rank?,
        last_rank,
    })
}

struct TerminalPrivateMallocAnalysis<'a> {
    function: &'a Function,
    module: &'a ModuleCtx,
    isa: &'a Evm,
    cfg: &'a ControlFlowGraph,
    exact_heap_base_before_malloc: &'a FxHashMap<InstId, bool>,
    terminal_private_blocks: SecondaryMap<BlockId, bool>,
}

impl<'a> TerminalPrivateMallocAnalysis<'a> {
    fn new(
        function: &'a Function,
        module: &'a ModuleCtx,
        isa: &'a Evm,
        cfg: &'a ControlFlowGraph,
        exact_heap_base_before_malloc: &'a FxHashMap<InstId, bool>,
    ) -> Self {
        let mut terminal_private_blocks = SecondaryMap::new();
        for block in function.layout.iter_block() {
            let _ = &mut terminal_private_blocks[block];
        }
        Self {
            function,
            module,
            isa,
            cfg,
            exact_heap_base_before_malloc,
            terminal_private_blocks,
        }
    }

    fn compute(mut self) -> FxHashSet<InstId> {
        self.compute_terminal_private_blocks();

        let mut out = FxHashSet::default();
        for block in self.function.layout.iter_block() {
            for inst in self.function.layout.iter_inst(block) {
                if matches!(self.resolve(inst), EvmInstKind::EvmMalloc(_))
                    && self
                        .suffix_is_terminal_private(block, self.function.layout.next_inst_of(inst))
                    && self.malloc_is_private(inst)
                {
                    out.insert(inst);
                }
            }
        }

        out
    }

    fn compute_terminal_private_blocks(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            for block in self.function.layout.iter_block() {
                let next = self.block_is_terminal_private(block);
                changed |= self.terminal_private_blocks[block] != next;
                self.terminal_private_blocks[block] = next;
            }
        }
    }

    fn block_is_terminal_private(&self, block: BlockId) -> bool {
        for inst in self.function.layout.iter_inst(block) {
            if self.inst_is_evm_terminal(inst) {
                return true;
            }
            if self.function.dfg.inst(inst).is_terminator() {
                return self.successors_are_terminal_private(block);
            }
            if !self.inst_allows_terminal_private_prefix(inst) {
                return false;
            }
        }

        self.successors_are_terminal_private(block)
    }

    fn successors_are_terminal_private(&self, block: BlockId) -> bool {
        let mut succs = self.cfg.succs_of(block);
        let Some(first) = succs.next() else {
            return false;
        };
        self.terminal_private_blocks[*first]
            && succs.all(|succ| self.terminal_private_blocks[*succ])
    }

    fn inst_is_evm_terminal(&self, inst: InstId) -> bool {
        matches!(
            self.resolve(inst),
            EvmInstKind::EvmReturn(_) | EvmInstKind::EvmRevert(_)
        )
    }

    fn inst_allows_terminal_private_prefix(&self, inst: InstId) -> bool {
        let effects = self.function.dfg.effects(inst);
        self.function.dfg.call_info(inst).is_none()
            && effects.other.is_empty()
            && effects
                .accesses
                .iter()
                .all(|access| access.kind == AccessKind::Write && access.space == MEMORY)
    }

    fn suffix_is_terminal_private(&self, block: BlockId, mut cursor: Option<InstId>) -> bool {
        while let Some(inst) = cursor {
            if self.inst_is_evm_terminal(inst) {
                return true;
            }
            if self.function.dfg.inst(inst).is_terminator() {
                return self.successors_are_terminal_private(block);
            }
            if !self.inst_allows_terminal_private_prefix(inst) {
                return false;
            }
            cursor = self.function.layout.next_inst_of(inst);
        }

        self.successors_are_terminal_private(block)
    }

    fn malloc_is_private(&self, inst: InstId) -> bool {
        malloc_private_uses_are_compatible_with_fixed_base(
            self.function,
            self.module,
            self.isa,
            inst,
            self.exact_heap_base_before_malloc
                .get(&inst)
                .copied()
                .unwrap_or(false),
        )
    }

    fn resolve(&self, inst: InstId) -> EvmInstKind<'_> {
        self.isa
            .inst_set()
            .resolve_inst(self.function.dfg.inst(inst))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PrivateMallocUseInfo {
    requires_exact_heap_base: bool,
}

struct PrivateMallocUseAnalysis<'a> {
    function: &'a Function,
    module: &'a ModuleCtx,
    isa: &'a Evm,
    malloc: InstId,
    derived_values: FxHashSet<ValueId>,
}

impl<'a> PrivateMallocUseAnalysis<'a> {
    fn new(function: &'a Function, module: &'a ModuleCtx, isa: &'a Evm, malloc: InstId) -> Self {
        let mut analysis = Self {
            function,
            module,
            isa,
            malloc,
            derived_values: function.dfg.inst_results(malloc).iter().copied().collect(),
        };
        analysis.compute_derived_values();
        analysis
    }

    fn analyze_private_address_uses(&self) -> Option<PrivateMallocUseInfo> {
        let mut requires_exact_heap_base = false;
        for block in self.function.layout.iter_block() {
            for inst in self.function.layout.iter_inst(block) {
                if inst != self.malloc && self.inst_uses_derived_value(inst) {
                    requires_exact_heap_base |= self.use_requires_exact_heap_base(inst)?;
                }
            }
        }

        Some(PrivateMallocUseInfo {
            requires_exact_heap_base,
        })
    }

    fn analyze_static_private_address_uses(
        &self,
        alloc_size_bytes: u32,
        exact_heap_base: bool,
    ) -> Option<()> {
        for block in self.function.layout.iter_block() {
            for inst in self.function.layout.iter_inst(block) {
                if inst != self.malloc && self.inst_uses_derived_value(inst) {
                    self.static_private_use_is_bounded(inst, alloc_size_bytes, exact_heap_base)?;
                }
            }
        }

        Some(())
    }

    fn compute_derived_values(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            for block in self.function.layout.iter_block() {
                for inst in self.function.layout.iter_inst(block) {
                    if inst != self.malloc && self.inst_uses_derived_value(inst) {
                        changed |= self.add_address_derived_results(inst);
                    }
                }
            }
        }
    }

    fn add_address_derived_results(&mut self, inst: InstId) -> bool {
        match self.resolve(inst) {
            EvmInstKind::Bitcast(_)
            | EvmInstKind::IntToPtr(_)
            | EvmInstKind::PtrToInt(_)
            | EvmInstKind::Gep(_)
            | EvmInstKind::Add(_)
            | EvmInstKind::Sub(_)
            | EvmInstKind::Phi(_) => {
                let mut changed = false;
                for result in self.function.dfg.inst_results(inst) {
                    changed |= self.derived_values.insert(*result);
                }
                changed
            }
            EvmInstKind::Uaddo(_)
            | EvmInstKind::Saddo(_)
            | EvmInstKind::Usubo(_)
            | EvmInstKind::Ssubo(_) => self
                .function
                .dfg
                .inst_results(inst)
                .first()
                .is_some_and(|result| self.derived_values.insert(*result)),
            _ => false,
        }
    }

    fn use_requires_exact_heap_base(&self, inst: InstId) -> Option<bool> {
        if self.inst_derives_address(inst) {
            return self
                .checked_overflow_flag(inst)
                .map_or(Some(false), |flag| {
                    self.checked_overflow_flag_is_private_control(flag)
                });
        }

        match self.resolve(inst) {
            EvmInstKind::Lt(lt) => {
                self.address_overflow_predicate_requires_exact_heap_base(inst, *lt.lhs(), *lt.rhs())
            }
            EvmInstKind::Mstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                Some(false)
            }
            EvmInstKind::EvmMstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                Some(false)
            }
            EvmInstKind::EvmMstore8(mstore) if !self.derived_values.contains(mstore.val()) => {
                Some(false)
            }
            EvmInstKind::EvmReturn(ret) if !self.derived_values.contains(ret.len()) => Some(false),
            EvmInstKind::EvmRevert(revert) if !self.derived_values.contains(revert.len()) => {
                Some(false)
            }
            _ => None,
        }
    }

    fn static_private_use_is_bounded(
        &self,
        inst: InstId,
        alloc_size_bytes: u32,
        exact_heap_base: bool,
    ) -> Option<()> {
        if self.inst_derives_address(inst) {
            if let Some(flag) = self.checked_overflow_flag(inst)
                && self.value_is_used(flag)
            {
                return None;
            }
            return Some(());
        }

        match self.resolve(inst) {
            EvmInstKind::Lt(lt)
                if exact_heap_base && self.inst_result_uses_are_private_branches(inst) =>
            {
                self.static_overflow_predicate_is_false(*lt.lhs(), *lt.rhs(), alloc_size_bytes)
            }
            EvmInstKind::Mload(mload) => {
                self.typed_addr_range_within_alloc(*mload.addr(), *mload.ty(), alloc_size_bytes)
            }
            EvmInstKind::Mstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                self.typed_addr_range_within_alloc(*mstore.addr(), *mstore.ty(), alloc_size_bytes)
            }
            EvmInstKind::EvmMload(mload) => {
                self.addr_range_within_alloc(*mload.addr(), WORD_BYTES, alloc_size_bytes)
            }
            EvmInstKind::EvmMstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                self.addr_range_within_alloc(*mstore.addr(), WORD_BYTES, alloc_size_bytes)
            }
            EvmInstKind::EvmMstore8(mstore) if !self.derived_values.contains(mstore.val()) => {
                self.addr_range_within_alloc(*mstore.addr(), 1, alloc_size_bytes)
            }
            EvmInstKind::EvmKeccak256(keccak) => {
                let len = self.static_len(*keccak.len())?;
                self.addr_range_within_alloc(*keccak.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmCalldataCopy(copy)
                if self.values_are_not_derived([*copy.data_offset(), *copy.len()]) =>
            {
                let len = self.static_len(*copy.len())?;
                self.addr_range_within_alloc(*copy.dst_addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmCodeCopy(copy)
                if self.values_are_not_derived([*copy.code_offset(), *copy.len()]) =>
            {
                let len = self.static_len(*copy.len())?;
                self.addr_range_within_alloc(*copy.dst_addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmReturnDataCopy(copy)
                if self.values_are_not_derived([*copy.data_offset(), *copy.len()]) =>
            {
                let len = self.static_len(*copy.len())?;
                self.addr_range_within_alloc(*copy.dst_addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmExtCodeCopy(copy)
                if self.values_are_not_derived([
                    *copy.ext_addr(),
                    *copy.code_offset(),
                    *copy.len(),
                ]) =>
            {
                let len = self.static_len(*copy.len())?;
                self.addr_range_within_alloc(*copy.dst_addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmMcopy(copy) if !self.derived_values.contains(copy.len()) => {
                let len = self.static_len(*copy.len())?;
                if self.derived_values.contains(copy.addr())
                    && !self.derived_values.contains(copy.dest())
                    && len != 0
                {
                    return None;
                }
                self.addr_range_within_alloc(*copy.dest(), len, alloc_size_bytes)?;
                self.addr_range_within_alloc(*copy.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmLog0(log) if !self.derived_values.contains(log.len()) => {
                let len = self.static_len(*log.len())?;
                self.addr_range_within_alloc(*log.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmLog1(log)
                if self.values_are_not_derived([*log.len(), *log.topic0()]) =>
            {
                let len = self.static_len(*log.len())?;
                self.addr_range_within_alloc(*log.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmLog2(log)
                if self.values_are_not_derived([*log.len(), *log.topic0(), *log.topic1()]) =>
            {
                let len = self.static_len(*log.len())?;
                self.addr_range_within_alloc(*log.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmLog3(log)
                if self.values_are_not_derived([
                    *log.len(),
                    *log.topic0(),
                    *log.topic1(),
                    *log.topic2(),
                ]) =>
            {
                let len = self.static_len(*log.len())?;
                self.addr_range_within_alloc(*log.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmLog4(log)
                if self.values_are_not_derived([
                    *log.len(),
                    *log.topic0(),
                    *log.topic1(),
                    *log.topic2(),
                    *log.topic3(),
                ]) =>
            {
                let len = self.static_len(*log.len())?;
                self.addr_range_within_alloc(*log.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmCreate(create)
                if self.values_are_not_derived([*create.val(), *create.len()]) =>
            {
                let len = self.static_len(*create.len())?;
                self.addr_range_within_alloc(*create.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmCreate2(create)
                if self.values_are_not_derived([*create.val(), *create.len(), *create.salt()]) =>
            {
                let len = self.static_len(*create.len())?;
                self.addr_range_within_alloc(*create.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmCall(call)
                if self.values_are_not_derived([
                    *call.gas(),
                    *call.addr(),
                    *call.val(),
                    *call.arg_len(),
                    *call.ret_len(),
                ]) =>
            {
                self.call_addr_ranges_are_bounded(
                    *call.arg_addr(),
                    *call.arg_len(),
                    *call.ret_addr(),
                    *call.ret_len(),
                    alloc_size_bytes,
                )
            }
            EvmInstKind::EvmCallCode(call)
                if self.values_are_not_derived([
                    *call.gas(),
                    *call.addr(),
                    *call.val(),
                    *call.arg_len(),
                    *call.ret_len(),
                ]) =>
            {
                self.call_addr_ranges_are_bounded(
                    *call.arg_addr(),
                    *call.arg_len(),
                    *call.ret_addr(),
                    *call.ret_len(),
                    alloc_size_bytes,
                )
            }
            EvmInstKind::EvmDelegateCall(call)
                if self.values_are_not_derived([
                    *call.gas(),
                    *call.ext_addr(),
                    *call.arg_len(),
                    *call.ret_len(),
                ]) =>
            {
                self.call_addr_ranges_are_bounded(
                    *call.arg_addr(),
                    *call.arg_len(),
                    *call.ret_addr(),
                    *call.ret_len(),
                    alloc_size_bytes,
                )
            }
            EvmInstKind::EvmStaticCall(call)
                if self.values_are_not_derived([
                    *call.gas(),
                    *call.ext_addr(),
                    *call.arg_len(),
                    *call.ret_len(),
                ]) =>
            {
                self.call_addr_ranges_are_bounded(
                    *call.arg_addr(),
                    *call.arg_len(),
                    *call.ret_addr(),
                    *call.ret_len(),
                    alloc_size_bytes,
                )
            }
            EvmInstKind::EvmReturn(ret) if !self.derived_values.contains(ret.len()) => {
                let len = self.static_len(*ret.len())?;
                self.addr_range_within_alloc(*ret.addr(), len, alloc_size_bytes)
            }
            EvmInstKind::EvmRevert(revert) if !self.derived_values.contains(revert.len()) => {
                let len = self.static_len(*revert.len())?;
                self.addr_range_within_alloc(*revert.addr(), len, alloc_size_bytes)
            }
            _ => None,
        }
    }

    fn call_addr_ranges_are_bounded(
        &self,
        arg_addr: ValueId,
        arg_len: ValueId,
        ret_addr: ValueId,
        ret_len: ValueId,
        alloc_size_bytes: u32,
    ) -> Option<()> {
        let arg_len = self.static_len(arg_len)?;
        let ret_len = self.static_len(ret_len)?;
        if self.derived_values.contains(&arg_addr)
            && !self.derived_values.contains(&ret_addr)
            && ret_len != 0
        {
            return None;
        }
        self.addr_range_within_alloc(arg_addr, arg_len, alloc_size_bytes)?;
        self.addr_range_within_alloc(ret_addr, ret_len, alloc_size_bytes)
    }

    fn typed_addr_range_within_alloc(
        &self,
        addr: ValueId,
        ty: sonatina_ir::Type,
        alloc_size_bytes: u32,
    ) -> Option<()> {
        let size = u32::try_from(self.module.size_of(ty).ok()?).ok()?;
        self.addr_range_within_alloc(addr, size, alloc_size_bytes)
    }

    fn addr_range_within_alloc(
        &self,
        addr: ValueId,
        len: u32,
        alloc_size_bytes: u32,
    ) -> Option<()> {
        if len == 0 || !self.derived_values.contains(&addr) {
            return Some(());
        }

        let offset = u32::try_from(self.derived_const_offset(addr)?).ok()?;
        (offset.checked_add(len)? <= alloc_size_bytes).then_some(())
    }

    fn static_len(&self, len: ValueId) -> Option<u32> {
        (!self.derived_values.contains(&len))
            .then(|| value_imm_u32(self.function, len))
            .flatten()
    }

    fn derived_const_offset(&self, value: ValueId) -> Option<i64> {
        self.derived_const_offset_impl(value, &mut FxHashSet::default())
    }

    fn derived_const_offset_impl(
        &self,
        value: ValueId,
        visiting: &mut FxHashSet<ValueId>,
    ) -> Option<i64> {
        if !self.derived_values.contains(&value) || !visiting.insert(value) {
            return None;
        }

        let offset = match self.function.dfg.get_value(value)? {
            Value::Inst {
                inst, result_idx, ..
            } if *inst == self.malloc && *result_idx == 0 => 0,
            Value::Inst {
                inst, result_idx, ..
            } => match self.resolve(*inst) {
                EvmInstKind::Bitcast(cast) => {
                    self.derived_const_offset_impl(*cast.from(), visiting)?
                }
                EvmInstKind::IntToPtr(cast) => {
                    self.derived_const_offset_impl(*cast.from(), visiting)?
                }
                EvmInstKind::PtrToInt(cast) => {
                    self.derived_const_offset_impl(*cast.from(), visiting)?
                }
                EvmInstKind::Add(add) => self.add_const_offset(*add.lhs(), *add.rhs(), visiting)?,
                EvmInstKind::Sub(sub) => {
                    let lhs = self.derived_const_offset_impl(*sub.lhs(), visiting)?;
                    let rhs = i64::from(value_imm_u32(self.function, *sub.rhs())?);
                    lhs.checked_sub(rhs)?
                }
                EvmInstKind::Uaddo(add) if *result_idx == 0 => {
                    self.add_const_offset(*add.lhs(), *add.rhs(), visiting)?
                }
                EvmInstKind::Saddo(add) if *result_idx == 0 => {
                    self.add_const_offset(*add.lhs(), *add.rhs(), visiting)?
                }
                EvmInstKind::Usubo(sub) if *result_idx == 0 => {
                    let lhs = self.derived_const_offset_impl(*sub.lhs(), visiting)?;
                    let rhs = i64::from(value_imm_u32(self.function, *sub.rhs())?);
                    lhs.checked_sub(rhs)?
                }
                EvmInstKind::Ssubo(sub) if *result_idx == 0 => {
                    let lhs = self.derived_const_offset_impl(*sub.lhs(), visiting)?;
                    let rhs = i64::from(value_imm_u32(self.function, *sub.rhs())?);
                    lhs.checked_sub(rhs)?
                }
                EvmInstKind::Phi(phi) => {
                    let mut args = phi.args().iter();
                    let (first, _) = args.next()?;
                    let first_offset = self.derived_const_offset_impl(*first, visiting)?;
                    if args.all(|(arg, _)| {
                        self.derived_const_offset_impl(*arg, visiting) == Some(first_offset)
                    }) {
                        first_offset
                    } else {
                        return None;
                    }
                }
                _ => return None,
            },
            _ => return None,
        };
        visiting.remove(&value);
        Some(offset)
    }

    fn add_const_offset(
        &self,
        lhs: ValueId,
        rhs: ValueId,
        visiting: &mut FxHashSet<ValueId>,
    ) -> Option<i64> {
        if self.derived_values.contains(&lhs) {
            let lhs = self.derived_const_offset_impl(lhs, visiting)?;
            let rhs = i64::from(value_imm_u32(self.function, rhs)?);
            lhs.checked_add(rhs)
        } else if self.derived_values.contains(&rhs) {
            let lhs = i64::from(value_imm_u32(self.function, lhs)?);
            let rhs = self.derived_const_offset_impl(rhs, visiting)?;
            lhs.checked_add(rhs)
        } else {
            None
        }
    }

    fn values_are_not_derived<const N: usize>(&self, values: [ValueId; N]) -> bool {
        values
            .into_iter()
            .all(|value| !self.derived_values.contains(&value))
    }

    fn static_overflow_predicate_is_false(
        &self,
        lhs: ValueId,
        rhs: ValueId,
        alloc_size_bytes: u32,
    ) -> Option<()> {
        if !self.value_is_add_of_base(lhs, rhs) {
            return None;
        }

        let offset = u32::try_from(self.derived_const_offset(lhs)?).ok()?;
        (offset <= alloc_size_bytes).then_some(())
    }

    fn inst_derives_address(&self, inst: InstId) -> bool {
        matches!(
            self.resolve(inst),
            EvmInstKind::Bitcast(_)
                | EvmInstKind::IntToPtr(_)
                | EvmInstKind::PtrToInt(_)
                | EvmInstKind::Gep(_)
                | EvmInstKind::Add(_)
                | EvmInstKind::Sub(_)
                | EvmInstKind::Phi(_)
                | EvmInstKind::Uaddo(_)
                | EvmInstKind::Saddo(_)
                | EvmInstKind::Usubo(_)
                | EvmInstKind::Ssubo(_)
        )
    }

    fn checked_overflow_flag(&self, inst: InstId) -> Option<ValueId> {
        match self.resolve(inst) {
            EvmInstKind::Uaddo(_)
            | EvmInstKind::Saddo(_)
            | EvmInstKind::Usubo(_)
            | EvmInstKind::Ssubo(_) => self.function.dfg.inst_results(inst).get(1).copied(),
            _ => None,
        }
    }

    fn checked_overflow_flag_is_private_control(&self, flag: ValueId) -> Option<bool> {
        let mut used = false;
        for block in self.function.layout.iter_block() {
            for user in self.function.layout.iter_inst(block) {
                if !self.inst_uses_value(user, flag) {
                    continue;
                }

                used = true;
                let EvmInstKind::Br(br) = self.resolve(user) else {
                    return None;
                };
                if br.cond() != &flag
                    || self
                        .function
                        .dfg
                        .inst(user)
                        .collect_values()
                        .iter()
                        .any(|value| self.derived_values.contains(value))
                {
                    return None;
                }
            }
        }
        Some(used)
    }

    fn address_overflow_predicate_requires_exact_heap_base(
        &self,
        inst: InstId,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Option<bool> {
        (self.value_is_add_of_base(lhs, rhs) && self.inst_result_uses_are_private_branches(inst))
            .then_some(true)
    }

    fn value_is_add_of_base(&self, value: ValueId, base: ValueId) -> bool {
        if !self.derived_values.contains(&value) || !self.derived_values.contains(&base) {
            return false;
        }

        let Some(Value::Inst { inst, .. }) = self.function.dfg.get_value(value) else {
            return false;
        };
        let EvmInstKind::Add(add) = self.resolve(*inst) else {
            return false;
        };

        (*add.lhs() == base && self.function.dfg.value_is_imm(*add.rhs()))
            || (*add.rhs() == base && self.function.dfg.value_is_imm(*add.lhs()))
    }

    fn inst_result_uses_are_private_branches(&self, inst: InstId) -> bool {
        let [result] = self.function.dfg.inst_results(inst) else {
            return false;
        };

        for block in self.function.layout.iter_block() {
            for user in self.function.layout.iter_inst(block) {
                if user == inst || !self.inst_uses_value(user, *result) {
                    continue;
                }

                let EvmInstKind::Br(br) = self.resolve(user) else {
                    return false;
                };
                if br.cond() != result {
                    return false;
                }
            }
        }

        true
    }

    fn inst_uses_derived_value(&self, inst: InstId) -> bool {
        self.function
            .dfg
            .inst(inst)
            .collect_values()
            .iter()
            .any(|value| self.derived_values.contains(value))
    }

    fn is_derived_value(&self, value: ValueId) -> bool {
        self.derived_values.contains(&value)
    }

    fn value_is_used(&self, value: ValueId) -> bool {
        self.function.layout.iter_block().any(|block| {
            self.function
                .layout
                .iter_inst(block)
                .any(|inst| self.inst_uses_value(inst, value))
        })
    }

    fn inst_uses_value(&self, inst: InstId, value: ValueId) -> bool {
        self.function
            .dfg
            .inst(inst)
            .collect_values()
            .contains(&value)
    }

    fn resolve(&self, inst: InstId) -> EvmInstKind<'_> {
        self.isa
            .inst_set()
            .resolve_inst(self.function.dfg.inst(inst))
    }
}

fn malloc_private_uses_are_compatible_with_fixed_base(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    malloc: InstId,
    exact_heap_base: bool,
) -> bool {
    PrivateMallocUseAnalysis::new(function, module, isa, malloc)
        .analyze_private_address_uses()
        .is_some_and(|info| !info.requires_exact_heap_base || exact_heap_base)
}

fn compute_program_free_ptr_slot_facts(
    module: &Module,
    schedule: &CallGraphSchedule,
    backend: &EvmBackend,
    analyses: &FxHashMap<FuncRef, FuncPreAnalysis>,
) -> (bool, FxHashMap<FuncRef, bool>) {
    let local_facts: FxHashMap<_, _> = schedule
        .funcs()
        .iter()
        .copied()
        .map(|func| {
            let analysis = expect_func_entry(analyses, func, "pre-analysis");
            let facts = module.func_store.view(func, |function| {
                function_free_ptr_slot_facts(function, backend, &analysis.prov.value)
            });
            (func, facts)
        })
        .collect();
    let local_writes = local_facts
        .iter()
        .map(|(&func, facts)| (func, facts.writes))
        .collect();

    (
        local_facts.values().any(|facts| facts.touches),
        compute_free_ptr_write_summaries(schedule, &local_writes),
    )
}

fn backend_spill_reserve_abs_words(
    func_plan: &memory_plan::SemanticFuncPlan,
    reserve: BackendSpillReserve,
) -> u32 {
    let scratch_end = if reserve.scratch_words == 0 {
        0
    } else {
        func_plan.scratch_words
    };
    let stable_end = match func_plan.stable_mode {
        StableMode::StableAbs { base_word } if reserve.stable_words != 0 => base_word
            .checked_add(func_plan.stable_words)
            .expect("backend stable reserve end overflow"),
        StableMode::None | StableMode::DynamicFrame | StableMode::StableAbs { .. } => 0,
    };

    scratch_end.max(stable_end)
}

fn compute_entry_may_have_live_frame(
    schedule: &CallGraphSchedule,
    semantic_plan: &memory_plan::ProgramMemoryPlan,
) -> FxHashMap<FuncRef, bool> {
    // A function may be entered while a dynamic frame is live iff some
    // transitive caller uses a dynamic frame. One forward-topo pass over the
    // condensation; a cyclic SCC with a dyn-frame member marks all members.
    let scc_uses_dyn_frame = |scc_ref| {
        schedule.members(scc_ref).iter().any(|func| {
            semantic_plan
                .funcs
                .get(func)
                .is_some_and(memory_plan::SemanticFuncPlan::uses_dynamic_frame)
        })
    };

    let mut incoming_live: FxHashMap<SccRef, bool> = FxHashMap::default();
    let mut entry_may_have_live_frame: FxHashMap<FuncRef, bool> = FxHashMap::default();
    for &scc_ref in &schedule.topo {
        let members_use_dyn_frame = scc_uses_dyn_frame(scc_ref);
        let live = incoming_live.get(&scc_ref).copied().unwrap_or(false)
            || (schedule.sccs.scc_info(scc_ref).is_cycle && members_use_dyn_frame);
        for &func in schedule.members(scc_ref) {
            entry_may_have_live_frame.insert(func, live);
        }
        if live || members_use_dyn_frame {
            for callee_scc in schedule.scc_edges.get(&scc_ref).into_iter().flatten() {
                incoming_live.insert(*callee_scc, true);
            }
        }
    }

    entry_may_have_live_frame
}

fn malloc_min_base(
    func_plan: &memory_plan::SemanticFuncPlan,
    global_dyn_base: u32,
    backend_spill_reserve_peak: u32,
    inst: InstId,
) -> u32 {
    let dyn_base_words = global_dyn_base
        .checked_sub(func_plan.arena_base)
        .expect("global dynamic base below arena base")
        / WORD_BYTES;
    let mut future_words = func_plan
        .malloc_future_abs_words
        .get(&inst)
        .copied()
        .unwrap_or(dyn_base_words)
        .max(func_plan.return_escape_caller_abs_words)
        .max(backend_spill_reserve_peak);
    let escape_kinds = func_plan
        .malloc_escape_kinds
        .get(&inst)
        .copied()
        .unwrap_or_default();
    if escape_kinds.has_global_or_unknown() {
        future_words = future_words.max(dyn_base_words.max(backend_spill_reserve_peak));
    }

    func_plan
        .arena_base
        .checked_add(
            WORD_BYTES
                .checked_mul(future_words)
                .expect("malloc minimum base overflow"),
        )
        .expect("malloc minimum base overflow")
}

#[cfg(test)]
mod tests {
    use rustc_hash::{FxHashMap, FxHashSet};
    use sonatina_ir::InstId;

    use super::*;
    use crate::isa::evm::{STATIC_BASE, malloc_plan::MallocEscapeKind};

    fn mem_plan_for_malloc(escape_kinds: MallocEscapeKind) -> memory_plan::SemanticFuncPlan {
        let malloc = InstId::from_u32(7);
        let mut malloc_future_abs_words = FxHashMap::default();
        malloc_future_abs_words.insert(malloc, 1);
        let mut malloc_escape_kinds = FxHashMap::default();
        malloc_escape_kinds.insert(malloc, escape_kinds);

        memory_plan::SemanticFuncPlan {
            arena_base: STATIC_BASE,
            scratch_words: 0,
            stable_words: 0,
            stable_mode: memory_plan::StableMode::None,
            entry_abs_words: 0,
            obj_loc: FxHashMap::default(),
            alloca_loc: FxHashMap::default(),
            call_preserve: FxHashMap::default(),
            malloc_future_abs_words,
            transient_mallocs: FxHashSet::default(),
            malloc_escape_kinds,
            return_escape_caller_abs_words: 10,
        }
    }

    #[test]
    fn local_malloc_honors_caller_clamp() {
        let malloc = InstId::from_u32(7);
        let min_base = malloc_min_base(
            &mem_plan_for_malloc(MallocEscapeKind::default()),
            STATIC_BASE + WORD_BYTES,
            0,
            malloc,
        );

        assert_eq!(min_base, STATIC_BASE + 10 * WORD_BYTES);
    }

    #[test]
    fn global_or_unknown_escaping_malloc_honors_caller_clamp() {
        let malloc = InstId::from_u32(7);
        let min_base = malloc_min_base(
            &mem_plan_for_malloc(MallocEscapeKind::UNKNOWN),
            STATIC_BASE + WORD_BYTES,
            0,
            malloc,
        );

        assert_eq!(min_base, STATIC_BASE + 10 * WORD_BYTES);
    }

    #[test]
    fn local_malloc_honors_backend_spill_reserve() {
        let malloc = InstId::from_u32(7);
        let min_base = malloc_min_base(
            &mem_plan_for_malloc(MallocEscapeKind::default()),
            STATIC_BASE + WORD_BYTES,
            16,
            malloc,
        );

        assert_eq!(min_base, STATIC_BASE + 16 * WORD_BYTES);
    }
}
