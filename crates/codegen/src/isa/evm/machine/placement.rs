use cranelift_entity::SecondaryMap;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, InstId, InstSetExt, Module,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::FuncRef,
};

use crate::module_analysis::CallGraph;

use super::{
    super::{
        EvmBackend, heap_plan, malloc_plan,
        mem_effects::compute_func_mem_effects,
        memory_plan::{self, BackendSpillReserve, FuncPreAnalysis, ObjLoc, StableMode, WORD_BYTES},
        prepare::{
            ArenaBaseFacts, choose_arena_base, compute_return_escape_caller_clamp_words,
            function_free_ptr_slot_facts,
        },
        ptr_escape::PtrEscapeSummary,
    },
    free_ptr_floor::{compute_free_ptr_floor_before_malloc, compute_free_ptr_write_summaries},
};

#[derive(Clone, Debug)]
pub(crate) struct EvmMemoryPlacementPlan {
    pub(crate) arena_base: u32,
    pub(crate) global_dyn_base: u32,
    pub(crate) scratch_peak_words: u32,
    pub(crate) static_chain_peak_words: u32,
    pub(crate) funcs: FxHashMap<FuncRef, EvmFuncPlacementPlan>,
}

#[derive(Clone, Debug)]
pub(crate) struct EvmFuncPlacementPlan {
    pub(crate) arena_base: u32,
    pub(crate) stable_mode: StableMode,
    pub(crate) stable_words: u32,
    pub(crate) mem_plan: memory_plan::FuncMemPlan,
    pub(crate) alloca_loc: FxHashMap<InstId, ObjLoc>,
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

pub(crate) fn compute_semantic_memory_placement(
    module: &Module,
    funcs: &[FuncRef],
    analyses: &FxHashMap<FuncRef, FuncPreAnalysis>,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    scratch_effects: &FxHashSet<FuncRef>,
    backend: &EvmBackend,
    backend_spill_reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
) -> EvmMemoryPlacementPlan {
    let mut semantic_plan = memory_plan::compute_semantic_program_memory_plan(
        module,
        funcs,
        analyses,
        ptr_escape,
        &backend.isa,
        &backend.arena_cost_model,
    );
    semantic_plan.apply_backend_spill_reserves(module, funcs, backend_spill_reserves);

    let mem_effects =
        compute_func_mem_effects(module, funcs, &semantic_plan, scratch_effects, &backend.isa);
    let return_escape_caller_abs_words = compute_return_escape_caller_clamp_words(
        module,
        funcs,
        &semantic_plan,
        &FxHashMap::default(),
    );

    let mut annotations: Vec<_> = funcs
        .par_iter()
        .copied()
        .map(|func| {
            let analysis = analyses
                .get(&func)
                .unwrap_or_else(|| panic!("missing pre-analysis for func {}", func.as_u32()));
            let (malloc_escape_kinds, transient_mallocs) =
                module.func_store.view(func, |function| {
                    let escape_kinds = malloc_plan::compute_malloc_escape_kinds_for_function(
                        function,
                        &module.ctx,
                        &backend.isa,
                        ptr_escape,
                    );
                    let transient = malloc_plan::compute_transient_mallocs(
                        function,
                        &module.ctx,
                        &backend.isa,
                        ptr_escape,
                        Some(&mem_effects),
                        &analysis.inst_liveness,
                    );
                    (escape_kinds, transient)
                });
            (
                func,
                malloc_escape_kinds,
                transient_mallocs,
                return_escape_caller_abs_words
                    .get(&func)
                    .copied()
                    .unwrap_or(0),
            )
        })
        .collect();
    annotations.sort_unstable_by_key(|(func, ..)| func.as_u32());
    for (func, malloc_escape_kinds, transient_mallocs, return_escape_caller_abs_words) in
        annotations
    {
        if let Some(func_plan) = semantic_plan.funcs.get_mut(&func) {
            func_plan.malloc_escape_kinds = malloc_escape_kinds;
            func_plan.transient_mallocs = transient_mallocs;
            func_plan.return_escape_caller_abs_words = return_escape_caller_abs_words;
        }
    }
    let has_dynamic_frames = semantic_plan
        .funcs
        .values()
        .any(memory_plan::FuncMemPlan::uses_dynamic_frame);
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
    let entry_may_have_live_frame =
        compute_entry_may_have_live_frame(module, funcs, &semantic_plan);

    let arena_base = choose_arena_base(
        module,
        funcs,
        backend,
        ptr_escape,
        ArenaBaseFacts {
            has_dynamic_frames,
            has_stackify_scratch_spills: !scratch_effects.is_empty(),
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
        funcs,
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

    let (free_ptr_slot_may_be_touched, free_ptr_write_summaries) =
        compute_program_free_ptr_slot_facts(module, funcs, backend, ptr_escape);
    let placement_ctx = MallocPlacementCtx {
        isa: &backend.isa,
        global_dyn_base: semantic_plan.global_dyn_base,
        backend_spill_reserve_peak: backend_spill_scratch_reserve_peak,
        entry_may_have_live_frame: &entry_may_have_live_frame,
        has_persistent_mallocs,
        free_ptr_slot_may_be_touched,
    };
    let func_placements = funcs
        .iter()
        .copied()
        .map(|func| {
            let func_plan = semantic_plan
                .funcs
                .get(&func)
                .unwrap_or_else(|| panic!("missing semantic plan for func {}", func.as_u32()));
            let (malloc_placements, free_ptr_floor_before_malloc) =
                module.func_store.view(func, |function| {
                    let malloc_placements =
                        placement_ctx.compute_func_malloc_placements(function, func, func_plan);
                    let free_ptr_floor_before_malloc = compute_free_ptr_floor_before_malloc(
                        function,
                        &module.ctx,
                        backend,
                        ptr_escape,
                        backend.isa.inst_set(),
                        &malloc_placements,
                        &free_ptr_write_summaries,
                    );
                    (malloc_placements, free_ptr_floor_before_malloc)
                });
            (
                func,
                EvmFuncPlacementPlan {
                    arena_base: func_plan.arena_base,
                    stable_mode: func_plan.stable_mode,
                    stable_words: func_plan.stable_words,
                    mem_plan: machine_mem_plan_from_semantic(func_plan),
                    alloca_loc: func_plan.alloca_loc.clone(),
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
        static_chain_peak_words: semantic_plan.static_chain_peak_words,
        funcs: func_placements,
    }
}

struct MallocPlacementCtx<'a> {
    isa: &'a Evm,
    global_dyn_base: u32,
    backend_spill_reserve_peak: u32,
    entry_may_have_live_frame: &'a FxHashMap<FuncRef, bool>,
    has_persistent_mallocs: bool,
    free_ptr_slot_may_be_touched: bool,
}

impl MallocPlacementCtx<'_> {
    fn compute_func_malloc_placements(
        &self,
        function: &Function,
        func: FuncRef,
        func_plan: &memory_plan::FuncMemPlan,
    ) -> FxHashMap<InstId, MallocPlacement> {
        let mut out = FxHashMap::default();
        let needs_dyn_sp_clamp = func_plan.uses_dynamic_frame()
            || self
                .entry_may_have_live_frame
                .get(&func)
                .copied()
                .unwrap_or(false);
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
                let placement = if transient
                    && !needs_dyn_sp_clamp
                    && !self.has_persistent_mallocs
                    && !self.free_ptr_slot_may_be_touched
                {
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

fn compute_program_free_ptr_slot_facts(
    module: &Module,
    funcs: &[FuncRef],
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) -> (bool, FxHashMap<FuncRef, bool>) {
    let local_facts: FxHashMap<_, _> = funcs
        .iter()
        .copied()
        .map(|func| {
            let facts = module.func_store.view(func, |function| {
                function_free_ptr_slot_facts(function, &module.ctx, backend, ptr_escape)
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
        compute_free_ptr_write_summaries(module, funcs, &local_writes, &backend.isa),
    )
}

fn machine_mem_plan_from_semantic(
    func_plan: &memory_plan::FuncMemPlan,
) -> memory_plan::FuncMemPlan {
    let mut mem_plan = func_plan.clone();
    mem_plan.alloca_loc.clear();
    mem_plan.spill_obj = SecondaryMap::new();
    mem_plan.malloc_future_abs_words.clear();
    mem_plan.transient_mallocs.clear();
    mem_plan.malloc_escape_kinds.clear();
    mem_plan
}

fn backend_spill_reserve_abs_words(
    func_plan: &memory_plan::FuncMemPlan,
    reserve: BackendSpillReserve,
) -> u32 {
    let scratch_end = if reserve.scratch_words == 0 {
        0
    } else {
        func_plan.scratch_words
    };
    let stable_end = match func_plan.stable_mode {
        StableMode::StaticAbs { base_word } if reserve.stable_words != 0 => base_word
            .checked_add(func_plan.stable_words)
            .expect("backend stable reserve end overflow"),
        StableMode::None | StableMode::DynamicFrame | StableMode::StaticAbs { .. } => 0,
    };

    scratch_end.max(stable_end)
}

fn compute_entry_may_have_live_frame(
    module: &Module,
    funcs: &[FuncRef],
    semantic_plan: &memory_plan::ProgramMemoryPlan,
) -> FxHashMap<FuncRef, bool> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let mut entry_may_have_live_frame: FxHashMap<FuncRef, bool> =
        funcs.iter().copied().map(|func| (func, false)).collect();

    let mut changed = true;
    while changed {
        changed = false;
        for &caller in funcs {
            let caller_uses_dynamic_frame = semantic_plan
                .funcs
                .get(&caller)
                .is_some_and(memory_plan::FuncMemPlan::uses_dynamic_frame);
            let caller_live = entry_may_have_live_frame
                .get(&caller)
                .copied()
                .unwrap_or(false);
            if !caller_uses_dynamic_frame && !caller_live {
                continue;
            }

            for &callee in call_graph.callee_of(caller) {
                if funcs_set.contains(&callee)
                    && !entry_may_have_live_frame
                        .get(&callee)
                        .copied()
                        .unwrap_or(false)
                {
                    entry_may_have_live_frame.insert(callee, true);
                    changed = true;
                }
            }
        }
    }

    entry_may_have_live_frame
}

fn malloc_min_base(
    func_plan: &memory_plan::FuncMemPlan,
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

    fn mem_plan_for_malloc(escape_kinds: MallocEscapeKind) -> memory_plan::FuncMemPlan {
        let malloc = InstId::from_u32(7);
        let mut malloc_future_abs_words = FxHashMap::default();
        malloc_future_abs_words.insert(malloc, 1);
        let mut malloc_escape_kinds = FxHashMap::default();
        malloc_escape_kinds.insert(malloc, escape_kinds);

        memory_plan::FuncMemPlan {
            arena_base: STATIC_BASE,
            scratch_words: 0,
            stable_words: 0,
            stable_mode: memory_plan::StableMode::None,
            entry_abs_words: 0,
            obj_loc: FxHashMap::default(),
            alloca_loc: FxHashMap::default(),
            spill_obj: SecondaryMap::new(),
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
