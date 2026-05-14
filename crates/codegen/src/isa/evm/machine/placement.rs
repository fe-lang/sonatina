use cranelift_entity::SecondaryMap;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    InstId, InstSetExt, Module,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::FuncRef,
};

use super::{
    super::{
        EvmBackend, heap_plan, malloc_plan,
        mem_effects::compute_func_mem_effects,
        memory_plan::{self, FuncPreAnalysis, ObjLoc, StableMode, WORD_BYTES},
        prepare::{
            ArenaBaseFacts, choose_arena_base, compute_return_escape_caller_clamp_words,
            function_may_touch_free_ptr_slot, function_may_write_free_ptr_slot,
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
    backend_spill_reserve_words: &FxHashMap<FuncRef, u32>,
) -> EvmMemoryPlacementPlan {
    let mut semantic_plan = memory_plan::compute_semantic_program_memory_plan(
        module,
        funcs,
        analyses,
        ptr_escape,
        &backend.isa,
        &backend.arena_cost_model,
    );

    let mem_effects =
        compute_func_mem_effects(module, funcs, &semantic_plan, scratch_effects, &backend.isa);
    let return_escape_caller_abs_words = compute_return_escape_caller_clamp_words(
        module,
        funcs,
        &semantic_plan,
        backend_spill_reserve_words,
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
    for (&func, &reserve_words) in backend_spill_reserve_words {
        if let Some(func_plan) = semantic_plan.funcs.get_mut(&func)
            && func_plan.uses_dynamic_frame()
        {
            func_plan.stable_words = func_plan
                .stable_words
                .checked_add(reserve_words)
                .expect("dynamic frame backend spill reserve overflow");
        }
    }

    let has_dynamic_frames = semantic_plan
        .funcs
        .values()
        .any(memory_plan::FuncMemPlan::uses_dynamic_frame);
    let backend_spill_reserve_peak = backend_spill_reserve_words
        .values()
        .copied()
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

    let arena_base = choose_arena_base(
        module,
        funcs,
        backend,
        ptr_escape,
        ArenaBaseFacts {
            has_dynamic_frames,
            has_stackify_scratch_spills: false,
            backend_spill_reserve_words: backend_spill_reserve_peak,
            has_persistent_mallocs,
        },
    );
    if has_dynamic_frames {
        semantic_plan.scratch_peak_words = semantic_plan
            .scratch_peak_words
            .max(backend_spill_reserve_peak);
    }
    semantic_plan.set_arena_base(arena_base);

    let mut malloc_bounds = heap_plan::compute_semantic_malloc_future_abs_words_with_extra(
        module,
        funcs,
        &semantic_plan,
        analyses,
        &backend.isa,
        backend_spill_reserve_words,
    );
    for (&func, &reserve_words) in backend_spill_reserve_words {
        if let Some(bounds) = malloc_bounds.get_mut(&func) {
            for bound in bounds.values_mut() {
                *bound = (*bound).max(reserve_words);
            }
        }
    }
    for (func, bounds) in malloc_bounds {
        if let Some(func_plan) = semantic_plan.funcs.get_mut(&func) {
            func_plan.malloc_future_abs_words = bounds;
        }
    }

    let local_free_ptr_touches: FxHashMap<FuncRef, bool> = funcs
        .iter()
        .copied()
        .map(|func| {
            let touches = module.func_store.view(func, |function| {
                function_may_touch_free_ptr_slot(function, &module.ctx, backend, ptr_escape)
            });
            (func, touches)
        })
        .collect();
    let free_ptr_slot_may_be_touched = local_free_ptr_touches.values().copied().any(|touch| touch);
    let local_free_ptr_writes: FxHashMap<FuncRef, bool> = funcs
        .iter()
        .copied()
        .map(|func| {
            let writes = module.func_store.view(func, |function| {
                function_may_write_free_ptr_slot(function, &module.ctx, backend, ptr_escape)
            });
            (func, writes)
        })
        .collect();
    let free_ptr_write_summaries =
        compute_free_ptr_write_summaries(module, funcs, &local_free_ptr_writes, &backend.isa);

    let mut func_placements: FxHashMap<FuncRef, EvmFuncPlacementPlan> = FxHashMap::default();
    for &func in funcs {
        let func_plan = semantic_plan
            .funcs
            .get(&func)
            .unwrap_or_else(|| panic!("missing semantic plan for func {}", func.as_u32()));
        let (malloc_placements, free_ptr_floor_before_malloc) =
            module.func_store.view(func, |function| {
                let ctx = MallocPlacementCtx {
                    isa: &backend.isa,
                    func_plan,
                    global_dyn_base: semantic_plan.global_dyn_base,
                    backend_spill_reserve_peak,
                    has_dynamic_frames,
                    has_persistent_mallocs,
                    free_ptr_slot_may_be_touched,
                };
                let malloc_placements = compute_func_malloc_placements(function, &ctx);
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
        func_placements.insert(
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
        );
    }

    EvmMemoryPlacementPlan {
        arena_base: semantic_plan.arena_base,
        global_dyn_base: semantic_plan.global_dyn_base,
        scratch_peak_words: semantic_plan.scratch_peak_words,
        static_chain_peak_words: semantic_plan.static_chain_peak_words,
        funcs: func_placements,
    }
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

struct MallocPlacementCtx<'a> {
    isa: &'a Evm,
    func_plan: &'a memory_plan::FuncMemPlan,
    global_dyn_base: u32,
    backend_spill_reserve_peak: u32,
    has_dynamic_frames: bool,
    has_persistent_mallocs: bool,
    free_ptr_slot_may_be_touched: bool,
}

fn compute_func_malloc_placements(
    function: &sonatina_ir::Function,
    ctx: &MallocPlacementCtx<'_>,
) -> FxHashMap<InstId, MallocPlacement> {
    let mut out = FxHashMap::default();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if !matches!(
                ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::EvmMalloc(_)
            ) {
                continue;
            }

            let transient = ctx.func_plan.transient_mallocs.contains(&inst);
            let needs_dyn_sp_clamp = ctx.has_dynamic_frames;
            let min_base = malloc_min_base(
                ctx.func_plan,
                ctx.global_dyn_base,
                ctx.backend_spill_reserve_peak,
                inst,
            );
            let placement = if transient
                && !needs_dyn_sp_clamp
                && !ctx.has_persistent_mallocs
                && !ctx.free_ptr_slot_may_be_touched
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
        .unwrap_or(dyn_base_words);
    let escape_kinds = func_plan
        .malloc_escape_kinds
        .get(&inst)
        .copied()
        .unwrap_or_default();
    if escape_kinds.has_global_or_unknown() {
        future_words = future_words.max(dyn_base_words.max(backend_spill_reserve_peak));
    } else if escape_kinds.is_return_only() {
        future_words = future_words.max(func_plan.return_escape_caller_abs_words);
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
