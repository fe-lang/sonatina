use rustc_hash::{FxHashMap, FxHashSet};
use tracing::{debug_span, info_span, trace_span};

use crate::{
    analysis::func_behavior,
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    liveness::{InstLiveness, Liveness},
    machinst::lower::SectionWorkModule,
    module_analysis::{CallGraph, SccBuilder},
    stackalloc::{StackifyAlloc, StackifyBuilder},
};
use sonatina_ir::{
    Function, GlobalVariableRef, InstSetExt, Module,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::Isa,
    module::{FuncRef, ModuleCtx},
    object::EmbedSymbol,
};

use super::{
    EvmBackend, LateCleanupProfile, canonicalize_alias_value,
    dyn_sp::{FuncDynSpPlan, compute_dyn_sp_plan},
    emit::{
        LateBlockAliasPlan, compute_function_entry_jump_targets, compute_late_block_alias_plan,
        immediate_u32, rewrite_evm_local_fallthrough_layout,
    },
    heap_plan,
    lazy_frame::FrameSummary,
    malloc_plan,
    mem_effects::compute_func_mem_effects,
    memory_plan::{
        self, FREE_PTR_SLOT, FuncMemPlan, ProgramMemoryPlan, STATIC_BASE, StableMode, WORD_BYTES,
        compute_abs_clobber_words, compute_program_memory_plan, topo_sort_sccs,
    },
    pipeline::EvmPipeline,
    ptr_escape::PtrEscapeSummary,
    scratch_effects, scratch_plan,
};

pub struct EvmPreparedSection {
    work: SectionWorkModule,
    funcs: Vec<FuncRef>,
    globals: Vec<GlobalVariableRef>,
    used_embed_symbols: FxHashSet<EmbedSymbol>,
    section_plan: EvmSectionPlan,
    function_plans: FxHashMap<FuncRef, EvmFunctionPlan>,
}

impl EvmPreparedSection {
    pub fn module(&self) -> &Module {
        self.work.module()
    }

    pub fn funcs(&self) -> &[FuncRef] {
        &self.funcs
    }

    pub fn globals(&self) -> &[GlobalVariableRef] {
        &self.globals
    }

    pub fn used_embed_symbols(&self) -> &FxHashSet<EmbedSymbol> {
        &self.used_embed_symbols
    }

    pub(crate) fn function_plan(&self, func: FuncRef) -> Option<&EvmFunctionPlan> {
        self.function_plans.get(&func)
    }

    pub(crate) fn section_plan(&self) -> &EvmSectionPlan {
        &self.section_plan
    }
}

#[derive(Clone)]
pub(crate) struct EvmSectionPlan {
    pub(crate) dyn_base: u32,
    pub(crate) scratch_peak_words: u32,
    pub(crate) static_chain_peak_words: u32,
    pub(crate) has_persistent_mallocs: bool,
    pub(crate) has_explicit_free_ptr_writes: bool,
}

#[derive(Clone)]
pub(crate) struct EvmFunctionPlan {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) emitted_block_order: Vec<sonatina_ir::BlockId>,
    pub(crate) block_aliases: FxHashMap<sonatina_ir::BlockId, sonatina_ir::BlockId>,
    pub(crate) mem_plan: FuncMemPlan,
    pub(crate) frame_summary: FrameSummary,
    pub(crate) dyn_sp_plan: FuncDynSpPlan,
    pub(crate) function_entry_jumpdest: bool,
}

pub(crate) fn prepare_section(
    backend: &EvmBackend,
    work: SectionWorkModule,
) -> Result<EvmPreparedSection, String> {
    let module = work.module();
    let pipeline = EvmPipeline::new(backend);
    let _span = info_span!(
        "sonatina.codegen.evm.prepare_section",
        funcs = module.funcs().len()
    )
    .entered();
    let pipeline = pipeline.run(&work)?;
    let funcs = pipeline.funcs;
    let ptr_escape = pipeline.ptr_escape;
    let membership = work.membership();

    {
        let _span = debug_span!("sonatina.codegen.evm.func_behavior").entered();
        func_behavior::analyze_module(module);
    }

    let (analyses, scratch_effects) =
        compute_scratch_effect_analyses(module, &funcs, backend, &ptr_escape);

    let mut plan = {
        let _span = debug_span!("sonatina.codegen.evm.compute_program_memory_plan").entered();
        compute_program_memory_plan(
            module,
            &funcs,
            &analyses,
            &ptr_escape,
            &backend.isa,
            &backend.arena_cost_model,
        )
    };

    let mem_effects = {
        let _span = trace_span!("sonatina.codegen.evm.compute_func_mem_effects").entered();
        compute_func_mem_effects(module, &funcs, &plan, &scratch_effects, &backend.isa)
    };
    let return_escape_caller_abs_words = {
        let _span = trace_span!("sonatina.codegen.evm.compute_return_escape_clamps").entered();
        compute_return_escape_caller_clamp_words(module, &funcs, &plan)
    };

    for &func in &funcs {
        let _span = trace_span!(
            "sonatina.codegen.evm.annotate_mem_plan_for_func",
            func_ref = func.as_u32()
        )
        .entered();
        let analysis = analyses.get(&func).expect("missing analysis");
        let (malloc_escape_kinds, transient_mallocs) = module.func_store.view(func, |function| {
            let escape_kinds = malloc_plan::compute_malloc_escape_kinds_for_function(
                function,
                &module.ctx,
                &backend.isa,
                &ptr_escape,
            );
            let transient = malloc_plan::compute_transient_mallocs(
                function,
                &module.ctx,
                &backend.isa,
                &ptr_escape,
                Some(&mem_effects),
                &analysis.inst_liveness,
            );
            (escape_kinds, transient)
        });
        if let Some(mem_plan) = plan.funcs.get_mut(&func) {
            mem_plan.malloc_escape_kinds = malloc_escape_kinds;
            mem_plan.return_escape_caller_abs_words = return_escape_caller_abs_words
                .get(&func)
                .copied()
                .unwrap_or(0);
            mem_plan.transient_mallocs = transient_mallocs;
        }
    }

    let malloc_bounds = {
        let _span = debug_span!("sonatina.codegen.evm.compute_malloc_future_abs_words").entered();
        heap_plan::compute_malloc_future_abs_words(module, &funcs, &plan, &analyses, &backend.isa)
    };
    for (func, bounds) in malloc_bounds {
        if let Some(mem_plan) = plan.funcs.get_mut(&func) {
            mem_plan.malloc_future_abs_words = bounds;
        }
    }

    if std::env::var_os("SONATINA_EVM_MEM_DEBUG").is_some() {
        debug_print_mem_plan(module, &funcs, &plan);
    }
    let has_persistent_mallocs = {
        let _span = trace_span!("sonatina.codegen.evm.detect_persistent_mallocs").entered();
        funcs.iter().copied().any(|func| {
            let Some(mem_plan) = plan.funcs.get(&func) else {
                return false;
            };
            module.func_store.view(func, |function| {
                function.layout.iter_block().any(|block| {
                    function.layout.iter_inst(block).any(|inst| {
                        matches!(
                            backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                            EvmInstKind::EvmMalloc(_)
                        ) && !mem_plan.transient_mallocs.contains(&inst)
                    })
                })
            })
        })
    };
    let has_explicit_free_ptr_writes = {
        let _span = trace_span!("sonatina.codegen.evm.detect_explicit_free_ptr_writes").entered();
        funcs.iter().copied().any(|func| {
            module.func_store.view(func, |function| {
                function.layout.iter_block().any(|block| {
                    function.layout.iter_inst(block).any(|inst| {
                        match backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
                            EvmInstKind::Mstore(mstore) => function
                                .dfg
                                .value_imm(*mstore.addr())
                                .and_then(immediate_u32)
                                .is_some_and(|addr| addr == u32::from(FREE_PTR_SLOT)),
                            EvmInstKind::EvmMstore8(mstore8) => function
                                .dfg
                                .value_imm(*mstore8.addr())
                                .and_then(immediate_u32)
                                .is_some_and(|addr| addr == u32::from(FREE_PTR_SLOT)),
                            _ => false,
                        }
                    })
                })
            })
        })
    };

    let section_entry = work.entry();
    let function_entry_jump_targets = {
        let _span =
            trace_span!("sonatina.codegen.evm.compute_function_entry_jump_targets").entered();
        compute_function_entry_jump_targets(module, &funcs)
    };
    let dyn_sp_plan = {
        let _span = trace_span!("sonatina.codegen.evm.compute_dyn_sp_plan").entered();
        compute_dyn_sp_plan(
            module,
            &funcs,
            section_entry,
            &plan,
            &analyses,
            &backend.isa,
        )
    };
    let has_dynamic_frames = plan.funcs.values().any(FuncMemPlan::uses_dynamic_frame);

    let section_plan = EvmSectionPlan {
        dyn_base: plan.global_dyn_base,
        scratch_peak_words: plan.scratch_peak_words,
        static_chain_peak_words: plan.static_chain_peak_words,
        has_persistent_mallocs,
        has_explicit_free_ptr_writes,
    };
    let function_plans = {
        let _span = trace_span!("sonatina.codegen.evm.extract_lowering_state").entered();
        let mut function_plans = FxHashMap::default();
        for (func, analysis) in analyses {
            let mem_plan = plan
                .funcs
                .get(&func)
                .cloned()
                .ok_or_else(|| format!("missing memory plan for func {}", func.as_u32()))?;
            let frame_summary = dyn_sp_plan
                .frame_summaries
                .get(&func)
                .cloned()
                .unwrap_or_default();
            let func_dyn_sp_plan = FuncDynSpPlan {
                entry_init: func == section_entry && dyn_sp_plan.entry_init,
                frontier_init_calls: dyn_sp_plan
                    .frontier_init_calls
                    .get(&func)
                    .cloned()
                    .unwrap_or_default(),
                checked_frontier_init_calls: dyn_sp_plan
                    .checked_frontier_init_calls
                    .get(&func)
                    .cloned()
                    .unwrap_or_default(),
                entry_live_frame: dyn_sp_plan
                    .entry_live_frame
                    .get(&func)
                    .copied()
                    .unwrap_or(false),
            };
            let alias_plan = module.func_store.view(func, |function| {
                compute_late_block_alias_plan(
                    function,
                    &analysis.alloc,
                    &frame_summary,
                    &analysis.block_order,
                )
            });
            let LateBlockAliasPlan {
                aliases: block_aliases,
                emitted_block_order,
            } = alias_plan;
            let emitted_block_order = if backend.late_cleanup_profile != LateCleanupProfile::Off {
                module.func_store.view(func, |function| {
                    rewrite_evm_local_fallthrough_layout(
                        function,
                        &block_aliases,
                        emitted_block_order,
                    )
                })
            } else {
                emitted_block_order
            };
            function_plans.insert(
                func,
                EvmFunctionPlan {
                    alloc: analysis.alloc,
                    emitted_block_order,
                    block_aliases,
                    mem_plan,
                    frame_summary,
                    dyn_sp_plan: func_dyn_sp_plan,
                    function_entry_jumpdest: function_entry_jump_targets.contains(&func),
                },
            );
        }
        function_plans
    };

    let _span = debug_span!(
        "sonatina.codegen.evm.prepare_section_summary",
        has_dynamic_frames,
        has_persistent_mallocs,
        has_explicit_free_ptr_writes
    )
    .entered();
    let mut globals: Vec<_> = membership.globals.iter().copied().collect();
    globals.sort_unstable();
    Ok(EvmPreparedSection {
        work,
        funcs,
        globals,
        used_embed_symbols: membership.used_embed_symbols,
        section_plan,
        function_plans,
    })
}

pub(crate) fn compute_return_escape_caller_clamp_words(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
) -> FxHashMap<FuncRef, u32> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let abs_clobber_words = compute_abs_clobber_words(module, funcs, plan);

    let mut callers: FxHashMap<FuncRef, FxHashSet<FuncRef>> = FxHashMap::default();
    let mut clamp_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for &func in funcs {
        clamp_words.insert(func, 0);
    }

    for &caller in funcs {
        module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(call) = function.dfg.call_info(inst) else {
                        continue;
                    };
                    let callee = call.callee();
                    if funcs_set.contains(&callee) {
                        callers.entry(callee).or_default().insert(caller);
                    }
                }
            }
        });
    }

    let mut changed = true;
    while changed {
        changed = false;

        for &func in funcs {
            let mut next = clamp_words.get(&func).copied().unwrap_or(0);
            for caller in callers.get(&func).into_iter().flatten() {
                let caller_clobber_words = abs_clobber_words
                    .get(caller)
                    .copied()
                    .or_else(|| plan.funcs.get(caller).map(FuncMemPlan::active_abs_words))
                    .unwrap_or(0);
                let caller_transitive_words = clamp_words.get(caller).copied().unwrap_or(0);
                next = next.max(caller_clobber_words.max(caller_transitive_words));
            }

            let cur = clamp_words.get(&func).copied().unwrap_or(0);
            if next > cur {
                clamp_words.insert(func, next);
                changed = true;
            }
        }
    }

    clamp_words
}

pub(crate) fn prepare_free_ptr_restore(
    function: &mut Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) {
    let _span = trace_span!("sonatina.codegen.evm.prepare_free_ptr_restore").entered();
    let mut did_insert = false;
    loop {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);

        let mut splitter = CriticalEdgeSplitter::new();
        splitter.run(function, &mut cfg);

        let mut liveness = Liveness::new();
        liveness.compute(function, &cfg);

        let mut inst_liveness = InstLiveness::new();
        inst_liveness.compute(function, &cfg, &liveness);

        let transient_mallocs = malloc_plan::compute_transient_mallocs(
            function,
            module,
            &backend.isa,
            ptr_escape,
            None,
            &inst_liveness,
        );

        if !did_insert
            && malloc_plan::should_restore_free_ptr_on_internal_returns(
                function,
                module,
                &backend.isa,
                ptr_escape,
                &transient_mallocs,
            )
        {
            malloc_plan::insert_free_ptr_restore_on_internal_returns(function, &backend.isa);
            did_insert = true;
            continue;
        }

        break;
    }
}

fn prepare_stackify_analysis(
    function: &mut Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    scratch_effects: Option<&FxHashSet<FuncRef>>,
) -> memory_plan::FuncAnalysis {
    let _span = trace_span!("sonatina.codegen.evm.prepare_stackify_analysis").entered();
    let mut cfg = ControlFlowGraph::new();
    {
        let _span = trace_span!("sonatina.codegen.evm.stackify.compute_cfg").entered();
        cfg.compute(function);
    }

    {
        let _span = trace_span!("sonatina.codegen.evm.stackify.split_critical_edges").entered();
        let mut splitter = CriticalEdgeSplitter::new();
        splitter.run(function, &mut cfg);
    }

    let (dom, block_order) = {
        let _span = trace_span!("sonatina.codegen.evm.stackify.compute_domtree").entered();
        let mut dom = DomTree::new();
        dom.compute(&cfg);
        let block_order = dom.rpo().to_owned();
        (dom, block_order)
    };

    let inst_liveness = {
        let _span = trace_span!("sonatina.codegen.evm.stackify.compute_liveness").entered();
        let mut liveness = Liveness::new();
        liveness.compute(function, &cfg);

        let mut inst_liveness = InstLiveness::new();
        inst_liveness.compute(function, &cfg, &liveness);
        inst_liveness
    };

    let (value_aliases, stack_liveness, canonical_scratch_live_values) = {
        let _span = trace_span!("sonatina.codegen.evm.stackify.canonicalize_aliases").entered();
        let value_aliases = backend.compute_stackify_value_aliases(function, module);

        let mut stack_liveness = Liveness::new();
        stack_liveness.compute_with_value_normalizer(function, &cfg, |v| {
            canonicalize_alias_value(&value_aliases, v)
        });

        let scratch_live_values = scratch_plan::compute_scratch_live_values(
            function,
            module,
            &backend.isa,
            ptr_escape,
            scratch_effects,
            &inst_liveness,
        );
        let mut canonical_scratch_live_values = crate::bitset::BitSet::default();
        for v in scratch_live_values.iter() {
            canonical_scratch_live_values.insert(canonicalize_alias_value(&value_aliases, v));
        }
        (value_aliases, stack_liveness, canonical_scratch_live_values)
    };

    let alloc = {
        let _span = trace_span!("sonatina.codegen.evm.stackify.compute_alloc").entered();
        StackifyBuilder::new(
            function,
            &cfg,
            &dom,
            &stack_liveness,
            backend.stackify_reach_depth,
        )
        .with_scratch_live_values(canonical_scratch_live_values)
        .with_scratch_spills(scratch_plan::SCRATCH_SPILL_SLOTS)
        .with_value_aliases(&value_aliases)
        .compute()
    };

    memory_plan::FuncAnalysis {
        alloc,
        inst_liveness,
        block_order,
        value_aliases,
    }
}

fn compute_scratch_effect_analyses(
    module: &Module,
    funcs: &[FuncRef],
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) -> (
    FxHashMap<FuncRef, memory_plan::FuncAnalysis>,
    FxHashSet<FuncRef>,
) {
    let _span = debug_span!("sonatina.codegen.evm.compute_scratch_effect_analyses").entered();
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);
    let topo = topo_sort_sccs(&funcs_set, &call_graph, &scc);
    let local_scratch_clobbers =
        scratch_effects::compute_local_scratch_clobbers(module, funcs, &backend.isa);

    let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
    let mut scratch_effects = FxHashSet::default();

    for &scc_ref in topo.iter().rev() {
        let mut components: Vec<FuncRef> = scc
            .scc_info(scc_ref)
            .components
            .iter()
            .copied()
            .filter(|func| funcs_set.contains(func))
            .collect();
        components.sort_unstable_by_key(|func| func.as_u32());

        let cycle_scratch_effects = scc.scc_info(scc_ref).is_cycle.then(|| {
            let mut cycle_scratch_effects = scratch_effects.clone();
            cycle_scratch_effects.extend(components.iter().copied());
            cycle_scratch_effects
        });
        let analysis_scratch_effects = cycle_scratch_effects.as_ref().unwrap_or(&scratch_effects);

        let mut scc_uses_scratch_spills = false;
        for func in components.iter().copied() {
            let _span = trace_span!(
                "sonatina.codegen.evm.prepare_stackify_analysis",
                func_ref = func.as_u32()
            )
            .entered();
            let analysis = module.func_store.modify(func, |function| {
                prepare_stackify_analysis(
                    function,
                    &module.ctx,
                    backend,
                    ptr_escape,
                    Some(analysis_scratch_effects),
                )
            });
            scc_uses_scratch_spills |= analysis.alloc.uses_scratch_spills();
            analyses.insert(func, analysis);
        }

        let scc_touches_scratch = scc_uses_scratch_spills
            || components
                .iter()
                .copied()
                .any(|func| local_scratch_clobbers.contains(&func))
            || components.iter().copied().any(|func| {
                call_graph
                    .callee_of(func)
                    .iter()
                    .copied()
                    .any(|callee| scratch_effects.contains(&callee))
            });
        if scc_touches_scratch {
            scratch_effects.extend(components);
        }
    }

    (analyses, scratch_effects)
}

fn debug_print_mem_plan(module: &Module, funcs: &[FuncRef], plan: &ProgramMemoryPlan) {
    let mut funcs_by_name: Vec<(String, FuncRef)> = funcs
        .iter()
        .copied()
        .map(|func| {
            (
                module.ctx.func_sig(func, |sig| sig.name().to_string()),
                func,
            )
        })
        .collect();
    funcs_by_name.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));

    eprintln!(
        "evm mem debug: global_dyn_base=0x{:x} static_base=0x{:x} scratch_peak_words={} static_chain_peak_words={}",
        plan.global_dyn_base, STATIC_BASE, plan.scratch_peak_words, plan.static_chain_peak_words
    );
    eprintln!("evm mem debug: entry_mem_init_stores=0");

    for (name, func) in funcs_by_name {
        let Some(func_plan) = plan.funcs.get(&func) else {
            continue;
        };
        let stable_mode = match func_plan.stable_mode {
            StableMode::None => "None".to_string(),
            StableMode::DynamicFrame => "DynamicFrame".to_string(),
            StableMode::StaticAbs { base_word } => format!("StaticAbs(base_word={base_word})"),
        };

        let (malloc_min, malloc_max, malloc_count) = if func_plan.malloc_future_abs_words.is_empty()
        {
            (None, None, 0)
        } else {
            let mut min = u32::MAX;
            let mut max = 0;
            for &words in func_plan.malloc_future_abs_words.values() {
                min = min.min(words);
                max = max.max(words);
            }
            (
                Some(min),
                Some(max),
                func_plan.malloc_future_abs_words.len(),
            )
        };

        let abs_end_words = func_plan.abs_words_end();
        let abs_end = (abs_end_words != 0).then(|| {
            STATIC_BASE
                .checked_add(
                    abs_end_words
                        .checked_mul(WORD_BYTES)
                        .expect("absolute end overflow"),
                )
                .expect("absolute end overflow")
        });

        eprintln!(
            "evm mem debug: {name} scratch_words={} stable_words={} stable_mode={} entry_abs_words={} abs_words_end={} malloc_bounds(min,max,count)=({:?},{:?},{malloc_count}) abs_end={:?}",
            func_plan.scratch_words,
            func_plan.stable_words,
            stable_mode,
            func_plan.entry_abs_words,
            abs_end_words,
            malloc_min,
            malloc_max,
            abs_end,
        );
    }
}
