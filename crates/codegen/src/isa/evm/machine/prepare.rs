use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{Module, cfg::ControlFlowGraph, isa::evm::EvmMachine, module::FuncRef};
use tracing::{debug_span, trace_span};

use crate::{
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    liveness::{InstLiveness, Liveness},
    module_analysis::{CallGraph, SccBuilder},
    stackalloc::{
        HOT_IMMEDIATE_SIZE_MIN_BLOCK_USES, HOT_IMMEDIATE_SIZE_MIN_MATERIALIZATION_BYTES,
        StackifyBuilder,
    },
};

use super::{
    super::{
        EvmBackend, ImmediateMaterializationMode, fixed_slots,
        memory_plan::{MachineStackifyAnalysis, topo_sort_sccs},
    },
    verify::verify_machine_module,
};

pub(crate) fn prepare_machine_stackify_analyses(
    module: &Module,
    funcs: &[FuncRef],
    backend: &EvmBackend,
    machine_isa: &EvmMachine,
) -> Result<FxHashMap<FuncRef, MachineStackifyAnalysis>, String> {
    verify_machine_module(module, funcs)?;
    let _span = debug_span!("sonatina.codegen.evm.machine.prepare_stackify").entered();
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);
    let topo = topo_sort_sccs(&funcs_set, &call_graph, &scc);
    let local_scratch_clobbers = compute_local_machine_scratch_clobbers(module, funcs, machine_isa);

    let mut analyses = FxHashMap::default();
    let mut fixed_slot_effects = FxHashSet::default();
    for &scc_ref in topo.iter().rev() {
        let mut components: Vec<FuncRef> = scc
            .scc_info(scc_ref)
            .components
            .iter()
            .copied()
            .filter(|func| funcs_set.contains(func))
            .collect();
        components.sort_unstable_by_key(|func| func.as_u32());

        let cycle_fixed_slot_effects = scc.scc_info(scc_ref).is_cycle.then(|| {
            let mut cycle_fixed_slot_effects = fixed_slot_effects.clone();
            cycle_fixed_slot_effects.extend(components.iter().copied());
            cycle_fixed_slot_effects
        });
        let analysis_fixed_slot_effects = cycle_fixed_slot_effects
            .as_ref()
            .unwrap_or(&fixed_slot_effects);

        let mut scc_results: Vec<_> = components
            .par_iter()
            .copied()
            .map(|func| {
                let analysis = module.func_store.modify(func, |function| {
                    prepare_machine_stackify_analysis(
                        function,
                        backend,
                        machine_isa,
                        Some(analysis_fixed_slot_effects),
                    )
                });
                let uses_scratch_spills = analysis.alloc.uses_scratch_spills();
                (func, analysis, uses_scratch_spills)
            })
            .collect();
        scc_results.sort_unstable_by_key(|(func, _, _)| func.as_u32());

        let mut scc_uses_scratch_spills = false;
        for (func, analysis, uses_scratch_spills) in scc_results {
            scc_uses_scratch_spills |= uses_scratch_spills;
            analyses.insert(func, analysis);
        }

        let scc_touches_fixed_slots = scc_uses_scratch_spills
            || components
                .iter()
                .copied()
                .any(|func| local_scratch_clobbers.contains(&func))
            || components.iter().copied().any(|func| {
                call_graph
                    .callee_of(func)
                    .iter()
                    .copied()
                    .any(|callee| fixed_slot_effects.contains(&callee))
            });
        if scc_touches_fixed_slots {
            fixed_slot_effects.extend(components);
        }
    }

    Ok(analyses)
}

fn prepare_machine_stackify_analysis(
    function: &mut sonatina_ir::Function,
    backend: &EvmBackend,
    machine_isa: &EvmMachine,
    fixed_slot_effects: Option<&FxHashSet<FuncRef>>,
) -> MachineStackifyAnalysis {
    let _span = trace_span!("sonatina.codegen.evm.machine.prepare_stackify_func").entered();
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    let mut splitter = CriticalEdgeSplitter::new();
    splitter.run(function, &mut cfg);

    let mut dom = DomTree::new();
    dom.compute(&cfg);
    let block_order = dom.rpo().to_owned();

    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);

    let mut inst_liveness = InstLiveness::new();
    inst_liveness.compute(function, &cfg, &liveness);

    let scratch_clobber_liveness = fixed_slots::MachineFixedSlotClobberLiveness::compute(
        function,
        machine_isa,
        fixed_slot_effects,
        &inst_liveness,
    );
    let (scratch_live_values, stable_final_spill_values) = scratch_clobber_liveness.into_parts();
    let mut builder = StackifyBuilder::new(
        function,
        &cfg,
        &dom,
        &liveness,
        backend.stackify_reach_depth,
    )
    .with_search_profile(backend.stackify_search_profile)
    .with_scratch_live_values(scratch_live_values)
    .with_scratch_spills(fixed_slots::FIXED_SPILL_SLOTS)
    .with_hot_immediate_caching();

    if backend.immediate_materialization_mode == ImmediateMaterializationMode::Size {
        builder = builder
            .with_hot_immediate_min_block_uses(HOT_IMMEDIATE_SIZE_MIN_BLOCK_USES)
            .with_hot_immediate_min_materialization_bytes(
                HOT_IMMEDIATE_SIZE_MIN_MATERIALIZATION_BYTES,
            );
    }

    let (alloc, trace) = if backend.capture_stackify_trace {
        let (alloc, trace) = builder.compute_with_trace_capture();
        (alloc, Some(trace))
    } else {
        (builder.compute(), None)
    };

    MachineStackifyAnalysis {
        alloc,
        block_order,
        stable_final_spill_values,
        trace,
    }
}

fn compute_local_machine_scratch_clobbers(
    module: &Module,
    funcs: &[FuncRef],
    machine_isa: &EvmMachine,
) -> FxHashSet<FuncRef> {
    let mut local: Vec<_> = funcs
        .par_iter()
        .copied()
        .filter(|&func| {
            module.func_store.view(func, |function| {
                function.layout.iter_block().any(|block| {
                    function.layout.iter_inst(block).any(|inst| {
                        fixed_slots::machine_inst_is_fixed_slot_clobber(function, machine_isa, inst)
                    })
                })
            })
        })
        .collect();
    local.sort_unstable_by_key(|func| func.as_u32());
    local.into_iter().collect()
}
