use crate::{
    analysis::memory_access::MemoryAccessAnalysis,
    cfg_scc::CfgSccAnalysis,
    domtree::DomTree,
    isa::evm::normalize_alias_map,
    liveness::Liveness,
    stackalloc::stackify::{
        builder::{StackifyContext, StackifyReachability, StackifySearchProfile},
        templates::{
            compute_def_info, compute_dom_depth, compute_phi_out_sources, compute_phi_results,
            function_has_internal_return,
        },
    },
};
use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, Function, ValueId, cfg::ControlFlowGraph};

pub(super) fn build_stackify_test_context<'a>(
    func: &'a Function,
    cfg: &'a ControlFlowGraph,
    dom: &'a DomTree,
    liveness: &'a Liveness,
    entry: BlockId,
    scc: CfgSccAnalysis,
    reach: StackifyReachability,
) -> StackifyContext<'a> {
    let mut value_aliases: SecondaryMap<ValueId, Option<ValueId>> = SecondaryMap::new();
    for value in func.dfg.values.keys() {
        value_aliases[value] = Some(value);
    }
    normalize_alias_map(func, &mut value_aliases);

    let dom_depth = compute_dom_depth(dom, entry);
    let def_info = compute_def_info(func, entry, &value_aliases);
    let phi_results = compute_phi_results(func, &value_aliases);
    let phi_out_sources = compute_phi_out_sources(func, cfg, &value_aliases);
    let spill_slot_interference =
        crate::stackalloc::stackify::slots::SpillSlotInterference::compute(
            func,
            cfg,
            liveness,
            &phi_results,
            &value_aliases,
        );
    let mut analysis = MemoryAccessAnalysis::new();
    let mut exact_local_addr: SecondaryMap<ValueId, Option<_>> = SecondaryMap::new();
    for value in func.dfg.values.keys() {
        exact_local_addr[value] =
            analysis.exact_local_addr(func, value_aliases[value].unwrap_or(value));
    }

    StackifyContext {
        func,
        cfg,
        dom,
        liveness,
        scratch_live_values: Default::default(),
        scratch_spill_slots: 0,
        entry,
        scc,
        dom_depth,
        def_info,
        phi_results,
        phi_out_sources,
        spill_slot_interference,
        has_internal_return: function_has_internal_return(func),
        reach,
        search_profile: StackifySearchProfile::Exact,
        value_aliases,
        exact_local_addr,
    }
}
