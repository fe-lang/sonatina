use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    InstSetExt, Module,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};
use std::collections::{BTreeMap, BTreeSet};

use crate::module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef};

use super::provenance::{Provenance, compute_provenance};

type ArgStoreTargets = Vec<SmallVec<[u32; 4]>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PtrEscapeSummary {
    pub(crate) arg_may_escape: Vec<bool>,
    pub(crate) arg_may_be_returned: Vec<bool>,
    pub(crate) arg_may_store_to_args: ArgStoreTargets,
    pub(crate) returns_any_ptr: bool,
}

impl PtrEscapeSummary {
    pub(crate) fn new(arg_count: usize) -> Self {
        Self {
            arg_may_escape: vec![false; arg_count],
            arg_may_be_returned: vec![false; arg_count],
            arg_may_store_to_args: std::iter::repeat_with(SmallVec::new)
                .take(arg_count)
                .collect(),
            returns_any_ptr: false,
        }
    }

    pub(crate) fn conservative_unknown(module: &Module, func: FuncRef) -> Self {
        Self::conservative_unknown_ctx(&module.ctx, func)
    }

    pub(crate) fn conservative_unknown_ctx(module: &ModuleCtx, func: FuncRef) -> Self {
        let arg_count = module.func_sig(func, |sig| sig.args().len());
        Self {
            arg_may_escape: vec![true; arg_count],
            arg_may_be_returned: vec![true; arg_count],
            arg_may_store_to_args: (0..arg_count)
                .map(|_| (0..arg_count).map(|idx| idx as u32).collect())
                .collect(),
            returns_any_ptr: module.func_sig(func, |sig| {
                sig.ret_tys().iter().any(|ty| ty.is_pointer(module))
            }),
        }
    }

    fn record_store_to_arg(&mut self, src_idx: usize, dst_idx: u32) {
        let Some(targets) = self.arg_may_store_to_args.get_mut(src_idx) else {
            return;
        };
        if targets.contains(&dst_idx) {
            return;
        }
        targets.push(dst_idx);
        targets.sort_unstable();
    }
}

pub(crate) fn compute_ptr_escape_summaries(
    module: &Module,
    funcs: &[FuncRef],
    isa: &Evm,
) -> FxHashMap<FuncRef, PtrEscapeSummary> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);

    let topo = topo_sort_sccs(&funcs_set, &call_graph, &scc);

    let mut summaries: FxHashMap<FuncRef, PtrEscapeSummary> = FxHashMap::default();
    for &f in funcs {
        let arg_count = module.func_store.view(f, |func| func.arg_values.len());
        summaries.insert(f, PtrEscapeSummary::new(arg_count));
    }

    for scc_ref in topo.into_iter().rev() {
        let mut component: Vec<FuncRef> = scc
            .scc_info(scc_ref)
            .components
            .iter()
            .copied()
            .filter(|f| funcs_set.contains(f))
            .collect();
        component.sort_unstable_by_key(|f| f.as_u32());

        loop {
            let mut changed = false;
            for &f in &component {
                let new_summary = compute_summary_for_func(module, f, isa, &summaries);
                let cur = summaries.get(&f).expect("missing ptr escape summary");
                if *cur != new_summary {
                    summaries.insert(f, new_summary);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }
    }

    summaries
}

fn topo_sort_sccs(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
    scc: &CallGraphSccs,
) -> Vec<SccRef> {
    let mut sccs: BTreeSet<SccRef> = BTreeSet::new();
    for &f in funcs {
        sccs.insert(scc.scc_ref(f));
    }

    let mut edges: BTreeMap<SccRef, BTreeSet<SccRef>> = BTreeMap::new();
    let mut indegree: BTreeMap<SccRef, usize> = BTreeMap::new();
    for &s in &sccs {
        edges.insert(s, BTreeSet::new());
        indegree.insert(s, 0);
    }

    for &f in funcs {
        let from = scc.scc_ref(f);
        for &callee in call_graph.callee_of(f) {
            let to = scc.scc_ref(callee);
            if from == to {
                continue;
            }

            let tos = edges.get_mut(&from).expect("missing scc");
            if tos.insert(to) {
                *indegree.get_mut(&to).expect("missing scc") += 1;
            }
        }
    }

    let mut ready: BTreeSet<SccRef> = BTreeSet::new();
    for (&s, &deg) in &indegree {
        if deg == 0 {
            ready.insert(s);
        }
    }

    let mut topo: Vec<SccRef> = Vec::with_capacity(sccs.len());
    while let Some(&s) = ready.first() {
        ready.remove(&s);
        topo.push(s);

        let tos: Vec<SccRef> = edges
            .get(&s)
            .expect("missing scc")
            .iter()
            .copied()
            .collect();
        for to in tos {
            let deg = indegree.get_mut(&to).expect("missing scc");
            *deg = deg.checked_sub(1).expect("indegree underflow");
            if *deg == 0 {
                ready.insert(to);
            }
        }
    }

    debug_assert_eq!(topo.len(), sccs.len(), "SCC topo sort incomplete");
    topo
}

fn compute_summary_for_func(
    module: &Module,
    func: FuncRef,
    isa: &Evm,
    summaries: &FxHashMap<FuncRef, PtrEscapeSummary>,
) -> PtrEscapeSummary {
    module.func_store.view(func, |function| {
        let arg_count = function.arg_values.len();
        let mut summary = PtrEscapeSummary::new(arg_count);

        let prov_info = compute_provenance(function, &module.ctx, isa, |callee| {
            summaries
                .get(&callee)
                .cloned()
                .unwrap_or_else(|| PtrEscapeSummary::conservative_unknown(module, callee))
        });
        let prov = &prov_info.value;
        let local_mem = &prov_info.local_mem;

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));

                match data {
                    EvmInstKind::Return(_) => {
                        let Some(ret_args) = function.dfg.return_args(inst) else {
                            continue;
                        };
                        for &ret_val in ret_args {
                            let ret_ty = function.dfg.value_ty(ret_val);
                            if ret_ty.is_pointer(&module.ctx) {
                                summary.returns_any_ptr = true;
                            }

                            let ret_prov = &prov[ret_val];
                            for idx in ret_prov.arg_indices() {
                                let idx = idx as usize;
                                if idx < summary.arg_may_be_returned.len() {
                                    summary.arg_may_be_returned[idx] = true;
                                }
                            }
                        }
                    }
                    EvmInstKind::Mstore(mstore) => {
                        let addr_prov = &prov[*mstore.addr()];
                        if addr_prov.is_local_addr() {
                            continue;
                        }

                        record_escape_into_provenance(
                            &mut summary,
                            &prov[*mstore.value()],
                            addr_prov,
                        );
                    }
                    EvmInstKind::EvmMstore8(mstore8) => {
                        let addr_prov = &prov[*mstore8.addr()];
                        if addr_prov.is_local_addr() {
                            continue;
                        }

                        record_escape_into_provenance(
                            &mut summary,
                            &prov[*mstore8.val()],
                            addr_prov,
                        );
                    }
                    EvmInstKind::EvmMcopy(mcopy) => {
                        let dest_prov = &prov[*mcopy.dest()];
                        if dest_prov.is_local_addr() {
                            continue;
                        }

                        let src_prov = &prov[*mcopy.addr()];
                        if src_prov.is_local_addr() {
                            for base in src_prov.alloca_insts() {
                                if let Some(stored) = local_mem.get(&base) {
                                    record_escape_into_provenance(&mut summary, stored, dest_prov);
                                }
                            }
                        } else {
                            record_escape_into_provenance(&mut summary, src_prov, dest_prov);
                        }
                    }
                    EvmInstKind::Call(call) => {
                        let callee = *call.callee();
                        let callee_sum = summaries.get(&callee).cloned().unwrap_or_else(|| {
                            PtrEscapeSummary::conservative_unknown(module, callee)
                        });

                        let args = call.args();
                        for (idx, &arg) in args.iter().enumerate() {
                            let p = &prov[arg];
                            if idx < callee_sum.arg_may_escape.len()
                                && callee_sum.arg_may_escape[idx]
                            {
                                for arg_idx in p.arg_indices() {
                                    let arg_idx = arg_idx as usize;
                                    if arg_idx < summary.arg_may_escape.len() {
                                        summary.arg_may_escape[arg_idx] = true;
                                    }
                                }
                            }
                            if let Some(targets) = callee_sum.arg_may_store_to_args.get(idx) {
                                for arg_idx in p.arg_indices() {
                                    for &target in targets {
                                        let Some(&target_arg) = args.get(target as usize) else {
                                            continue;
                                        };
                                        record_escape_from_arg_index(
                                            &mut summary,
                                            arg_idx as usize,
                                            &prov[target_arg],
                                        );
                                    }
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        summary
    })
}

fn record_escape_into_provenance(
    summary: &mut PtrEscapeSummary,
    src_prov: &Provenance,
    dst_prov: &Provenance,
) {
    for arg_idx in src_prov.arg_indices() {
        record_escape_from_arg_index(summary, arg_idx as usize, dst_prov);
    }
}

fn record_escape_from_arg_index(
    summary: &mut PtrEscapeSummary,
    src_idx: usize,
    dst_prov: &Provenance,
) {
    for dst_idx in dst_prov.arg_indices() {
        summary.record_store_to_arg(src_idx, dst_idx);
    }
    if dst_prov.may_be_nonlocal_nonarg()
        && let Some(escapes) = summary.arg_may_escape.get_mut(src_idx)
    {
        *escapes = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn compute(
        src: &str,
    ) -> (
        FxHashMap<String, PtrEscapeSummary>,
        FxHashMap<String, FuncRef>,
    ) {
        let parsed = parse_module(src).unwrap();
        let funcs: Vec<FuncRef> = parsed.module.funcs();
        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for f in funcs.iter().copied() {
            let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
            names.insert(name, f);
        }

        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });

        let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        let mut out: FxHashMap<String, PtrEscapeSummary> = FxHashMap::default();
        for (name, f) in &names {
            if let Some(sum) = summaries.get(f) {
                out.insert(name.clone(), sum.clone());
            }
        }

        (out, names)
    }

    #[test]
    fn ptr_escape_direct_return() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %g(v0.*i8) -> *i8 {
block0:
    return v0;
}
"#,
        );

        let g = &summaries["g"];
        assert!(g.returns_any_ptr);
        assert_eq!(g.arg_may_be_returned, vec![true]);
        assert_eq!(g.arg_may_escape, vec![false]);
    }

    #[test]
    fn ptr_escape_propagates_through_calls() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %sink(v0.*i8) {
block0:
    mstore 0.i32 v0 *i8;
    return;
}

func public %f(v0.*i8) {
block0:
    call %sink v0;
    return;
}
"#,
        );

        let sink = &summaries["sink"];
        assert_eq!(sink.arg_may_escape, vec![true]);

        let f = &summaries["f"];
        assert_eq!(f.arg_may_escape, vec![true]);
    }

    #[test]
    fn ptr_escape_call_return_flow() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %id(v0.*i8) -> *i8 {
block0:
    return v0;
}

func public %f(v0.*i8) -> *i8 {
block0:
    v1.*i8 = call %id v0;
    return v1;
}
"#,
        );

        let f = &summaries["f"];
        assert!(f.returns_any_ptr);
        assert_eq!(f.arg_may_be_returned, vec![true]);
        assert_eq!(f.arg_may_escape, vec![false]);
    }

    #[test]
    fn ptr_escape_non_arg_unknown_return_does_not_mark_all_args_returned() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8, v1.*i8) -> *i8 {
block0:
    v2.*i8 = int_to_ptr 0.i32 *i8;
    return v2;
}
"#,
        );

        let f = &summaries["f"];
        assert!(f.returns_any_ptr);
        assert_eq!(f.arg_may_be_returned, vec![false, false]);
        assert_eq!(f.arg_may_escape, vec![false, false]);
    }

    #[test]
    fn ptr_escape_non_arg_unknown_store_does_not_mark_all_args_escape() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8, v1.*i8) {
block0:
    v2.*i8 = int_to_ptr 0.i32 *i8;
    mstore 0.i32 v2 *i8;
    return;
}
"#,
        );

        let f = &summaries["f"];
        assert_eq!(f.arg_may_be_returned, vec![false, false]);
        assert_eq!(f.arg_may_escape, vec![false, false]);
    }

    #[test]
    fn ptr_escape_tracks_pointer_store_into_out_param_arg_conditionally() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
    mstore v1 v0 *i8;
    return;
}
"#,
        );

        let capture = &summaries["capture"];
        assert_eq!(capture.arg_may_escape, vec![false, false]);
        assert_eq!(capture.arg_may_be_returned, vec![false, false]);
        assert_eq!(
            capture.arg_may_store_to_args[0].as_slice(),
            &[1],
            "arg 0 should only escape through arg 1"
        );
        assert!(
            capture.arg_may_store_to_args[1].is_empty(),
            "out-param itself should not be marked as forwarded"
        );
    }

    #[test]
    fn ptr_escape_local_out_param_capture_does_not_mark_caller_arg_escape() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

type @Take = {i256, *[i256; 8]};

func public %take(v7.*@Take, v0.i256, v1.*[i256; 8]) {
block0:
    v3.*i256 = bitcast v7 *i256;
    mstore v3 v0 i256;
    v4.**[i256; 8] = gep v7 0.i256 1.i256;
    mstore v4 v1 *[i256; 8];
    return;
}

func public %take_get(v0.*@Take, v1.i256) -> i256 {
block0:
    v3.**[i256; 8] = gep v0 0.i256 1.i256;
    v4.*[i256; 8] = mload v3 *[i256; 8];
    v5.*i256 = gep v4 0.i256 v1;
    v6.i256 = mload v5 i256;
    return v6;
}

func public %sum_last4(v0.*[i256; 8]) -> i256 {
block0:
    v1.*@Take = alloca @Take;
    call %take v1 4.i256 v0;
    v2.i256 = call %take_get v1 0.i256;
    return v2;
}
"#,
        );

        let take = &summaries["take"];
        assert_eq!(take.arg_may_escape, vec![false, false, false]);
        assert_eq!(
            take.arg_may_store_to_args[2].as_slice(),
            &[0],
            "take should forward arg 2 only into the synthetic out-param"
        );

        let sum_last4 = &summaries["sum_last4"];
        assert_eq!(
            sum_last4.arg_may_escape,
            vec![false],
            "caller-local synthetic out-param must not count as an escape"
        );
    }
}
