use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    InstSetExt, Module,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::FuncRef,
};
use std::collections::{BTreeMap, BTreeSet};

use crate::module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef};

use super::provenance::compute_provenance;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PtrEscapeSummary {
    pub(crate) arg_may_escape: Vec<bool>,
    pub(crate) arg_may_be_returned: Vec<bool>,
    pub(crate) returns_any_ptr: bool,
}

impl PtrEscapeSummary {
    fn new(arg_count: usize) -> Self {
        Self {
            arg_may_escape: vec![false; arg_count],
            arg_may_be_returned: vec![false; arg_count],
            returns_any_ptr: false,
        }
    }

    fn conservative_unknown(module: &Module, func: FuncRef) -> Self {
        let arg_count = module.func_store.view(func, |f| f.arg_values.len());
        Self {
            arg_may_escape: vec![true; arg_count],
            arg_may_be_returned: vec![true; arg_count],
            returns_any_ptr: module
                .ctx
                .func_sig(func, |sig| sig.ret_ty().is_pointer(&module.ctx)),
        }
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

        let mut arg_is_ptr: Vec<bool> = Vec::with_capacity(arg_count);
        for &arg in &function.arg_values {
            arg_is_ptr.push(function.dfg.value_ty(arg).is_pointer(&module.ctx));
        }

        let prov_info = compute_provenance(function, &module.ctx, isa, |callee| {
            summaries
                .get(&callee)
                .cloned()
                .unwrap_or_else(|| PtrEscapeSummary::conservative_unknown(module, callee))
                .arg_may_be_returned
        });
        let prov = &prov_info.value;
        let local_mem = &prov_info.local_mem;

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));

                match data {
                    EvmInstKind::Return(ret) => {
                        let Some(ret_val) = *ret.arg() else {
                            continue;
                        };

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

                        if ret_ty.is_pointer(&module.ctx) && !ret_prov.has_any_arg() {
                            for (idx, is_ptr) in arg_is_ptr.iter().copied().enumerate() {
                                if is_ptr {
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

                        let val_prov = &prov[*mstore.value()];
                        for idx in val_prov.arg_indices() {
                            let idx = idx as usize;
                            if idx < summary.arg_may_escape.len() {
                                summary.arg_may_escape[idx] = true;
                            }
                        }
                        if val_prov.is_unknown_ptr() {
                            mark_all_ptr_args_escape(&mut summary, &arg_is_ptr);
                        }
                    }
                    EvmInstKind::EvmMstore8(mstore8) => {
                        let addr_prov = &prov[*mstore8.addr()];
                        if addr_prov.is_local_addr() {
                            continue;
                        }

                        let val_prov = &prov[*mstore8.val()];
                        for idx in val_prov.arg_indices() {
                            let idx = idx as usize;
                            if idx < summary.arg_may_escape.len() {
                                summary.arg_may_escape[idx] = true;
                            }
                        }
                        if val_prov.is_unknown_ptr() {
                            mark_all_ptr_args_escape(&mut summary, &arg_is_ptr);
                        }
                    }
                    EvmInstKind::EvmMcopy(mcopy) => {
                        let dest_prov = &prov[*mcopy.dest()];
                        if dest_prov.is_local_addr() {
                            continue;
                        }

                        let src_prov = &prov[*mcopy.addr()];
                        if src_prov.is_local_addr() {
                            let mut any = false;
                            for base in src_prov.alloca_insts() {
                                any = true;
                                if let Some(stored) = local_mem.get(&base) {
                                    for idx in stored.arg_indices() {
                                        let idx = idx as usize;
                                        if idx < summary.arg_may_escape.len() {
                                            summary.arg_may_escape[idx] = true;
                                        }
                                    }
                                    if stored.is_unknown_ptr() {
                                        mark_all_ptr_args_escape(&mut summary, &arg_is_ptr);
                                    }
                                }
                            }
                            if !any {
                                mark_all_ptr_args_escape(&mut summary, &arg_is_ptr);
                            }
                        } else {
                            mark_all_ptr_args_escape(&mut summary, &arg_is_ptr);
                        }
                    }
                    EvmInstKind::Call(call) => {
                        let callee = *call.callee();
                        let callee_sum = summaries.get(&callee).cloned().unwrap_or_else(|| {
                            PtrEscapeSummary::conservative_unknown(module, callee)
                        });

                        let args = call.args();
                        for (idx, &arg) in args.iter().enumerate() {
                            if idx < callee_sum.arg_may_escape.len()
                                && callee_sum.arg_may_escape[idx]
                            {
                                let p = &prov[arg];
                                for arg_idx in p.arg_indices() {
                                    let arg_idx = arg_idx as usize;
                                    if arg_idx < summary.arg_may_escape.len() {
                                        summary.arg_may_escape[arg_idx] = true;
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

fn mark_all_ptr_args_escape(summary: &mut PtrEscapeSummary, arg_is_ptr: &[bool]) {
    for (idx, is_ptr) in arg_is_ptr.iter().copied().enumerate() {
        if is_ptr {
            summary.arg_may_escape[idx] = true;
        }
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
}
