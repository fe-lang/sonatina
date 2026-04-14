use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    InstSetExt, Module, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};
use std::collections::{BTreeMap, BTreeSet};

use crate::module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef};

use super::provenance::{Provenance, compute_provenance};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ArgStoreLattice(u8);

impl ArgStoreLattice {
    const LOCAL: u8 = 1 << 0;
    const ARG: u8 = 1 << 1;
    const NONLOCAL: u8 = 1 << 2;

    fn record(&mut self, flag: u8) -> bool {
        let changed = self.0 & flag == 0;
        self.0 |= flag;
        changed
    }

    fn record_local(&mut self) -> bool {
        self.record(Self::LOCAL)
    }

    fn record_arg(&mut self) -> bool {
        self.record(Self::ARG)
    }

    fn record_nonlocal(&mut self) -> bool {
        self.record(Self::NONLOCAL)
    }

    #[cfg(test)]
    pub(crate) fn may_store_local(self) -> bool {
        self.0 & Self::LOCAL != 0
    }

    #[cfg(test)]
    pub(crate) fn may_store_to_arg(self) -> bool {
        self.0 & Self::ARG != 0
    }

    pub(crate) fn may_store_nonlocal(self) -> bool {
        self.0 & Self::NONLOCAL != 0
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct PtrArgEscape {
    pub(crate) stores: ArgStoreLattice,
    pub(crate) arg_store_targets: SmallVec<[u32; 4]>,
    pub(crate) may_be_returned: bool,
}

impl PtrArgEscape {
    fn record_store_to_arg(&mut self, dst_idx: u32) -> bool {
        if self.arg_store_targets.contains(&dst_idx) {
            return false;
        }
        self.arg_store_targets.push(dst_idx);
        self.arg_store_targets.sort_unstable();
        self.stores.record_arg()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PtrEscapeSummary {
    pub(crate) args: Vec<PtrArgEscape>,
    pub(crate) returns_any_ptr: bool,
}

impl PtrEscapeSummary {
    pub(crate) fn new(arg_count: usize) -> Self {
        Self {
            args: vec![PtrArgEscape::default(); arg_count],
            returns_any_ptr: false,
        }
    }

    pub(crate) fn conservative_unknown(module: &Module, func: FuncRef) -> Self {
        Self::conservative_unknown_ctx(&module.ctx, func)
    }

    pub(crate) fn conservative_unknown_ctx(module: &ModuleCtx, func: FuncRef) -> Self {
        let arg_count = module.func_sig(func, |sig| sig.args().len());
        let mut out = Self::new(arg_count);
        out.returns_any_ptr = module.func_sig(func, |sig| {
            sig.ret_tys().iter().any(|ty| ty.is_pointer(module))
        });
        for arg in &mut out.args {
            arg.may_be_returned = true;
            arg.stores.record_arg();
            arg.stores.record_nonlocal();
            arg.arg_store_targets
                .extend((0..arg_count).map(|idx| idx as u32));
        }
        out
    }

    fn record_store_to_arg(&mut self, src_idx: usize, dst_idx: u32) {
        let Some(arg) = self.args.get_mut(src_idx) else {
            return;
        };
        let _ = arg.record_store_to_arg(dst_idx);
    }

    fn record_store_local(&mut self, src_idx: usize) {
        if let Some(arg) = self.args.get_mut(src_idx) {
            let _ = arg.stores.record_local();
        }
    }

    fn record_store_nonlocal(&mut self, src_idx: usize) {
        if let Some(arg) = self.args.get_mut(src_idx) {
            let _ = arg.stores.record_nonlocal();
        }
    }

    fn record_returned_arg(&mut self, src_idx: usize) {
        if let Some(arg) = self.args.get_mut(src_idx) {
            arg.may_be_returned = true;
        }
    }

    pub(crate) fn arg_may_escape(&self, src_idx: usize) -> bool {
        self.args
            .get(src_idx)
            .is_some_and(|arg| arg.stores.may_store_nonlocal())
    }

    pub(crate) fn arg_may_be_returned(&self, src_idx: usize) -> bool {
        self.args
            .get(src_idx)
            .is_some_and(|arg| arg.may_be_returned)
    }

    pub(crate) fn arg_store_targets(&self, src_idx: usize) -> &[u32] {
        self.args
            .get(src_idx)
            .map_or(&[], |arg| arg.arg_store_targets.as_slice())
    }

    pub(crate) fn arg_store_lattice(&self, src_idx: usize) -> ArgStoreLattice {
        self.args
            .get(src_idx)
            .map_or_else(ArgStoreLattice::default, |arg| arg.stores)
    }

    pub(crate) fn call_arg_may_escape_nonlocal(
        &self,
        src_idx: usize,
        call_args: &[ValueId],
        prov: &SecondaryMap<ValueId, Provenance>,
    ) -> bool {
        self.arg_may_escape(src_idx)
            || self
                .call_arg_store_dest_args(src_idx, call_args)
                .any(|dst_arg| {
                    let dst_prov = &prov[dst_arg];
                    dst_prov.has_any_arg() || dst_prov.may_be_nonlocal_nonarg()
                })
    }

    pub(crate) fn call_arg_store_dest_args<'a>(
        &'a self,
        src_idx: usize,
        call_args: &'a [ValueId],
    ) -> impl Iterator<Item = ValueId> + 'a {
        self.arg_store_targets(src_idx)
            .iter()
            .filter_map(move |&dst_idx| call_args.get(dst_idx as usize).copied())
    }

    fn normalize(&mut self) {
        let direct: Vec<_> = self
            .args
            .iter()
            .map(|arg| (arg.stores, arg.arg_store_targets.clone()))
            .collect();

        for src_idx in 0..self.args.len() {
            let (mut stores, direct_targets) = direct[src_idx].clone();
            let mut stack = direct_targets.into_vec();
            let mut seen = vec![false; self.args.len()];
            let mut closed_targets = SmallVec::<[u32; 4]>::new();

            while let Some(dst_idx) = stack.pop() {
                let dst_idx = dst_idx as usize;
                if dst_idx >= self.args.len() || seen[dst_idx] {
                    continue;
                }
                seen[dst_idx] = true;
                closed_targets.push(dst_idx as u32);

                let (_, dst_targets) = &direct[dst_idx];
                stack.extend(dst_targets.iter().copied());
            }

            closed_targets.sort_unstable();
            closed_targets.dedup();
            if !closed_targets.is_empty() {
                let _ = stores.record_arg();
            }

            self.args[src_idx].stores = stores;
            self.args[src_idx].arg_store_targets = closed_targets;
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
                let mut new_summary = compute_summary_for_func(module, f, isa, &summaries);
                new_summary.normalize();
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
                                summary.record_returned_arg(idx as usize);
                            }
                        }
                    }
                    EvmInstKind::Mstore(mstore) => {
                        let addr_prov = &prov[*mstore.addr()];
                        record_escape_into_provenance(
                            &mut summary,
                            &prov[*mstore.value()],
                            addr_prov,
                        );
                    }
                    EvmInstKind::EvmMstore8(mstore8) => {
                        let addr_prov = &prov[*mstore8.addr()];
                        record_escape_into_provenance(
                            &mut summary,
                            &prov[*mstore8.val()],
                            addr_prov,
                        );
                    }
                    EvmInstKind::EvmMcopy(mcopy) => {
                        let dest_prov = &prov[*mcopy.dest()];
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
                            if callee_sum.arg_store_lattice(idx).may_store_nonlocal() {
                                for arg_idx in p.arg_indices() {
                                    summary.record_store_nonlocal(arg_idx as usize);
                                }
                            }
                            for arg_idx in p.arg_indices() {
                                for target_arg in callee_sum.call_arg_store_dest_args(idx, args) {
                                    record_escape_from_arg_index(
                                        &mut summary,
                                        arg_idx as usize,
                                        &prov[target_arg],
                                    );
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
    if dst_prov.is_local_addr() {
        summary.record_store_local(src_idx);
    }
    for dst_idx in dst_prov.arg_indices() {
        summary.record_store_to_arg(src_idx, dst_idx);
    }
    if dst_prov.may_be_nonlocal_nonarg() {
        summary.record_store_nonlocal(src_idx);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn arg_may_escape(summary: &PtrEscapeSummary) -> Vec<bool> {
        (0..summary.args.len())
            .map(|idx| summary.arg_may_escape(idx))
            .collect()
    }

    fn arg_may_be_returned(summary: &PtrEscapeSummary) -> Vec<bool> {
        (0..summary.args.len())
            .map(|idx| summary.arg_may_be_returned(idx))
            .collect()
    }

    fn arg_store_targets(summary: &PtrEscapeSummary, idx: usize) -> Vec<u32> {
        summary.arg_store_targets(idx).to_vec()
    }

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

    fn call_arg_may_escape_from_src(src: &str, func_name: &str, arg_index: usize) -> bool {
        let parsed = parse_module(src).expect("module parses");
        let funcs: Vec<FuncRef> = parsed.module.funcs();
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func| {
                parsed
                    .module
                    .ctx
                    .func_sig(func, |sig| sig.name() == func_name)
            })
            .expect("function exists");

        parsed.module.func_store.view(func_ref, |function| {
            let prov = compute_provenance(function, &parsed.module.ctx, &isa, |callee| {
                summaries.get(&callee).cloned().unwrap_or_else(|| {
                    PtrEscapeSummary::conservative_unknown(&parsed.module, callee)
                })
            })
            .value;
            let call_inst = function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .find(|&inst| function.dfg.call_info(inst).is_some())
                .expect("call exists");
            let EvmInstKind::Call(call) = isa.inst_set().resolve_inst(function.dfg.inst(call_inst))
            else {
                panic!("expected internal call");
            };
            let callee_sum = summaries.get(call.callee()).cloned().unwrap_or_else(|| {
                PtrEscapeSummary::conservative_unknown(&parsed.module, *call.callee())
            });

            callee_sum.call_arg_may_escape_nonlocal(arg_index, call.args(), &prov)
        })
    }

    fn ret_provenance_from_src(src: &str, func_name: &str) -> Provenance {
        let parsed = parse_module(src).expect("module parses");
        let funcs: Vec<FuncRef> = parsed.module.funcs();
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func| {
                parsed
                    .module
                    .ctx
                    .func_sig(func, |sig| sig.name() == func_name)
            })
            .expect("function exists");

        parsed.module.func_store.view(func_ref, |function| {
            let prov = compute_provenance(function, &parsed.module.ctx, &isa, |callee| {
                summaries.get(&callee).cloned().unwrap_or_else(|| {
                    PtrEscapeSummary::conservative_unknown(&parsed.module, callee)
                })
            })
            .value;

            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
                    if let EvmInstKind::Return(_) = data
                        && let Some(ret_val) = function
                            .dfg
                            .return_args(inst)
                            .and_then(|args| args.first().copied())
                    {
                        return prov[ret_val].clone();
                    }
                }
            }

            panic!("no return value in function");
        })
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
        assert_eq!(arg_may_be_returned(g), vec![true]);
        assert_eq!(arg_may_escape(g), vec![false]);
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
        assert_eq!(arg_may_escape(sink), vec![true]);

        let f = &summaries["f"];
        assert_eq!(arg_may_escape(f), vec![true]);
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
        assert_eq!(arg_may_be_returned(f), vec![true]);
        assert_eq!(arg_may_escape(f), vec![false]);
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
        assert_eq!(arg_may_be_returned(f), vec![false, false]);
        assert_eq!(arg_may_escape(f), vec![false, false]);
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
        assert_eq!(arg_may_be_returned(f), vec![false, false]);
        assert_eq!(arg_may_escape(f), vec![false, false]);
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
        assert_eq!(arg_may_escape(capture), vec![false, false]);
        assert_eq!(arg_may_be_returned(capture), vec![false, false]);
        assert_eq!(
            arg_store_targets(capture, 0),
            vec![1],
            "arg 0 should only escape through arg 1"
        );
        assert!(
            capture.arg_store_targets(1).is_empty(),
            "out-param itself should not be marked as forwarded"
        );
        assert!(capture.arg_store_lattice(0).may_store_to_arg());
        assert!(!capture.arg_store_lattice(0).may_store_nonlocal());
    }

    #[test]
    fn ptr_escape_preserves_self_target_arg_stores() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %capture(v0.**i8) {
block0:
    mstore v0 v0 **i8;
    return;
}
"#,
        );

        let capture = &summaries["capture"];
        assert_eq!(arg_may_escape(capture), vec![false]);
        assert_eq!(arg_may_be_returned(capture), vec![false]);
        assert_eq!(
            arg_store_targets(capture, 0),
            vec![0],
            "self-target out-param stores must stay modeled"
        );
        assert!(capture.arg_store_lattice(0).may_store_to_arg());
        assert!(!capture.arg_store_lattice(0).may_store_nonlocal());
    }

    #[test]
    fn ptr_escape_self_target_call_preserves_local_roundtrip_provenance() {
        let ret_prov = ret_provenance_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %capture(v0.**i8) {
block0:
    mstore v0 v0 **i8;
    return;
}

func public %wrapper() -> **i8 {
block0:
    v0.**i8 = alloca *i8;
    call %capture v0;
    v1.**i8 = mload v0 **i8;
    return v1;
}
"#,
            "wrapper",
        );

        assert!(ret_prov.is_local_addr(), "{ret_prov:?}");
        assert_eq!(ret_prov.alloca_insts().count(), 1);
    }

    #[test]
    fn ptr_escape_keeps_nonlocal_outparam_destinations_context_sensitive() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
    mstore v1 v0 *i8;
    mstore 0.i32 v1 **i8;
    return;
}

func public %top_arg(v0.*i8, v1.**i8) {
block0:
    call %capture v0 v1;
    return;
}

func public %top_local(v0.*i8) {
block0:
    v1.**i8 = alloca *i8;
    call %capture v0 v1;
    return;
}
"#;
        let (summaries, _) = compute(src);

        let capture = &summaries["capture"];
        assert_eq!(arg_may_escape(capture), vec![false, true]);
        assert_eq!(
            arg_store_targets(capture, 0),
            vec![1],
            "source arg should keep only the forwarded out-param target"
        );
        assert!(!capture.arg_store_lattice(0).may_store_nonlocal());
        assert!(capture.arg_store_lattice(0).may_store_to_arg());
        assert!(capture.arg_store_lattice(1).may_store_nonlocal());

        assert!(
            call_arg_may_escape_from_src(src, "top_arg", 0),
            "arg-backed out-param should still make the source escape"
        );
        assert!(
            !call_arg_may_escape_from_src(src, "top_local", 0),
            "caller-local out-param should remain non-escaping"
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
        assert_eq!(arg_may_escape(take), vec![false, false, false]);
        assert_eq!(
            arg_store_targets(take, 2),
            vec![0],
            "take should forward arg 2 only into the synthetic out-param"
        );

        let sum_last4 = &summaries["sum_last4"];
        assert_eq!(
            arg_may_escape(sum_last4),
            vec![false],
            "caller-local synthetic out-param must not count as an escape"
        );
    }

    #[test]
    fn ptr_escape_resolves_outparam_arg_escapes_through_callers() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
    mstore v1 v0 *i8;
    return;
}

func public %wrapper(v0.*i8, v1.**i8) {
block0:
    call %capture v0 v1;
    return;
}

func public %through_arg(v0.*i8, v1.**i8) {
block0:
    call %wrapper v0 v1;
    return;
}

func public %top_arg(v0.*i8, v1.**i8) {
block0:
    call %through_arg v0 v1;
    return;
}

func public %top_local(v0.*i8) {
block0:
    v1.**i8 = alloca *i8;
    call %through_arg v0 v1;
    return;
}
"#;
        let (summaries, _) = compute(src);

        let wrapper = &summaries["wrapper"];
        assert_eq!(arg_may_escape(wrapper), vec![false, false]);
        assert_eq!(
            arg_store_targets(wrapper, 0),
            vec![1],
            "wrapper should still record that arg 0 flows into arg 1"
        );

        let through_arg = &summaries["through_arg"];
        assert_eq!(
            arg_may_escape(through_arg),
            vec![false, false],
            "intermediate wrappers should keep arg-backed stores contextual"
        );

        assert!(
            call_arg_may_escape_from_src(src, "top_arg", 0),
            "argument-backed out-param should mark the source arg as escaping at the caller boundary"
        );

        assert!(
            !call_arg_may_escape_from_src(src, "top_local", 0),
            "caller-local synthetic out-param must stay non-escaping"
        );
    }

    #[test]
    fn ptr_escape_store_lattice_covers_direct_and_mixed_destinations() {
        type PtrEscapeCase = (&'static str, &'static str, fn(&PtrEscapeSummary));

        let cases: [PtrEscapeCase; 4] = [
            (
                "direct_nonlocal",
                r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8) {
block0:
    mstore 0.i32 v0 *i8;
    return;
}
"#,
                |summary: &PtrEscapeSummary| {
                    assert_eq!(arg_may_escape(summary), vec![true]);
                    assert!(summary.arg_store_lattice(0).may_store_nonlocal());
                    assert!(!summary.arg_store_lattice(0).may_store_local());
                    assert!(!summary.arg_store_lattice(0).may_store_to_arg());
                },
            ),
            (
                "wrapper_arg",
                r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
    mstore v1 v0 *i8;
    return;
}

func public %f(v0.*i8, v1.**i8) {
block0:
    call %capture v0 v1;
    return;
}
"#,
                |summary: &PtrEscapeSummary| {
                    assert_eq!(arg_may_escape(summary), vec![false, false]);
                    assert!(!summary.arg_store_lattice(0).may_store_local());
                    assert!(summary.arg_store_lattice(0).may_store_to_arg());
                    assert!(!summary.arg_store_lattice(0).may_store_nonlocal());
                    assert_eq!(arg_store_targets(summary, 0), vec![1]);
                },
            ),
            (
                "wrapper_local",
                r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
    mstore v1 v0 *i8;
    return;
}

func public %f(v0.*i8) {
block0:
    v1.**i8 = alloca *i8;
    call %capture v0 v1;
    return;
}
"#,
                |summary: &PtrEscapeSummary| {
                    assert_eq!(arg_may_escape(summary), vec![false]);
                    assert!(summary.arg_store_lattice(0).may_store_local());
                    assert!(!summary.arg_store_lattice(0).may_store_nonlocal());
                    assert!(!summary.arg_store_lattice(0).may_store_to_arg());
                },
            ),
            (
                "mixed_destinations",
                r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8, v1.**i8, v2.i1) {
block0:
    br v2 block1 block2;

block1:
    mstore v1 v0 *i8;
    return;

block2:
    v3.**i8 = alloca *i8;
    mstore v3 v0 *i8;
    return;
}
"#,
                |summary: &PtrEscapeSummary| {
                    assert_eq!(arg_may_escape(summary), vec![false, false, false]);
                    assert!(summary.arg_store_lattice(0).may_store_local());
                    assert!(summary.arg_store_lattice(0).may_store_to_arg());
                    assert!(!summary.arg_store_lattice(0).may_store_nonlocal());
                    assert_eq!(arg_store_targets(summary, 0), vec![1]);
                },
            ),
        ];

        for (name, src, check) in cases {
            let (summaries, _) = compute(src);
            check(
                summaries
                    .get("f")
                    .unwrap_or_else(|| panic!("missing summary for case {name}")),
            );
        }
    }
}
