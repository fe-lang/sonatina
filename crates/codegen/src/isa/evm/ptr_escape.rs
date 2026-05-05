#[cfg(test)]
use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, Module, ValueId,
    isa::evm::Evm,
    module::{FuncRef, ModuleCtx},
};
use std::collections::{BTreeMap, BTreeSet};

use crate::module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef};

use super::{
    escape_scan::{
        EscapeScanCtx, PtrTransferEvent, PtrTransferSource, for_each_ptr_transfer_at_inst,
    },
    provenance::{Provenance, compute_provenance, type_can_carry_pointer_provenance},
};

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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct PtrReturnEscape {
    pub(crate) returned_args: SmallVec<[u32; 4]>,
    pub(crate) non_arg_pointer: bool,
}

impl PtrReturnEscape {
    fn record_arg(&mut self, arg_idx: u32) -> bool {
        if self.returned_args.contains(&arg_idx) {
            return false;
        }
        self.returned_args.push(arg_idx);
        self.returned_args.sort_unstable();
        true
    }
}

/// Summary of direct pointer escape effects at a function boundary.
///
/// All facts are callee-local: [`PtrArgEscape::arg_store_targets`] records only
/// direct writes within the callee body (including single-level callee summary
/// application during SCC fixpoint iteration). No transitive closure is taken.
///
/// Effects that depend on caller context (e.g., whether a destination arg is
/// backed by local memory vs nonlocal memory) must be derived at call sites
/// via [`Self::call_arg_may_escape_nonlocal`] or [`Self::for_each_store_effect`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PtrEscapeSummary {
    pub(crate) args: Vec<PtrArgEscape>,
    pub(crate) returns: Vec<PtrReturnEscape>,
}

impl PtrEscapeSummary {
    fn new(arg_count: usize, ret_count: usize) -> Self {
        Self {
            args: vec![PtrArgEscape::default(); arg_count],
            returns: vec![PtrReturnEscape::default(); ret_count],
        }
    }

    pub(crate) fn empty_for_func(module: &ModuleCtx, func: FuncRef) -> Self {
        module.func_sig(func, |sig| Self::new(sig.args().len(), sig.ret_tys().len()))
    }

    pub(crate) fn conservative_unknown_ctx(module: &ModuleCtx, func: FuncRef) -> Self {
        let (arg_count, ret_count) =
            module.func_sig(func, |sig| (sig.args().len(), sig.ret_tys().len()));
        let mut out = Self::new(arg_count, ret_count);
        module.func_sig(func, |sig| {
            for (ret_idx, &ret_ty) in sig.ret_tys().iter().enumerate() {
                if type_can_carry_pointer_provenance(module, ret_ty) {
                    out.returns[ret_idx].non_arg_pointer = true;
                    for arg_idx in 0..arg_count {
                        let _ = out.returns[ret_idx].record_arg(arg_idx as u32);
                    }
                }
            }
        });
        for arg in &mut out.args {
            arg.stores.record_arg();
            arg.stores.record_nonlocal();
            arg.arg_store_targets
                .extend((0..arg_count).map(|idx| idx as u32));
        }
        out
    }

    pub(crate) fn get_or_conservative(
        summaries: &FxHashMap<FuncRef, Self>,
        module: &ModuleCtx,
        func: FuncRef,
    ) -> Self {
        summaries
            .get(&func)
            .cloned()
            .unwrap_or_else(|| Self::conservative_unknown_ctx(module, func))
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

    fn record_returned_arg(&mut self, ret_idx: usize, src_idx: usize) {
        if let Some(ret) = self.returns.get_mut(ret_idx) {
            let _ = ret.record_arg(src_idx as u32);
        }
    }

    fn record_returned_non_arg_pointer(&mut self, ret_idx: usize) {
        if let Some(ret) = self.returns.get_mut(ret_idx) {
            ret.non_arg_pointer = true;
        }
    }

    pub(crate) fn arg_may_escape(&self, src_idx: usize) -> bool {
        self.args
            .get(src_idx)
            .is_some_and(|arg| arg.stores.may_store_nonlocal())
    }

    #[cfg(test)]
    pub(crate) fn arg_may_be_returned(&self, src_idx: usize) -> bool {
        self.returns
            .iter()
            .any(|ret| ret.returned_args.contains(&(src_idx as u32)))
    }

    pub(crate) fn returned_arg_indices(&self, ret_idx: usize) -> &[u32] {
        self.returns
            .get(ret_idx)
            .map_or(&[], |ret| ret.returned_args.as_slice())
    }

    pub(crate) fn return_may_be_non_arg_pointer(&self, ret_idx: usize) -> bool {
        self.returns
            .get(ret_idx)
            .is_some_and(|ret| ret.non_arg_pointer)
    }

    pub(crate) fn arg_store_targets(&self, src_idx: usize) -> &[u32] {
        self.args
            .get(src_idx)
            .map_or(&[], |arg| arg.arg_store_targets.as_slice())
    }

    #[cfg(test)]
    pub(crate) fn arg_count(&self) -> usize {
        self.args.len()
    }

    #[cfg(test)]
    pub(crate) fn arg_store_lattice(&self, src_idx: usize) -> ArgStoreLattice {
        self.args
            .get(src_idx)
            .map_or_else(ArgStoreLattice::default, |arg| arg.stores)
    }

    #[cfg(test)]
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

    /// Apply this summary's store effects at a call site, substituting actual
    /// args for formals. Calls `f(src_formal_idx, dst_actual)` for each direct
    /// src-to-dst-arg edge in the summary.
    pub(crate) fn for_each_store_effect(
        &self,
        call_args: &[ValueId],
        mut f: impl FnMut(usize, ValueId),
    ) {
        for (src_idx, arg) in self.args.iter().enumerate() {
            for &dst_idx in &arg.arg_store_targets {
                if let Some(&dst_actual) = call_args.get(dst_idx as usize) {
                    f(src_idx, dst_actual);
                }
            }
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
        module.func_store.view(f, |func| {
            let sig_arg_count = module.ctx.func_sig(f, |sig| sig.args().len());
            debug_assert_eq!(func.arg_values.len(), sig_arg_count);
        });
        summaries.insert(f, PtrEscapeSummary::empty_for_func(&module.ctx, f));
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
        let sig_arg_count = module.ctx.func_sig(func, |sig| sig.args().len());
        debug_assert_eq!(function.arg_values.len(), sig_arg_count);
        let mut summary = PtrEscapeSummary::empty_for_func(&module.ctx, func);

        let prov_info = compute_provenance(function, &module.ctx, isa, |callee| {
            PtrEscapeSummary::get_or_conservative(summaries, &module.ctx, callee)
        });
        let prov = &prov_info.value;
        let local_mem = &prov_info.local_mem;
        let arg_mem = &prov_info.arg_mem;
        let scan_ctx = EscapeScanCtx {
            module: &module.ctx,
            isa,
            ptr_escape: summaries,
            prov,
            local_mem,
            arg_mem,
        };

        let malloc_escape = compute_local_malloc_escape(scan_ctx, function);
        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                for_each_ptr_transfer_at_inst(function, inst, scan_ctx, |event| match event {
                    PtrTransferEvent::Return { ret_idx, value } => {
                        let ret_prov = &prov[value];
                        if ret_prov.is_unknown_ptr()
                            || ret_prov.malloc_insts().next().is_some()
                            || (function.dfg.value_ty(value).is_pointer(&module.ctx)
                                && ret_prov.has_no_known_bases())
                        {
                            summary.record_returned_non_arg_pointer(ret_idx);
                        }

                        for idx in prov[value].arg_indices() {
                            summary.record_returned_arg(ret_idx, idx as usize);
                        }
                    }
                    PtrTransferEvent::Write {
                        dest_prov, source, ..
                    } => match source {
                        PtrTransferSource::Value(value) => {
                            record_escape_into_provenance(
                                &mut summary,
                                &prov[value],
                                dest_prov,
                                &malloc_escape.escaping,
                            );
                        }
                        PtrTransferSource::LocalMem { stored, .. }
                        | PtrTransferSource::ArgMem { stored } => {
                            record_escape_into_provenance(
                                &mut summary,
                                stored,
                                dest_prov,
                                &malloc_escape.escaping,
                            );
                        }
                        PtrTransferSource::UnknownCopy => {}
                    },
                    PtrTransferEvent::CallArgEscape { value, .. } => {
                        for arg_idx in prov[value].arg_indices() {
                            summary.record_store_nonlocal(arg_idx as usize);
                        }
                    }
                    PtrTransferEvent::CallArgStore {
                        value, dest_prov, ..
                    } => {
                        for arg_idx in prov[value].arg_indices() {
                            record_escape_from_arg_index(
                                &mut summary,
                                arg_idx as usize,
                                dest_prov,
                                &malloc_escape.escaping,
                            );
                        }
                    }
                });
            }
        }

        summary
    })
}

#[derive(Default)]
struct LocalMallocEscape {
    contents: FxHashMap<InstId, Provenance>,
    escaping: FxHashSet<InstId>,
}

impl LocalMallocEscape {
    fn record_write(&mut self, src_prov: &Provenance, dst_prov: &Provenance) {
        for malloc in dst_prov.malloc_insts() {
            let _ = self
                .contents
                .entry(malloc)
                .or_default()
                .union_with(src_prov);
        }

        if dst_prov.has_any_arg() || dst_prov.may_be_nonlocal_nonarg_without_malloc() {
            self.record_escape(src_prov);
        }
    }

    fn record_escape(&mut self, prov: &Provenance) {
        for malloc in prov.malloc_insts() {
            self.escaping.insert(malloc);
        }
    }

    fn close(&mut self) {
        let mut worklist: SmallVec<[InstId; 8]> = self.escaping.iter().copied().collect();
        while let Some(malloc) = worklist.pop() {
            if let Some(stored) = self.contents.get(&malloc) {
                for child in stored.malloc_insts() {
                    if self.escaping.insert(child) {
                        worklist.push(child);
                    }
                }
            }
        }
    }
}

fn compute_local_malloc_escape(
    scan_ctx: EscapeScanCtx<'_>,
    function: &Function,
) -> LocalMallocEscape {
    let mut out = LocalMallocEscape::default();
    let prov = scan_ctx.prov;

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            for_each_ptr_transfer_at_inst(function, inst, scan_ctx, |event| match event {
                PtrTransferEvent::Return { value, .. }
                | PtrTransferEvent::CallArgEscape { value, .. } => out.record_escape(&prov[value]),
                PtrTransferEvent::Write {
                    dest_prov, source, ..
                } => match source {
                    PtrTransferSource::Value(value) => out.record_write(&prov[value], dest_prov),
                    PtrTransferSource::LocalMem { stored, .. }
                    | PtrTransferSource::ArgMem { stored } => {
                        out.record_write(stored, dest_prov);
                    }
                    PtrTransferSource::UnknownCopy => {}
                },
                PtrTransferEvent::CallArgStore {
                    value, dest_prov, ..
                } => {
                    out.record_write(&prov[value], dest_prov);
                }
            });
        }
    }

    out.close();
    out
}

fn record_escape_into_provenance(
    summary: &mut PtrEscapeSummary,
    src_prov: &Provenance,
    dst_prov: &Provenance,
    escaping_mallocs: &FxHashSet<InstId>,
) {
    for arg_idx in src_prov.arg_indices() {
        record_escape_from_arg_index(summary, arg_idx as usize, dst_prov, escaping_mallocs);
    }
}

fn record_escape_from_arg_index(
    summary: &mut PtrEscapeSummary,
    src_idx: usize,
    dst_prov: &Provenance,
    escaping_mallocs: &FxHashSet<InstId>,
) {
    if dst_prov.is_local_addr() || dst_prov.malloc_insts().next().is_some() {
        summary.record_store_local(src_idx);
    }
    for dst_idx in dst_prov.arg_indices() {
        summary.record_store_to_arg(src_idx, dst_idx);
    }
    if dst_prov.may_be_nonlocal_nonarg_without_malloc()
        || dst_prov
            .malloc_insts()
            .any(|malloc| escaping_mallocs.contains(&malloc))
    {
        summary.record_store_nonlocal(src_idx);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{InstSetExt, inst::evm::inst_set::EvmInstKind, isa::Isa};
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn arg_may_escape(summary: &PtrEscapeSummary) -> Vec<bool> {
        (0..summary.arg_count())
            .map(|idx| summary.arg_may_escape(idx))
            .collect()
    }

    fn arg_may_be_returned(summary: &PtrEscapeSummary) -> Vec<bool> {
        (0..summary.arg_count())
            .map(|idx| summary.arg_may_be_returned(idx))
            .collect()
    }

    fn ret_args(summary: &PtrEscapeSummary, ret_idx: usize) -> Vec<u32> {
        summary.returned_arg_indices(ret_idx).to_vec()
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
                PtrEscapeSummary::get_or_conservative(&summaries, &parsed.module.ctx, callee)
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
            let callee_sum = PtrEscapeSummary::get_or_conservative(
                &summaries,
                &parsed.module.ctx,
                *call.callee(),
            );

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
                PtrEscapeSummary::get_or_conservative(&summaries, &parsed.module.ctx, callee)
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
        assert_eq!(ret_args(g, 0), vec![0]);
        assert!(!g.return_may_be_non_arg_pointer(0));
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
        assert_eq!(ret_args(f, 0), vec![0]);
        assert!(!f.return_may_be_non_arg_pointer(0));
        assert_eq!(arg_may_be_returned(f), vec![true]);
        assert_eq!(arg_may_escape(f), vec![false]);
    }

    #[test]
    fn ptr_escape_tracks_i256_arg_returned_in_aggregate() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

type @Box = {i256};

func public %box(v0.i256) -> @Box {
block0:
    v1.@Box = insert_value undef.@Box 0.i256 v0;
    return v1;
}
"#,
        );

        let boxed = &summaries["box"];
        assert_eq!(ret_args(boxed, 0), vec![0]);
        assert_eq!(arg_may_be_returned(boxed), vec![true]);
        assert_eq!(arg_may_escape(boxed), vec![false]);
    }

    #[test]
    fn ptr_escape_tracks_i256_malloc_return_as_non_arg_pointer() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %mk() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = ptr_to_int v0 i256;
    return v1;
}
"#,
        );

        let mk = &summaries["mk"];
        assert!(mk.return_may_be_non_arg_pointer(0));
        assert!(ret_args(mk, 0).is_empty());
        assert_eq!(arg_may_be_returned(mk), Vec::<bool>::new());
    }

    #[test]
    fn ptr_escape_keeps_i256_arg_store_into_local_malloc_local() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %scratch(v0.i256) {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v0 i256;
    return;
}
"#,
        );

        let scratch = &summaries["scratch"];
        assert_eq!(arg_may_escape(scratch), vec![false]);
        assert!(scratch.arg_store_lattice(0).may_store_local());
        assert!(!scratch.arg_store_lattice(0).may_store_nonlocal());
    }

    #[test]
    fn ptr_escape_marks_i256_arg_stored_into_returned_malloc_as_escaping() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %box(v0.i256) -> i256 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v0 i256;
    return v2;
}
"#,
        );

        let boxed = &summaries["box"];
        assert!(boxed.return_may_be_non_arg_pointer(0));
        assert_eq!(arg_may_escape(boxed), vec![true]);
        assert_eq!(arg_may_be_returned(boxed), vec![false]);
    }

    #[test]
    fn ptr_escape_closes_escaping_malloc_contents() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %box(v0.i256) -> i256 {
block0:
    v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 v0 i256;
    v3.*i8 = evm_malloc 32.i256;
    v4.i256 = ptr_to_int v3 i256;
    mstore v4 v2 i256;
    return v4;
}
"#,
        );

        let boxed = &summaries["box"];
        assert!(boxed.return_may_be_non_arg_pointer(0));
        assert_eq!(arg_may_escape(boxed), vec![true]);
        assert_eq!(arg_may_be_returned(boxed), vec![false]);
    }

    #[test]
    fn conservative_unknown_treats_i256_returns_as_pointer_carriers() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    return 0.i256;
}
"#,
        )
        .expect("module parses");
        let f = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func| parsed.module.ctx.func_sig(func, |sig| sig.name() == "f"))
            .expect("function exists");

        let summary = PtrEscapeSummary::conservative_unknown_ctx(&parsed.module.ctx, f);
        assert!(summary.return_may_be_non_arg_pointer(0));
        assert_eq!(ret_args(&summary, 0), vec![0]);
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
        assert!(f.return_may_be_non_arg_pointer(0));
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

    #[test]
    fn ptr_escape_no_transitive_closure_over_arg_store_targets() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %capture(v0.*i8, v1.**i8) {
block0:
    mstore v1 v0 *i8;
    return;
}

func public %forward(v0.*i8, v1.**i8, v2.***i8) {
block0:
    call %capture v0 v1;
    call %capture v1 v2;
    return;
}
"#,
        );

        let forward = &summaries["forward"];
        assert_eq!(
            arg_store_targets(forward, 0),
            vec![1],
            "arg 0 stores to arg 1 only; no transitive closure to arg 2"
        );
        assert_eq!(
            arg_store_targets(forward, 1),
            vec![2],
            "arg 1 stores to arg 2 only"
        );
        assert_eq!(
            arg_may_escape(forward),
            vec![false, false, false],
            "no arg should be unconditionally nonlocal"
        );
    }

    #[test]
    fn ptr_escape_mcopy_from_arg_attributes_stored_content_not_source_address() {
        let src = r#"
target = "evm-ethereum-osaka"

func public %relay(v0.*i8, v1.**i8, v2.**i8) {
block0:
    mstore v1 v0 *i8;
    evm_mcopy v2 v1 32.i256;
    return;
}

func public %top_local(v0.*i8) {
block0:
    v1.**i8 = alloca *i8;
    v2.**i8 = alloca *i8;
    call %relay v0 v1 v2;
    return;
}

func public %top_nonlocal_dest(v0.*i8, v1.**i8) {
block0:
    v2.**i8 = alloca *i8;
    call %relay v0 v2 v1;
    return;
}
"#;
        let (summaries, _) = compute(src);

        let relay = &summaries["relay"];
        // arg 0's value was stored at *arg1, then mcopy'd to *arg2.
        // The summary should attribute the escape to arg 0 (the content),
        // NOT to arg 1 (the source address).
        assert_eq!(
            arg_store_targets(relay, 0),
            vec![1, 2],
            "arg 0 should flow to both arg 1 (via mstore) and arg 2 (via mcopy of *arg1)"
        );
        assert!(
            !relay.arg_store_targets(1).contains(&2),
            "arg 1 (source address) should NOT be recorded as storing to arg 2"
        );
        assert_eq!(
            arg_may_escape(relay),
            vec![false, false, false],
            "no arg should be unconditionally nonlocal"
        );

        // When both the mstore dest and mcopy dest are caller-local,
        // no escape should be reported.
        assert!(
            !call_arg_may_escape_from_src(src, "top_local", 0),
            "arg 0 should not escape when all destinations are caller-local"
        );

        // When the mcopy destination is nonlocal, arg 0 should escape.
        assert!(
            call_arg_may_escape_from_src(src, "top_nonlocal_dest", 0),
            "arg 0 should escape when mcopy destination is nonlocal"
        );
    }

    #[test]
    fn ptr_escape_mcopy_from_local_to_arg_tracks_content() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %copy_out(v0.*i8, v1.**i8) {
block0:
    v2.**i8 = alloca *i8;
    mstore v2 v0 *i8;
    evm_mcopy v1 v2 32.i256;
    return;
}
"#,
        );

        let f = &summaries["copy_out"];
        // arg 0 was stored to local memory, then mcopy'd to *arg 1.
        // The local branch of mcopy should attribute this to arg 0.
        assert_eq!(
            arg_store_targets(f, 0),
            vec![1],
            "arg 0 should escape through arg 1 via local-to-arg mcopy"
        );
        assert_eq!(
            arg_may_escape(f),
            vec![false, false],
            "no arg should be unconditionally nonlocal"
        );
    }

    #[test]
    fn ptr_escape_mcopy_from_arg_to_local_keeps_escape_local() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %copy_local(v0.*i8, v1.**i8) {
block0:
    mstore v1 v0 *i8;
    v2.**i8 = alloca *i8;
    evm_mcopy v2 v1 32.i256;
    return;
}
"#,
        );

        let f = &summaries["copy_local"];
        assert_eq!(arg_store_targets(f, 0), vec![1]);
        assert!(f.arg_store_lattice(0).may_store_local());
        assert!(f.arg_store_lattice(0).may_store_to_arg());
        assert!(!f.arg_store_lattice(0).may_store_nonlocal());
        assert_eq!(arg_may_escape(f), vec![false, false]);
    }

    #[test]
    fn ptr_escape_mstore8_uses_destination_provenance_like_mstore() {
        let (summaries, _) = compute(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.*i8, v1.*i8, v2.i1) {
block0:
    v3.i256 = ptr_to_int v0 i256;
    br v2 block1 block2;

block1:
    evm_mstore8 v1 v3;
    return;

block2:
    v4.*i8 = alloca i8;
    evm_mstore8 v4 v3;
    return;
}
"#,
        );

        let f = &summaries["f"];
        assert_eq!(arg_store_targets(f, 0), vec![1]);
        assert!(f.arg_store_lattice(0).may_store_local());
        assert!(f.arg_store_lattice(0).may_store_to_arg());
        assert!(!f.arg_store_lattice(0).may_store_nonlocal());
        assert_eq!(arg_may_escape(f), vec![false, false, false]);
    }
}
