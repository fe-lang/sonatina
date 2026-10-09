#[cfg(test)]
use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, Module, ValueId,
    isa::evm::Evm,
    module::{FuncRef, ModuleCtx},
};

use crate::module_analysis::CallGraphSchedule;

use super::{
    escape_scan::{
        EscapeScanCtx, EscapeSink, PtrTransferEvent, PtrTransferSource,
        escape_source_may_be_heap_derived, for_each_escape_event_at_inst,
        for_each_ptr_transfer_at_inst,
    },
    ptr_provenance::{ArgumentOrigin, Provenance, compute_provenance},
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
    pub(crate) arg_store_targets: SmallVec<[ArgumentOrigin; 4]>,
    pub(crate) source_imprecise: bool,
    pub(crate) stored_heap_pointer: bool,
    pub(crate) stored_unknown_pointer: bool,
}

impl PtrArgEscape {
    fn record_store_to_arg(&mut self, origin: ArgumentOrigin) -> bool {
        self.stores.record_arg() | ArgumentOrigin::join_into(&mut self.arg_store_targets, origin)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct PtrReturnEscape {
    pub(crate) origins: SmallVec<[ArgumentOrigin; 4]>,
    pub(crate) heap_pointer: bool,
    pub(crate) unknown_pointer: bool,
}

impl PtrReturnEscape {
    fn record_arg(&mut self, origin: ArgumentOrigin) -> bool {
        ArgumentOrigin::join_into(&mut self.origins, origin)
    }
}

/// Summary of pointer escape effects at a function boundary.
///
/// Argument store edges are callee-local: [`PtrArgEscape::arg_store_targets`] records only
/// direct writes within the callee body (including single-level callee summary
/// application during SCC fixpoint iteration). No store-edge transitive closure
/// is taken. Heap publication propagates through callees independently of these
/// argument-derived edges.
///
/// Effects that depend on caller context (e.g., whether a destination arg is
/// backed by local memory vs nonlocal memory) must be derived at call sites,
/// either via [`Self::for_each_store_effect`] or by the shared instruction
/// scanner in [`super::escape_scan`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PtrEscapeSummary {
    pub(crate) args: Vec<PtrArgEscape>,
    pub(crate) arg_memory: Vec<(ArgumentOrigin, PtrArgEscape)>,
    pub(crate) returns: Vec<PtrReturnEscape>,
    /// May publish newly allocated or unknown heap storage through memory,
    /// including allocations made by callees. Returned pointers are tracked
    /// separately: a caller may discard them without publishing their storage.
    /// This is conservative for writes through caller-local output arguments.
    pub(crate) may_publish_heap: bool,
}

impl PtrEscapeSummary {
    fn new(arg_count: usize, ret_count: usize) -> Self {
        Self {
            args: vec![PtrArgEscape::default(); arg_count],
            arg_memory: Vec::new(),
            returns: vec![PtrReturnEscape::default(); ret_count],
            may_publish_heap: false,
        }
    }

    pub(crate) fn empty_for_func(module: &ModuleCtx, func: FuncRef) -> Self {
        module.func_sig(func, |sig| Self::new(sig.args().len(), sig.ret_tys().len()))
    }

    pub(crate) fn conservative_unknown_ctx(module: &ModuleCtx, func: FuncRef) -> Self {
        let (arg_count, ret_count) =
            module.func_sig(func, |sig| (sig.args().len(), sig.ret_tys().len()));
        let mut out = Self::new(arg_count, ret_count);
        // An unknown body can allocate and publish memory even without args.
        out.may_publish_heap = true;
        module.func_sig(func, |sig| {
            for (ret_idx, &ret_ty) in sig.ret_tys().iter().enumerate() {
                if ret_ty.is_pointer(module) {
                    out.returns[ret_idx].unknown_pointer = true;
                    for arg_idx in 0..arg_count {
                        let _ =
                            out.returns[ret_idx].record_arg(ArgumentOrigin::value(arg_idx as u32));
                    }
                }
            }

            for (src_idx, &src_ty) in sig.args().iter().enumerate() {
                if !src_ty.is_pointer(module) {
                    continue;
                }

                out.args[src_idx].stored_unknown_pointer = true;
                let _ = out.args[src_idx].stores.record_nonlocal();
                for (dst_idx, &dst_ty) in sig.args().iter().enumerate() {
                    if dst_ty.is_pointer(module) {
                        let _ = out.args[src_idx]
                            .record_store_to_arg(ArgumentOrigin::value(dst_idx as u32));
                    }
                }
            }
        });
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

    fn arg_effect_mut(&mut self, origin: ArgumentOrigin) -> &mut PtrArgEscape {
        if origin.depth == 0 {
            let effect = &mut self.args[origin.index as usize];
            effect.source_imprecise |= !origin.exact;
            return effect;
        }
        let index = if let Some(index) = self
            .arg_memory
            .iter()
            .position(|(old, _)| old.index == origin.index)
        {
            let old = &mut self.arg_memory[index].0;
            old.transitive |= origin.transitive || old.depth != origin.depth;
            old.exact &= origin.exact;
            old.depth = old.depth.min(origin.depth);
            index
        } else {
            self.arg_memory.push((origin, PtrArgEscape::default()));
            self.arg_memory.sort_unstable_by_key(|(origin, _)| *origin);
            self.arg_memory
                .iter()
                .position(|(old, _)| *old == origin)
                .unwrap()
        };
        &mut self.arg_memory[index].1
    }

    pub(crate) fn argument_effects(&self) -> impl Iterator<Item = (ArgumentOrigin, &PtrArgEscape)> {
        self.args
            .iter()
            .enumerate()
            .map(|(index, effect)| {
                let mut origin = ArgumentOrigin::value(index as u32);
                origin.exact = !effect.source_imprecise;
                (origin, effect)
            })
            .chain(
                self.arg_memory
                    .iter()
                    .map(|(origin, effect)| (*origin, effect)),
            )
    }

    #[cfg(test)]
    pub(crate) fn arg_may_escape(&self, src_idx: usize) -> bool {
        self.args
            .get(src_idx)
            .is_some_and(|arg| arg.stores.may_store_nonlocal())
    }

    #[cfg(test)]
    pub(crate) fn arg_may_be_returned(&self, src_idx: usize) -> bool {
        self.returns.iter().any(|ret| {
            ret.origins
                .iter()
                .any(|origin| origin.index == src_idx as u32 && origin.depth == 0)
        })
    }

    #[cfg(test)]
    pub(crate) fn returned_arg_indices(&self, ret_idx: usize) -> Vec<u32> {
        self.returns
            .get(ret_idx)
            .into_iter()
            .flat_map(|ret| &ret.origins)
            .filter_map(|origin| (origin.depth == 0).then_some(origin.index))
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn return_may_be_non_arg_pointer(&self, ret_idx: usize) -> bool {
        self.returns
            .get(ret_idx)
            .is_some_and(|ret| ret.heap_pointer || ret.unknown_pointer)
    }

    #[cfg(test)]
    pub(crate) fn arg_store_targets(&self, src_idx: usize) -> Vec<u32> {
        self.args
            .get(src_idx)
            .into_iter()
            .flat_map(|arg| &arg.arg_store_targets)
            .filter_map(|origin| (origin.depth == 0).then_some(origin.index))
            .collect()
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
                    dst_prov.has_any_arg()
                        || dst_prov.may_reference_heap()
                        || dst_prov.may_be_nonlocal_nonarg_without_malloc()
                })
    }

    #[cfg(test)]
    pub(crate) fn call_arg_store_dest_args<'a>(
        &'a self,
        src_idx: usize,
        call_args: &'a [ValueId],
    ) -> impl Iterator<Item = ValueId> + 'a {
        self.arg_store_targets(src_idx)
            .into_iter()
            .filter_map(move |dst_idx| call_args.get(dst_idx as usize).copied())
    }

    pub(crate) fn for_each_store_effect(&self, mut f: impl FnMut(ArgumentOrigin, ArgumentOrigin)) {
        for (source, effect) in self.argument_effects() {
            for &dest in &effect.arg_store_targets {
                f(source, dest);
            }
        }
    }
}

pub(crate) fn compute_ptr_escape_summaries(
    module: &Module,
    funcs: &[FuncRef],
    isa: &Evm,
) -> FxHashMap<FuncRef, PtrEscapeSummary> {
    let schedule = CallGraphSchedule::compute(module, funcs);

    let mut summaries: FxHashMap<FuncRef, PtrEscapeSummary> = FxHashMap::default();
    for &f in funcs {
        module.func_store.view(f, |func| {
            let sig_arg_count = module.ctx.func_sig(f, |sig| sig.args().len());
            debug_assert_eq!(func.arg_values.len(), sig_arg_count);
        });
        summaries.insert(f, PtrEscapeSummary::empty_for_func(&module.ctx, f));
    }

    for &scc_ref in schedule.topo.iter().rev() {
        let component = schedule.members(scc_ref);
        loop {
            let mut changed = false;
            for &f in component {
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
        for &(origin, ref stored) in &prov_info.arg_mem {
            let effect = summary.arg_effect_mut(origin);
            effect.stored_heap_pointer |= stored.may_reference_heap();
            effect.stored_unknown_pointer |= stored.may_reference_unknown_local();
        }
        let scan_ctx = EscapeScanCtx::new(function, &module.ctx, isa, summaries, &prov_info);
        SummaryComputer {
            function,
            scan_ctx: &scan_ctx,
            summary,
        }
        .compute()
    })
}

struct SummaryComputer<'a> {
    function: &'a Function,
    scan_ctx: &'a EscapeScanCtx<'a>,
    summary: PtrEscapeSummary,
}

impl<'a> SummaryComputer<'a> {
    fn compute(mut self) -> PtrEscapeSummary {
        for block in self.function.layout.iter_block() {
            for inst in self.function.layout.iter_inst(block) {
                for_each_ptr_transfer_at_inst(self.function, inst, self.scan_ctx, |event| {
                    self.record_event(event);
                });
                if !self.summary.may_publish_heap {
                    for_each_escape_event_at_inst(self.function, inst, self.scan_ctx, |event| {
                        self.summary.may_publish_heap |= !matches!(event.sink, EscapeSink::Return)
                            && escape_source_may_be_heap_derived(
                                self.function,
                                self.scan_ctx,
                                &event.source,
                            );
                    });
                    if let Some(call) = self.function.dfg.call_info(inst) {
                        self.summary.may_publish_heap |= PtrEscapeSummary::get_or_conservative(
                            self.scan_ctx.ptr_escape,
                            self.scan_ctx.module,
                            call.callee(),
                        )
                        .may_publish_heap;
                    }
                }
            }
        }
        self.summary
    }

    fn record_event(&mut self, event: PtrTransferEvent<'_>) {
        match event {
            PtrTransferEvent::Return { ret_idx, value } => self.record_return(ret_idx, value),
            PtrTransferEvent::Write {
                dest_prov, source, ..
            } => match source {
                PtrTransferSource::Value(value) => {
                    self.record_provenance_write(&self.scan_ctx.prov_info.value[value], dest_prov);
                }
                PtrTransferSource::Memory { stored, .. } => {
                    self.record_provenance_write(&stored, dest_prov);
                }
            },
            PtrTransferEvent::CallArgEscape { stored, .. } => {
                for origin in stored.argument_origins() {
                    self.summary.arg_effect_mut(origin).stores.record_nonlocal();
                }
            }
            PtrTransferEvent::CallArgStore {
                stored, dest_prov, ..
            } => {
                self.record_provenance_write(&stored, &dest_prov);
            }
        }
    }

    fn record_return(&mut self, ret_idx: usize, value: ValueId) {
        let ret_prov = &self.scan_ctx.prov_info.value[value];
        if let Some(ret) = self.summary.returns.get_mut(ret_idx) {
            ret.heap_pointer |= ret_prov.may_reference_heap();
            ret.unknown_pointer |= ret_prov.may_reference_unknown_local()
                || (self
                    .function
                    .dfg
                    .value_ty(value)
                    .is_pointer(self.scan_ctx.module)
                    && ret_prov.is_empty());
            for origin in ret_prov.argument_origins() {
                ret.record_arg(origin);
            }
        }
    }

    fn record_provenance_write(&mut self, src: &Provenance, dest: &Provenance) {
        for origin in src.argument_origins() {
            let effect = self.summary.arg_effect_mut(origin);
            if dest.is_local_addr() || dest.malloc_insts().next().is_some() {
                effect.stores.record_local();
            }
            for target in dest.argument_origins() {
                effect.record_store_to_arg(target);
            }
            if dest.may_be_nonlocal_nonarg_without_malloc()
                || dest
                    .malloc_insts()
                    .any(|malloc| self.scan_ctx.escaping_mallocs.contains(&malloc))
            {
                effect.stores.record_nonlocal();
            }
        }
    }
}

#[cfg(test)]
mod tests;
