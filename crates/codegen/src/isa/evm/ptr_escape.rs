use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, InstSetExt, Module, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use crate::module_analysis::CallGraphSchedule;

use super::{
    escape_scan::{
        EscapeScanCtx, PtrTransferEvent, PtrTransferSource, for_each_ptr_transfer_at_inst,
    },
    ptr_provenance::{Provenance, compute_provenance, type_can_carry_pointer_provenance},
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
/// backed by local memory vs nonlocal memory) must be derived at call sites,
/// either via [`Self::for_each_store_effect`] or by the shared instruction
/// scanner in [`super::escape_scan`].
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
                if ret_ty.is_pointer(module) {
                    out.returns[ret_idx].non_arg_pointer = true;
                    for arg_idx in 0..arg_count {
                        let _ = out.returns[ret_idx].record_arg(arg_idx as u32);
                    }
                }
            }

            for (src_idx, &src_ty) in sig.args().iter().enumerate() {
                if !src_ty.is_pointer(module) {
                    continue;
                }

                let _ = out.args[src_idx].stores.record_nonlocal();
                for (dst_idx, &dst_ty) in sig.args().iter().enumerate() {
                    if dst_ty.is_pointer(module) {
                        let _ = out.args[src_idx].record_store_to_arg(dst_idx as u32);
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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ArgOrigins(SmallVec<[u32; 4]>);

impl ArgOrigins {
    fn new() -> Self {
        Self(SmallVec::new())
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn insert(&mut self, idx: u32) -> bool {
        if self.0.contains(&idx) {
            return false;
        }
        self.0.push(idx);
        self.0.sort_unstable();
        true
    }

    fn union_with(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for idx in other.iter() {
            changed |= self.insert(idx);
        }
        changed
    }

    fn iter(&self) -> impl Iterator<Item = u32> + '_ {
        self.0.iter().copied()
    }

    fn source_indices_with(&self, src_prov: &Provenance) -> SmallVec<[usize; 4]> {
        let mut out = SmallVec::new();
        out.extend(src_prov.arg_indices().map(|idx| idx as usize));
        out.extend(self.iter().map(|idx| idx as usize));
        out
    }

    fn from_addr(addr_prov: &Provenance, addr_origins: &Self) -> Self {
        let mut out = Self::new();
        for idx in addr_prov.arg_indices() {
            let _ = out.insert(idx);
        }
        let _ = out.union_with(addr_origins);
        out
    }

    fn is_only_forwarded_addr_for(&self, addr_prov: &Provenance) -> bool {
        !self.is_empty() && addr_prov.has_no_known_bases() && !addr_prov.is_unknown_ptr()
    }
}

struct ArgForwardingState<'a> {
    function: &'a Function,
    module: &'a ModuleCtx,
    isa: &'a Evm,
    summaries: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
    prov: &'a SecondaryMap<ValueId, Provenance>,
    origins: SecondaryMap<ValueId, ArgOrigins>,
    local_mem: FxHashMap<InstId, ArgOrigins>,
    arg_mem: Vec<ArgOrigins>,
}

impl<'a> ArgForwardingState<'a> {
    fn new(
        function: &'a Function,
        module: &'a ModuleCtx,
        isa: &'a Evm,
        summaries: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
        prov: &'a SecondaryMap<ValueId, Provenance>,
    ) -> Self {
        let mut origins: SecondaryMap<ValueId, ArgOrigins> = SecondaryMap::new();
        for value in function.dfg.value_ids() {
            let _ = &mut origins[value];
        }
        for (idx, &arg) in function.arg_values.iter().enumerate() {
            if type_can_carry_pointer_provenance(module, function.dfg.value_ty(arg)) {
                let _ = origins[arg].insert(idx as u32);
            }
        }

        Self {
            function,
            module,
            isa,
            summaries,
            prov,
            origins,
            local_mem: FxHashMap::default(),
            arg_mem: vec![ArgOrigins::new(); function.arg_values.len()],
        }
    }

    fn compute(mut self) -> SecondaryMap<ValueId, ArgOrigins> {
        let mut changed = true;
        while changed {
            changed = false;
            for block in self.function.layout.iter_block() {
                for inst in self.function.layout.iter_inst(block) {
                    changed |= self.visit_inst(inst);
                }
            }
        }
        self.origins
    }

    fn visit_inst(&mut self, inst: InstId) -> bool {
        let data = self
            .isa
            .inst_set()
            .resolve_inst(self.function.dfg.inst(inst));

        if let EvmInstKind::Mstore(mstore) = &data {
            return self.store_value_to_addr(*mstore.addr(), *mstore.value());
        }

        if let EvmInstKind::Call(call) = &data {
            let mut changed = false;
            let summary =
                PtrEscapeSummary::get_or_conservative(self.summaries, self.module, *call.callee());
            let args = call.args();
            summary.for_each_store_effect(args, |src_idx, dst_actual| {
                if let Some(&src_actual) = args.get(src_idx) {
                    changed |= self.store_value_to_addr(dst_actual, src_actual);
                }
            });

            for (ret_idx, &def) in self.function.dfg.inst_results(inst).iter().enumerate() {
                if type_can_carry_pointer_provenance(self.module, self.function.dfg.value_ty(def)) {
                    let mut next = ArgOrigins::new();
                    for &idx in summary.returned_arg_indices(ret_idx) {
                        if let Some(&arg) = args.get(idx as usize) {
                            let _ = next.union_with(&self.origins[arg]);
                        }
                    }
                    changed |= self.set_origins(def, next);
                }
            }
            return changed;
        }

        let [def] = self.function.dfg.inst_results(inst) else {
            return false;
        };
        if !type_can_carry_pointer_provenance(self.module, self.function.dfg.value_ty(*def)) {
            return false;
        }

        self.set_origins(*def, self.compute_inst_origins(inst, data))
    }

    fn compute_inst_origins(&self, inst: InstId, data: EvmInstKind<'_>) -> ArgOrigins {
        let mut next = ArgOrigins::new();
        match data {
            EvmInstKind::Mload(mload) => {
                let _ = next.union_with(&self.load_from_addr(*mload.addr()));
            }
            EvmInstKind::Phi(phi) => {
                for (value, _) in phi.args().iter() {
                    let _ = next.union_with(&self.origins[*value]);
                }
            }
            EvmInstKind::Gep(gep) => {
                if let Some(&base) = gep.values().first() {
                    let _ = next.union_with(&self.origins[base]);
                }
            }
            EvmInstKind::Bitcast(bc) => {
                let _ = next.union_with(&self.origins[*bc.from()]);
            }
            EvmInstKind::IntToPtr(i2p) => {
                let _ = next.union_with(&self.origins[*i2p.from()]);
            }
            EvmInstKind::PtrToInt(p2i) => {
                let _ = next.union_with(&self.origins[*p2i.from()]);
            }
            EvmInstKind::InsertValue(iv) => {
                let _ = next.union_with(&self.origins[*iv.dest()]);
                let _ = next.union_with(&self.origins[*iv.value()]);
            }
            EvmInstKind::ExtractValue(ev) => {
                let _ = next.union_with(&self.origins[*ev.dest()]);
            }
            EvmInstKind::Add(_)
            | EvmInstKind::Sub(_)
            | EvmInstKind::Mul(_)
            | EvmInstKind::And(_)
            | EvmInstKind::Or(_)
            | EvmInstKind::Xor(_)
            | EvmInstKind::Shl(_)
            | EvmInstKind::Shr(_)
            | EvmInstKind::Sar(_)
            | EvmInstKind::Not(_)
            | EvmInstKind::Sext(_)
            | EvmInstKind::Zext(_)
            | EvmInstKind::Trunc(_)
            | EvmInstKind::EvmSdiv(_)
            | EvmInstKind::EvmUdiv(_)
            | EvmInstKind::EvmUmod(_)
            | EvmInstKind::EvmSmod(_)
            | EvmInstKind::EvmAddMod(_)
            | EvmInstKind::EvmMulMod(_)
            | EvmInstKind::EvmExp(_)
            | EvmInstKind::EvmSignExtend(_)
            | EvmInstKind::EvmByte(_)
            | EvmInstKind::EvmClz(_) => {
                self.function.dfg.inst(inst).for_each_value(&mut |value| {
                    let _ = next.union_with(&self.origins[value]);
                });
            }
            _ => {}
        }
        next
    }

    fn store_value_to_addr(&mut self, addr: ValueId, value: ValueId) -> bool {
        self.store_origins_to_addr(addr, self.origins[value].clone())
    }

    fn store_origins_to_addr(&mut self, addr: ValueId, val_origins: ArgOrigins) -> bool {
        let mut changed = false;
        let addr_prov = &self.prov[addr];
        if addr_prov.is_local_addr() {
            for base in addr_prov.alloca_insts() {
                changed |= self
                    .local_mem
                    .entry(base)
                    .or_default()
                    .union_with(&val_origins);
            }
        }

        for idx in ArgOrigins::from_addr(addr_prov, &self.origins[addr]).iter() {
            if let Some(slot) = self.arg_mem.get_mut(idx as usize) {
                changed |= slot.union_with(&val_origins);
            }
        }
        changed
    }

    fn load_from_addr(&self, addr: ValueId) -> ArgOrigins {
        let mut out = ArgOrigins::new();
        let addr_prov = &self.prov[addr];
        if addr_prov.is_local_addr() {
            for base in addr_prov.alloca_insts() {
                if let Some(stored) = self.local_mem.get(&base) {
                    let _ = out.union_with(stored);
                }
            }
        }

        for idx in ArgOrigins::from_addr(addr_prov, &self.origins[addr]).iter() {
            if let Some(stored) = self.arg_mem.get(idx as usize) {
                let _ = out.union_with(stored);
            }
        }
        out
    }

    fn set_origins(&mut self, value: ValueId, next: ArgOrigins) -> bool {
        if self.origins[value] == next {
            return false;
        }
        self.origins[value] = next;
        true
    }
}

fn compute_arg_forwarding(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    summaries: &FxHashMap<FuncRef, PtrEscapeSummary>,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> SecondaryMap<ValueId, ArgOrigins> {
    ArgForwardingState::new(function, module, isa, summaries, prov).compute()
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
        let summary = PtrEscapeSummary::empty_for_func(&module.ctx, func);

        let prov_info = compute_provenance(function, &module.ctx, isa, |callee| {
            PtrEscapeSummary::get_or_conservative(summaries, &module.ctx, callee)
        });
        let prov = &prov_info.value;
        let local_mem = &prov_info.local_mem;
        let arg_mem = &prov_info.arg_mem;
        let arg_origins = compute_arg_forwarding(function, &module.ctx, isa, summaries, prov);
        let scan_ctx = EscapeScanCtx {
            module: &module.ctx,
            isa,
            ptr_escape: summaries,
            prov,
            local_mem,
            arg_mem,
        };

        let malloc_escape = compute_local_malloc_escape(scan_ctx, function, &arg_origins);
        SummaryComputer {
            function,
            scan_ctx,
            arg_origins: &arg_origins,
            malloc_escape: &malloc_escape,
            summary,
        }
        .compute()
    })
}

struct SummaryComputer<'a> {
    function: &'a Function,
    scan_ctx: EscapeScanCtx<'a>,
    arg_origins: &'a SecondaryMap<ValueId, ArgOrigins>,
    malloc_escape: &'a LocalMallocEscape,
    summary: PtrEscapeSummary,
}

impl<'a> SummaryComputer<'a> {
    fn compute(mut self) -> PtrEscapeSummary {
        for block in self.function.layout.iter_block() {
            for inst in self.function.layout.iter_inst(block) {
                for_each_ptr_transfer_at_inst(self.function, inst, self.scan_ctx, |event| {
                    self.record_event(event);
                });
            }
        }
        self.summary
    }

    fn record_event(&mut self, event: PtrTransferEvent<'a>) {
        match event {
            PtrTransferEvent::Return { ret_idx, value } => self.record_return(ret_idx, value),
            PtrTransferEvent::Write {
                dest,
                dest_prov,
                source,
                ..
            } => match source {
                PtrTransferSource::Value(value) => self.record_value_write(value, dest_prov, dest),
                PtrTransferSource::LocalMem { stored, .. }
                | PtrTransferSource::ArgMem { stored } => {
                    self.record_provenance_write(stored, dest_prov, dest);
                }
                PtrTransferSource::UnknownCopy => {}
            },
            PtrTransferEvent::CallArgEscape { value, .. } => {
                for arg_idx in self.arg_sources(value) {
                    self.summary.record_store_nonlocal(arg_idx);
                }
            }
            PtrTransferEvent::CallArgStore {
                value,
                dest,
                dest_prov,
                ..
            } => self.record_value_write(value, dest_prov, dest),
        }
    }

    fn record_return(&mut self, ret_idx: usize, value: ValueId) {
        let ret_prov = &self.scan_ctx.prov[value];
        if ret_prov.is_unknown_ptr()
            || ret_prov.malloc_insts().next().is_some()
            || (self
                .function
                .dfg
                .value_ty(value)
                .is_pointer(self.scan_ctx.module)
                && ret_prov.has_no_known_bases())
        {
            self.summary.record_returned_non_arg_pointer(ret_idx);
        }

        for arg_idx in self.arg_sources(value) {
            self.summary.record_returned_arg(ret_idx, arg_idx);
        }
    }

    fn record_value_write(&mut self, value: ValueId, dst_prov: &Provenance, dst: ValueId) {
        let dst_origins = self.arg_origins[dst].clone();
        for arg_idx in self.arg_sources(value) {
            self.record_arg_write(arg_idx, dst_prov, &dst_origins);
        }
    }

    fn record_provenance_write(
        &mut self,
        src_prov: &Provenance,
        dst_prov: &Provenance,
        dst: ValueId,
    ) {
        let dst_origins = self.arg_origins[dst].clone();
        for arg_idx in src_prov.arg_indices() {
            self.record_arg_write(arg_idx as usize, dst_prov, &dst_origins);
        }
    }

    fn record_arg_write(
        &mut self,
        src_idx: usize,
        dst_prov: &Provenance,
        dst_origins: &ArgOrigins,
    ) {
        if dst_prov.is_local_addr() || dst_prov.malloc_insts().next().is_some() {
            self.summary.record_store_local(src_idx);
        }
        for dst_idx in dst_prov.arg_indices() {
            self.summary.record_store_to_arg(src_idx, dst_idx);
        }
        for dst_idx in dst_origins.iter() {
            self.summary.record_store_to_arg(src_idx, dst_idx);
        }
        if (dst_prov.may_be_nonlocal_nonarg_without_malloc()
            && !dst_origins.is_only_forwarded_addr_for(dst_prov))
            || dst_prov
                .malloc_insts()
                .any(|malloc| self.malloc_escape.escaping.contains(&malloc))
        {
            self.summary.record_store_nonlocal(src_idx);
        }
    }

    fn arg_sources(&self, value: ValueId) -> SmallVec<[usize; 4]> {
        self.arg_origins[value].source_indices_with(&self.scan_ctx.prov[value])
    }
}

#[derive(Default)]
struct LocalMallocEscape {
    contents: FxHashMap<InstId, Provenance>,
    escaping: FxHashSet<InstId>,
}

impl LocalMallocEscape {
    fn record_write(
        &mut self,
        src_prov: &Provenance,
        dst_prov: &Provenance,
        dst_origins: &ArgOrigins,
    ) {
        for malloc in dst_prov.malloc_insts() {
            let _ = self
                .contents
                .entry(malloc)
                .or_default()
                .union_with(src_prov);
        }

        if dst_prov.has_any_arg() {
            self.record_escape(src_prov);
            return;
        }

        if dst_prov.may_be_nonlocal_nonarg_without_malloc()
            && !dst_origins.is_only_forwarded_addr_for(dst_prov)
        {
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
    arg_origins: &SecondaryMap<ValueId, ArgOrigins>,
) -> LocalMallocEscape {
    let mut out = LocalMallocEscape::default();
    let prov = scan_ctx.prov;

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            for_each_ptr_transfer_at_inst(function, inst, scan_ctx, |event| match event {
                PtrTransferEvent::Return { value, .. }
                | PtrTransferEvent::CallArgEscape { value, .. } => out.record_escape(&prov[value]),
                PtrTransferEvent::Write {
                    dest,
                    dest_prov,
                    source,
                    ..
                } => match source {
                    PtrTransferSource::Value(value) => {
                        out.record_write(&prov[value], dest_prov, &arg_origins[dest]);
                    }
                    PtrTransferSource::LocalMem { stored, .. }
                    | PtrTransferSource::ArgMem { stored } => {
                        out.record_write(stored, dest_prov, &arg_origins[dest]);
                    }
                    PtrTransferSource::UnknownCopy => {}
                },
                PtrTransferEvent::CallArgStore {
                    value,
                    dest,
                    dest_prov,
                    ..
                } => {
                    out.record_write(&prov[value], dest_prov, &arg_origins[dest]);
                }
            });
        }
    }

    out.close();
    out
}

#[cfg(test)]
mod tests;
