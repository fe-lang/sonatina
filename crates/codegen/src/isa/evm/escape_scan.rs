use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use super::{
    ptr_escape::PtrEscapeSummary,
    ptr_provenance::{Provenance, ProvenanceInfo, memory_store},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PtrWriteKind {
    Store,
    Copy,
}

#[derive(Clone, Debug)]
pub(crate) enum PtrTransferSource {
    Value(ValueId),
    Memory { addr: ValueId, stored: Provenance },
}

#[derive(Clone, Debug)]
pub(crate) enum PtrTransferEvent<'a> {
    Return {
        ret_idx: usize,
        value: ValueId,
    },
    Write {
        kind: PtrWriteKind,
        dest_prov: &'a Provenance,
        source: PtrTransferSource,
    },
    CallArgEscape {
        callee: FuncRef,
        arg_index: usize,
        value: ValueId,
        stored: Provenance,
    },
    CallArgStore {
        callee: FuncRef,
        arg_index: usize,
        value: ValueId,
        stored: Provenance,
        dest_prov: Provenance,
    },
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EscapeSink {
    Return,
    NonLocalStore,
    NonLocalCopy,
    CallArg { callee: FuncRef, arg_index: usize },
}

#[derive(Clone, Debug)]
pub(crate) enum EscapeSource {
    Value(ValueId),
    Memory { addr: ValueId, stored: Provenance },
    CallArgument { value: ValueId, stored: Provenance },
}

#[derive(Clone, Debug)]
pub(crate) struct EscapeEvent {
    pub(crate) sink: EscapeSink,
    pub(crate) source: EscapeSource,
}

pub(crate) struct EscapeScanCtx<'a> {
    pub(crate) module: &'a ModuleCtx,
    pub(crate) isa: &'a Evm,
    pub(crate) ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
    pub(crate) prov_info: &'a ProvenanceInfo,
    pub(crate) escaping_mallocs: FxHashSet<InstId>,
}

impl<'a> EscapeScanCtx<'a> {
    pub(crate) fn new(
        function: &Function,
        module: &'a ModuleCtx,
        isa: &'a Evm,
        ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
        prov_info: &'a ProvenanceInfo,
    ) -> Self {
        let mut ctx = Self {
            module,
            isa,
            ptr_escape,
            prov_info,
            escaping_mallocs: FxHashSet::default(),
        };
        let mut roots = Provenance::default();
        for inst in function.layout.iter_all_insts() {
            for_each_ptr_transfer_at_inst(function, inst, &ctx, |event| {
                let (stored, dest) = match &event {
                    PtrTransferEvent::Return { value, .. } => (&prov_info.value[*value], None),
                    PtrTransferEvent::CallArgEscape { stored, .. } => (stored, None),
                    PtrTransferEvent::Write {
                        dest_prov, source, ..
                    } => {
                        let stored = match source {
                            PtrTransferSource::Value(value) => &prov_info.value[*value],
                            PtrTransferSource::Memory { stored, .. } => stored,
                        };
                        (stored, Some(*dest_prov))
                    }
                    PtrTransferEvent::CallArgStore {
                        stored, dest_prov, ..
                    } => (stored, Some(dest_prov)),
                };
                if dest.is_none_or(|dest| {
                    dest.has_any_arg() || dest.may_be_nonlocal_nonarg_without_malloc()
                }) {
                    roots.union_with(stored);
                }
            });
        }
        let reachable = prov_info.reachable_memory(&roots);
        ctx.escaping_mallocs.extend(reachable.malloc_insts());
        if reachable.is_unknown_ptr() {
            // An unknown escaped address can name any allocation in this
            // function, including a container holding an argument pointer.
            ctx.escaping_mallocs
                .extend(function.layout.iter_all_insts().filter(|&inst| {
                    matches!(
                        isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                        EvmInstKind::EvmMalloc(_)
                    )
                }));
        }
        ctx
    }

    fn is_local_destination(&self, dest: &Provenance) -> bool {
        !dest.has_any_arg()
            && !dest.may_be_nonlocal_nonarg_without_malloc()
            && !dest
                .malloc_insts()
                .any(|malloc| self.escaping_mallocs.contains(&malloc))
    }
}

pub(crate) fn escape_source_may_be_heap_derived(
    function: &Function,
    ctx: &EscapeScanCtx<'_>,
    source: &EscapeSource,
) -> bool {
    match source {
        EscapeSource::Value(value) => {
            ctx.prov_info.value[*value].malloc_insts().next().is_some()
                || ctx.prov_info.value[*value].is_unknown_ptr()
                || (function.dfg.value_ty(*value).is_pointer(ctx.module)
                    && ctx.prov_info.value[*value].has_no_known_bases())
        }
        EscapeSource::Memory { stored, .. } | EscapeSource::CallArgument { stored, .. } => {
            stored.is_unknown_ptr() || stored.malloc_insts().next().is_some()
        }
    }
}

pub(crate) fn for_each_ptr_transfer_at_inst<'a>(
    function: &'a Function,
    inst: InstId,
    ctx: &EscapeScanCtx<'a>,
    mut visit: impl FnMut(PtrTransferEvent<'a>),
) {
    let data = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));
    if let Some((dest, value, _)) = memory_store(&data, ctx.module) {
        visit(PtrTransferEvent::Write {
            kind: PtrWriteKind::Store,
            dest_prov: &ctx.prov_info.value[dest],
            source: PtrTransferSource::Value(value),
        });
        return;
    }
    match data {
        EvmInstKind::Return(_) => {
            let Some(ret_args) = function.dfg.return_args(inst) else {
                return;
            };
            for (ret_idx, &value) in ret_args.iter().enumerate() {
                visit(PtrTransferEvent::Return { ret_idx, value });
            }
        }
        EvmInstKind::EvmMcopy(mcopy) => {
            let dest = *mcopy.dest();
            let addr = *mcopy.addr();
            let src_prov = &ctx.prov_info.value[addr];
            let mut stored = ctx.prov_info.load_memory(src_prov);
            if src_prov.has_no_known_bases() && src_prov.argument_origins().next().is_none() {
                stored.mark_unknown_non_arg();
            }
            visit(PtrTransferEvent::Write {
                kind: PtrWriteKind::Copy,
                dest_prov: &ctx.prov_info.value[dest],
                source: PtrTransferSource::Memory { addr, stored },
            });
        }
        EvmInstKind::Call(call) => {
            let callee = *call.callee();
            let callee_sum =
                PtrEscapeSummary::get_or_conservative(ctx.ptr_escape, ctx.module, callee);

            for (origin, effect) in callee_sum.argument_effects() {
                let arg_index = origin.index as usize;
                let Some(&value) = call.args().get(arg_index) else {
                    continue;
                };
                let stored = ctx.prov_info.resolve_argument(call.args(), origin);
                if effect.stores.may_store_nonlocal() {
                    visit(PtrTransferEvent::CallArgEscape {
                        callee,
                        arg_index,
                        value,
                        stored: stored.clone(),
                    });
                }
                for &dest in &effect.arg_store_targets {
                    let dest_prov = ctx.prov_info.resolve_argument(call.args(), dest);
                    visit(PtrTransferEvent::CallArgStore {
                        callee,
                        arg_index,
                        value,
                        stored: stored.clone(),
                        dest_prov,
                    });
                }
            }
        }
        _ => {}
    }
}

pub(crate) fn for_each_escape_event_at_inst<'a>(
    function: &'a Function,
    inst: InstId,
    ctx: &EscapeScanCtx<'a>,
    mut visit: impl FnMut(EscapeEvent),
) {
    for_each_ptr_transfer_at_inst(function, inst, ctx, |event| match event {
        PtrTransferEvent::Return { value, .. } => visit(EscapeEvent {
            sink: EscapeSink::Return,
            source: EscapeSource::Value(value),
        }),
        PtrTransferEvent::Write {
            kind,
            dest_prov,
            source,
            ..
        } => {
            if ctx.is_local_destination(dest_prov) {
                return;
            }

            match (kind, source) {
                (PtrWriteKind::Store, PtrTransferSource::Value(value)) => visit(EscapeEvent {
                    sink: EscapeSink::NonLocalStore,
                    source: EscapeSource::Value(value),
                }),
                (PtrWriteKind::Copy, PtrTransferSource::Memory { addr, stored }) => {
                    visit(EscapeEvent {
                        sink: EscapeSink::NonLocalCopy,
                        source: EscapeSource::Memory { addr, stored },
                    })
                }
                (PtrWriteKind::Copy, PtrTransferSource::Value(_)) => {
                    unreachable!("copies do not emit direct-value sources")
                }
                (PtrWriteKind::Store, _) => {}
            }
        }
        PtrTransferEvent::CallArgEscape {
            callee,
            arg_index,
            value,
            stored,
        } => {
            visit(EscapeEvent {
                sink: EscapeSink::CallArg { callee, arg_index },
                source: EscapeSource::CallArgument { value, stored },
            });
        }
        PtrTransferEvent::CallArgStore {
            callee,
            arg_index,
            value,
            stored,
            dest_prov,
        } => {
            if !ctx.is_local_destination(&dest_prov) {
                visit(EscapeEvent {
                    sink: EscapeSink::CallArg { callee, arg_index },
                    source: EscapeSource::CallArgument { value, stored },
                });
            }
        }
    });
}
