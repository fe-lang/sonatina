use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use super::{provenance::Provenance, ptr_escape::PtrEscapeSummary};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PtrWriteKind {
    Store,
    Copy,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum PtrTransferSource<'a> {
    Value(ValueId),
    LocalMem {
        addr: ValueId,
        stored: &'a Provenance,
    },
    ArgMem {
        stored: &'a Provenance,
    },
    UnknownCopy,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum PtrTransferEvent<'a> {
    Return {
        value: ValueId,
    },
    Write {
        kind: PtrWriteKind,
        dest_prov: &'a Provenance,
        source: PtrTransferSource<'a>,
    },
    CallArgEscape {
        callee: FuncRef,
        arg_index: usize,
        value: ValueId,
    },
    CallArgStore {
        callee: FuncRef,
        arg_index: usize,
        value: ValueId,
        dest_prov: &'a Provenance,
    },
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EscapeSink {
    Return,
    NonLocalStore,
    NonLocalCopy,
    CallArg { callee: FuncRef, arg_index: usize },
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum EscapeSource<'a> {
    Value(ValueId),
    LocalMem {
        addr: ValueId,
        stored: &'a Provenance,
    },
    UnknownCopy,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct EscapeEvent<'a> {
    pub(crate) sink: EscapeSink,
    pub(crate) source: EscapeSource<'a>,
}

#[derive(Clone, Copy)]
pub(crate) struct EscapeScanCtx<'a> {
    pub(crate) module: &'a ModuleCtx,
    pub(crate) isa: &'a Evm,
    pub(crate) ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
    pub(crate) prov: &'a SecondaryMap<ValueId, Provenance>,
    pub(crate) local_mem: &'a FxHashMap<InstId, Provenance>,
    pub(crate) arg_mem: &'a [Provenance],
}

pub(crate) fn for_each_ptr_transfer_at_inst<'a>(
    function: &'a Function,
    inst: InstId,
    ctx: EscapeScanCtx<'a>,
    mut visit: impl FnMut(PtrTransferEvent<'a>),
) {
    let data = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));
    match data {
        EvmInstKind::Return(_) => {
            let Some(ret_args) = function.dfg.return_args(inst) else {
                return;
            };
            for &value in ret_args {
                visit(PtrTransferEvent::Return { value });
            }
        }
        EvmInstKind::Mstore(mstore) => {
            let dest = *mstore.addr();
            visit(PtrTransferEvent::Write {
                kind: PtrWriteKind::Store,
                dest_prov: &ctx.prov[dest],
                source: PtrTransferSource::Value(*mstore.value()),
            });
        }
        EvmInstKind::EvmMstore8(mstore8) => {
            let dest = *mstore8.addr();
            visit(PtrTransferEvent::Write {
                kind: PtrWriteKind::Store,
                dest_prov: &ctx.prov[dest],
                source: PtrTransferSource::Value(*mstore8.val()),
            });
        }
        EvmInstKind::EvmMcopy(mcopy) => {
            let dest = *mcopy.dest();
            let addr = *mcopy.addr();
            let src_prov = &ctx.prov[addr];
            for base in src_prov.alloca_insts() {
                if let Some(stored) = ctx.local_mem.get(&base) {
                    visit(PtrTransferEvent::Write {
                        kind: PtrWriteKind::Copy,
                        dest_prov: &ctx.prov[dest],
                        source: PtrTransferSource::LocalMem { addr, stored },
                    });
                }
            }
            for arg_index in src_prov.arg_indices() {
                if let Some(stored) = ctx.arg_mem.get(arg_index as usize) {
                    visit(PtrTransferEvent::Write {
                        kind: PtrWriteKind::Copy,
                        dest_prov: &ctx.prov[dest],
                        source: PtrTransferSource::ArgMem { stored },
                    });
                }
            }
            if !src_prov.is_local_addr() {
                visit(PtrTransferEvent::Write {
                    kind: PtrWriteKind::Copy,
                    dest_prov: &ctx.prov[dest],
                    source: PtrTransferSource::UnknownCopy,
                });
            }
        }
        EvmInstKind::Call(call) => {
            let callee = *call.callee();
            let callee_sum =
                ctx.ptr_escape.get(&callee).cloned().unwrap_or_else(|| {
                    PtrEscapeSummary::conservative_unknown_ctx(ctx.module, callee)
                });

            for (arg_index, &value) in call.args().iter().enumerate() {
                if callee_sum.arg_may_escape(arg_index) {
                    visit(PtrTransferEvent::CallArgEscape {
                        callee,
                        arg_index,
                        value,
                    });
                }
                for dest in callee_sum.call_arg_store_dest_args(arg_index, call.args()) {
                    visit(PtrTransferEvent::CallArgStore {
                        callee,
                        arg_index,
                        value,
                        dest_prov: &ctx.prov[dest],
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
    ctx: EscapeScanCtx<'a>,
    mut visit: impl FnMut(EscapeEvent<'a>),
) {
    let mut call_arg_escapes: SmallVec<[(FuncRef, usize, ValueId); 4]> = SmallVec::new();
    for_each_ptr_transfer_at_inst(function, inst, ctx, |event| match event {
        PtrTransferEvent::Return { value } => visit(EscapeEvent {
            sink: EscapeSink::Return,
            source: EscapeSource::Value(value),
        }),
        PtrTransferEvent::Write {
            kind,
            dest_prov,
            source,
            ..
        } => {
            if dest_prov.is_local_addr() {
                return;
            }

            match (kind, source) {
                (PtrWriteKind::Store, PtrTransferSource::Value(value)) => visit(EscapeEvent {
                    sink: EscapeSink::NonLocalStore,
                    source: EscapeSource::Value(value),
                }),
                (PtrWriteKind::Copy, PtrTransferSource::LocalMem { addr, stored }) => {
                    visit(EscapeEvent {
                        sink: EscapeSink::NonLocalCopy,
                        source: EscapeSource::LocalMem { addr, stored },
                    })
                }
                (
                    PtrWriteKind::Copy,
                    PtrTransferSource::ArgMem { .. } | PtrTransferSource::UnknownCopy,
                ) => visit(EscapeEvent {
                    sink: EscapeSink::NonLocalCopy,
                    source: EscapeSource::UnknownCopy,
                }),
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
        } => {
            if !call_arg_escapes.contains(&(callee, arg_index, value)) {
                call_arg_escapes.push((callee, arg_index, value));
            }
        }
        PtrTransferEvent::CallArgStore {
            callee,
            arg_index,
            value,
            dest_prov,
        } => {
            if (dest_prov.has_any_arg() || dest_prov.may_be_nonlocal_nonarg())
                && !call_arg_escapes.contains(&(callee, arg_index, value))
            {
                call_arg_escapes.push((callee, arg_index, value));
            }
        }
    });
    for (callee, arg_index, value) in call_arg_escapes {
        visit(EscapeEvent {
            sink: EscapeSink::CallArg { callee, arg_index },
            source: EscapeSource::Value(value),
        });
    }
}
