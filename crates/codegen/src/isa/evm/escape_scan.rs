use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use super::{provenance::Provenance, ptr_escape::PtrEscapeSummary};

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
    pub(crate) inst: InstId,
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
}

pub(crate) fn for_each_escape_event_at_inst<'a>(
    function: &'a Function,
    inst: InstId,
    ctx: EscapeScanCtx<'a>,
    mut visit: impl FnMut(EscapeEvent<'a>),
) {
    let data = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));
    match data {
        EvmInstKind::Return(_) => {
            let Some(ret_args) = function.dfg.return_args(inst) else {
                return;
            };
            for &value in ret_args {
                visit(EscapeEvent {
                    inst,
                    sink: EscapeSink::Return,
                    source: EscapeSource::Value(value),
                });
            }
        }
        EvmInstKind::Mstore(mstore) => {
            if ctx.prov[*mstore.addr()].is_local_addr() {
                return;
            }
            visit(EscapeEvent {
                inst,
                sink: EscapeSink::NonLocalStore,
                source: EscapeSource::Value(*mstore.value()),
            });
        }
        EvmInstKind::EvmMstore8(mstore8) => {
            if ctx.prov[*mstore8.addr()].is_local_addr() {
                return;
            }
            visit(EscapeEvent {
                inst,
                sink: EscapeSink::NonLocalStore,
                source: EscapeSource::Value(*mstore8.val()),
            });
        }
        EvmInstKind::EvmMcopy(mcopy) => {
            if ctx.prov[*mcopy.dest()].is_local_addr() {
                return;
            }
            let addr = *mcopy.addr();
            let src_prov = &ctx.prov[addr];
            if src_prov.is_local_addr() {
                for base in src_prov.alloca_insts() {
                    if let Some(stored) = ctx.local_mem.get(&base) {
                        visit(EscapeEvent {
                            inst,
                            sink: EscapeSink::NonLocalCopy,
                            source: EscapeSource::LocalMem { addr, stored },
                        });
                    }
                }
                return;
            }
            visit(EscapeEvent {
                inst,
                sink: EscapeSink::NonLocalCopy,
                source: EscapeSource::UnknownCopy,
            });
        }
        EvmInstKind::Call(call) => {
            let callee = *call.callee();
            let callee_sum =
                ctx.ptr_escape.get(&callee).cloned().unwrap_or_else(|| {
                    PtrEscapeSummary::conservative_unknown_ctx(ctx.module, callee)
                });
            for (arg_index, &value) in call.args().iter().enumerate() {
                if !callee_sum.call_arg_may_escape_nonlocal(arg_index, call.args(), ctx.prov) {
                    continue;
                }
                visit(EscapeEvent {
                    inst,
                    sink: EscapeSink::CallArg { callee, arg_index },
                    source: EscapeSource::Value(value),
                });
            }
        }
        _ => {}
    }
}
