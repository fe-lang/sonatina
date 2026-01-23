use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    Function, Immediate, InstId, InstSetExt, U256, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use crate::{bitset::BitSet, liveness::InstLiveness};

use super::{
    mem_effects::FuncMemEffects,
    memory_plan::WORD_BYTES,
    provenance::{Provenance, compute_value_provenance},
    ptr_escape::PtrEscapeSummary,
};

pub(crate) const SCRATCH_SPILL_SLOTS: u32 = 2;

const SCRATCH_END_BYTES: u32 = SCRATCH_SPILL_SLOTS * WORD_BYTES;

fn imm_lt_u32(imm: Immediate, bound: u32) -> bool {
    match imm {
        Immediate::I1(val) => (val as u32) < bound,
        Immediate::I8(val) => val >= 0 && (val as u32) < bound,
        Immediate::I16(val) => val >= 0 && (val as u32) < bound,
        Immediate::I32(val) => val >= 0 && (val as u32) < bound,
        Immediate::I64(val) => val >= 0 && (val as u64) < bound as u64,
        Immediate::I128(val) => val >= 0 && (val as u128) < bound as u128,
        Immediate::I256(val) => !val.is_negative() && val.to_u256() < U256::from(bound),
    }
}

fn addr_may_overlap_scratch(
    function: &Function,
    addr: ValueId,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> bool {
    if function.dfg.value_is_imm(addr) {
        let imm = function
            .dfg
            .value_imm(addr)
            .expect("imm value missing payload");
        return imm_lt_u32(imm, SCRATCH_END_BYTES);
    }

    let prov = &prov[addr];
    prov.is_empty() || prov.has_any_arg()
}

pub(crate) fn inst_is_scratch_clobber(
    function: &Function,
    isa: &Evm,
    inst: InstId,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> bool {
    match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
        EvmInstKind::Mstore(mstore) => addr_may_overlap_scratch(function, *mstore.addr(), prov),
        EvmInstKind::EvmMstore8(mstore8) => {
            addr_may_overlap_scratch(function, *mstore8.addr(), prov)
        }
        EvmInstKind::EvmCalldataCopy(copy) => {
            addr_may_overlap_scratch(function, *copy.dst_addr(), prov)
        }
        EvmInstKind::EvmCodeCopy(copy) => {
            addr_may_overlap_scratch(function, *copy.dst_addr(), prov)
        }
        EvmInstKind::EvmExtCodeCopy(copy) => {
            addr_may_overlap_scratch(function, *copy.dst_addr(), prov)
        }
        EvmInstKind::EvmReturnDataCopy(copy) => {
            addr_may_overlap_scratch(function, *copy.dst_addr(), prov)
        }
        EvmInstKind::EvmMcopy(copy) => addr_may_overlap_scratch(function, *copy.dest(), prov),
        EvmInstKind::EvmCall(call) => addr_may_overlap_scratch(function, *call.ret_addr(), prov),
        EvmInstKind::EvmCallCode(call) => {
            addr_may_overlap_scratch(function, *call.ret_addr(), prov)
        }
        EvmInstKind::EvmDelegateCall(call) => {
            addr_may_overlap_scratch(function, *call.ret_addr(), prov)
        }
        EvmInstKind::EvmStaticCall(call) => {
            addr_may_overlap_scratch(function, *call.ret_addr(), prov)
        }
        _ => false,
    }
}

pub(crate) fn compute_scratch_live_values(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    mem_effects: Option<&FxHashMap<FuncRef, FuncMemEffects>>,
    inst_liveness: &InstLiveness,
) -> BitSet<ValueId> {
    let prov = compute_value_provenance(function, module, isa, |callee| {
        ptr_escape.get(&callee).map_or_else(
            || {
                let arg_count = module.func_sig(callee, |sig| sig.args().len());
                vec![true; arg_count]
            },
            |summary| summary.arg_may_be_returned.clone(),
        )
    });

    let mut scratch_live_values: BitSet<ValueId> = BitSet::default();

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let is_barrier = if let Some(call) = function.dfg.call_info(inst) {
                let callee = call.callee();
                mem_effects.map_or(true, |effects| {
                    effects
                        .get(&callee)
                        .copied()
                        .unwrap_or_default()
                        .touches_scratch
                })
            } else {
                inst_is_scratch_clobber(function, isa, inst, &prov)
            };

            if is_barrier {
                scratch_live_values.union_with(inst_liveness.live_out(inst));
                if let Some(def) = function.dfg.inst_result(inst) {
                    scratch_live_values.remove(def);
                }
            }
        }
    }

    scratch_live_values
}
