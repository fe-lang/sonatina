use rustc_hash::FxHashSet;
use sonatina_ir::{
    Function, Immediate, InstId, InstSetExt, U256, ValueId,
    inst::evm::machine_inst_set::EvmMachineInstKind,
    isa::{Isa, evm::EvmMachine},
    module::FuncRef,
};

use crate::{bitset::BitSet, liveness::InstLiveness};

use super::memory_plan::WORD_BYTES;

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
        Immediate::EnumTag { value, .. } => {
            !value.is_negative() && value.to_u256() < U256::from(bound)
        }
    }
}

fn machine_addr_may_overlap_scratch(function: &Function, addr: ValueId) -> bool {
    if function.dfg.value_is_imm(addr) {
        let imm = function
            .dfg
            .value_imm(addr)
            .expect("imm value missing payload");
        imm_lt_u32(imm, SCRATCH_END_BYTES)
    } else {
        true
    }
}

pub(crate) fn machine_inst_is_scratch_clobber(
    function: &Function,
    isa: &EvmMachine,
    inst: InstId,
) -> bool {
    match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
        EvmMachineInstKind::EvmMstore(mstore) => {
            machine_addr_may_overlap_scratch(function, *mstore.addr())
        }
        EvmMachineInstKind::EvmMstore8(mstore8) => {
            machine_addr_may_overlap_scratch(function, *mstore8.addr())
        }
        EvmMachineInstKind::EvmCalldataCopy(copy) => {
            machine_addr_may_overlap_scratch(function, *copy.dst_addr())
        }
        EvmMachineInstKind::EvmCodeCopy(copy) => {
            machine_addr_may_overlap_scratch(function, *copy.dst_addr())
        }
        EvmMachineInstKind::EvmExtCodeCopy(copy) => {
            machine_addr_may_overlap_scratch(function, *copy.dst_addr())
        }
        EvmMachineInstKind::EvmReturnDataCopy(copy) => {
            machine_addr_may_overlap_scratch(function, *copy.dst_addr())
        }
        EvmMachineInstKind::EvmMcopy(copy) => {
            machine_addr_may_overlap_scratch(function, *copy.dest())
        }
        EvmMachineInstKind::EvmCall(call) => {
            machine_addr_may_overlap_scratch(function, *call.ret_addr())
        }
        EvmMachineInstKind::EvmCallCode(call) => {
            machine_addr_may_overlap_scratch(function, *call.ret_addr())
        }
        EvmMachineInstKind::EvmDelegateCall(call) => {
            machine_addr_may_overlap_scratch(function, *call.ret_addr())
        }
        EvmMachineInstKind::EvmStaticCall(call) => {
            machine_addr_may_overlap_scratch(function, *call.ret_addr())
        }
        _ => false,
    }
}

pub(crate) fn compute_machine_scratch_live_values(
    function: &Function,
    isa: &EvmMachine,
    scratch_effects: Option<&FxHashSet<FuncRef>>,
    inst_liveness: &InstLiveness,
) -> BitSet<ValueId> {
    let mut scratch_live_values: BitSet<ValueId> = BitSet::default();

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let is_barrier = if let Some(call) = function.dfg.call_info(inst) {
                let callee = call.callee();
                scratch_effects.is_none_or(|effects| effects.contains(&callee))
            } else {
                machine_inst_is_scratch_clobber(function, isa, inst)
            };

            if is_barrier {
                scratch_live_values.union_with(inst_liveness.live_out(inst));
                for def in function.dfg.inst_results(inst) {
                    scratch_live_values.remove(*def);
                }
            }
        }
    }

    scratch_live_values
}
