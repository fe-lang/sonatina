use macros::Inst;
pub mod inst_set;

use crate::{module::FuncRef, value::ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmUdiv {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmSdiv {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmUmod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmSmod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
#[inst(terminator)]
pub struct EvmStop {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
#[inst(terminator)]
pub struct EvmInvalid {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmAddMod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
    #[inst(value)]
    modulus: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmMulMod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
    #[inst(value)]
    modulus: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExp {
    #[inst(value)]
    base: ValueId,
    #[inst(value)]
    exponent: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmByte {
    #[inst(value)]
    pos: ValueId,
    #[inst(value)]
    value: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmKeccak256 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmAddress {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmBalance {
    #[inst(value)]
    contract_addr: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmOrigin {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmCaller {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmCallValue {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmCallDataLoad {
    data_offset: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmCallDataSize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCallDataCopy {
    #[inst(value)]
    dst_addr: ValueId,
    #[inst(value)]
    data_offset: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmCodeSize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCodeCopy {
    #[inst(value)]
    dst_addr: ValueId,
    #[inst(value)]
    code_offset: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmGasPrice {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmExtCodeSize {
    #[inst(value)]
    ext_addr: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmExtCodeCopy {
    #[inst(value)]
    ext_addr: ValueId,
    #[inst(value)]
    dst_addr: ValueId,
    #[inst(value)]
    code_offset: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmReturnDataSize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmReturnDataCopy {
    #[inst(value)]
    dst_addr: ValueId,
    #[inst(value)]
    data_offset: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmExtCodeHash {
    #[inst(value)]
    ext_addr: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmBlockHash {
    #[inst(value)]
    block_num: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmCoinBase {
    #[inst(value)]
    block_num: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmTimestamp {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmNumber {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmPrevRandao {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmGasLimit {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmChainId {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmSelfBalance {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmBaseFee {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmBlobHash {
    #[inst(value)]
    idx: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmBlobBaseFee {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmMstore8 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    val: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmSload {
    #[inst(value)]
    key: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmSstore {
    #[inst(value)]
    key: ValueId,
    #[inst(value)]
    val: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmMsize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmGas {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmTload {
    #[inst(value)]
    key: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmTstore {
    #[inst(value)]
    key: ValueId,
    #[inst(value)]
    val: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmMcopy {
    #[inst(value)]
    dest: ValueId,
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog0 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog1 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
    #[inst(value)]
    topic0: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog2 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
    #[inst(value)]
    topic0: ValueId,
    #[inst(value)]
    topic1: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog3 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
    #[inst(value)]
    topic0: ValueId,
    #[inst(value)]
    topic1: ValueId,
    #[inst(value)]
    topic2: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog4 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
    #[inst(value)]
    topic0: ValueId,
    #[inst(value)]
    topic1: ValueId,
    #[inst(value)]
    topic2: ValueId,
    #[inst(value)]
    topic3: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCreate {
    #[inst(value)]
    val: ValueId,
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCall {
    #[inst(value)]
    gas: ValueId,
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    val: ValueId,
    #[inst(value)]
    arg_addr: ValueId,
    #[inst(value)]
    arg_len: ValueId,
    #[inst(value)]
    ret_addr: ValueId,
    #[inst(value)]
    ret_offset: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCallCode {
    #[inst(value)]
    gas: ValueId,
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    val: ValueId,
    #[inst(value)]
    arg_addr: ValueId,
    #[inst(value)]
    arg_len: ValueId,
    #[inst(value)]
    ret_addr: ValueId,
    #[inst(value)]
    ret_offset: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
#[inst(terminator)]
pub struct EvmReturn {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmDelegateCall {
    #[inst(value)]
    gas: ValueId,
    #[inst(value)]
    ext_addr: ValueId,
    #[inst(value)]
    arg_addr: ValueId,
    #[inst(value)]
    arg_len: ValueId,
    #[inst(value)]
    ret_addr: ValueId,
    #[inst(value)]
    ret_len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCreate2 {
    #[inst(value)]
    val: ValueId,
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
    #[inst(value)]
    salt: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmStaticCall {
    #[inst(value)]
    gas: ValueId,
    #[inst(value)]
    ext_addr: ValueId,
    #[inst(value)]
    arg_addr: ValueId,
    #[inst(value)]
    arg_len: ValueId,
    #[inst(value)]
    ret_addr: ValueId,
    #[inst(value)]
    ret_len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
#[inst(terminator)]
pub struct EvmRevert {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
#[inst(terminator)]
pub struct EvmSelfDestruct {
    #[inst(value)]
    addr: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmMalloc {
    #[inst(value)]
    size: ValueId,
}

/// An instruction that takes the main function of a contract
/// as an argument and returns the size of the contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmContractSize {
    contract: FuncRef,
}
