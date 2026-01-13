use macros::Inst;
pub mod inst_set;

use crate::value::ValueId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmUdiv {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmSdiv {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmUmod {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmSmod {
    lhs: ValueId,
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
    lhs: ValueId,
    rhs: ValueId,
    modulus: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmMulMod {
    lhs: ValueId,
    rhs: ValueId,
    modulus: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExp {
    base: ValueId,
    exponent: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmByte {
    pos: ValueId,
    value: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmClz {
    word: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmKeccak256 {
    addr: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmAddress {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmBalance {
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
pub struct EvmCalldataLoad {
    #[inst(value)]
    data_offset: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmCalldataSize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCalldataCopy {
    dst_addr: ValueId,
    data_offset: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmCodeSize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCodeCopy {
    dst_addr: ValueId,
    code_offset: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmGasPrice {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmExtCodeSize {
    ext_addr: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmExtCodeCopy {
    ext_addr: ValueId,
    dst_addr: ValueId,
    code_offset: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmReturnDataSize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmReturnDataCopy {
    dst_addr: ValueId,
    data_offset: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmExtCodeHash {
    ext_addr: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmBlockHash {
    block_num: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmCoinBase {}

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
    idx: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmBlobBaseFee {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmMstore8 {
    addr: ValueId,
    val: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Read))]
pub struct EvmSload {
    key: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmSstore {
    key: ValueId,
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
    key: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmTstore {
    key: ValueId,
    val: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmMcopy {
    dest: ValueId,
    addr: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog0 {
    addr: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog1 {
    addr: ValueId,
    len: ValueId,
    topic0: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog2 {
    addr: ValueId,
    len: ValueId,
    topic0: ValueId,
    topic1: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog3 {
    addr: ValueId,
    len: ValueId,
    topic0: ValueId,
    topic1: ValueId,
    topic2: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmLog4 {
    addr: ValueId,
    len: ValueId,
    topic0: ValueId,
    topic1: ValueId,
    topic2: ValueId,
    topic3: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCreate {
    val: ValueId,
    addr: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCall {
    gas: ValueId,
    addr: ValueId,
    val: ValueId,
    arg_addr: ValueId,
    arg_len: ValueId,
    ret_addr: ValueId,
    ret_offset: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCallCode {
    gas: ValueId,
    addr: ValueId,
    val: ValueId,
    arg_addr: ValueId,
    arg_len: ValueId,
    ret_addr: ValueId,
    ret_offset: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
#[inst(terminator)]
pub struct EvmReturn {
    addr: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmDelegateCall {
    gas: ValueId,
    ext_addr: ValueId,
    arg_addr: ValueId,
    arg_len: ValueId,
    ret_addr: ValueId,
    ret_len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmCreate2 {
    val: ValueId,
    addr: ValueId,
    len: ValueId,
    salt: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmStaticCall {
    gas: ValueId,
    ext_addr: ValueId,
    arg_addr: ValueId,
    arg_len: ValueId,
    ret_addr: ValueId,
    ret_len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
#[inst(terminator)]
pub struct EvmRevert {
    addr: ValueId,
    len: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
#[inst(terminator)]
pub struct EvmSelfDestruct {
    addr: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(crate::inst::SideEffect::Write))]
pub struct EvmMalloc {
    size: ValueId,
}
