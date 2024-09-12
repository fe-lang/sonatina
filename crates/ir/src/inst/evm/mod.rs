use macros::Inst;
pub mod inst_set;

use crate::Value;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmStop {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmAddMod {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
    #[inst(value)]
    modulus: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmMulMod {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
    #[inst(value)]
    modulus: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExp {
    #[inst(value)]
    base: Value,
    #[inst(value)]
    exponent: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmByte {
    #[inst(value)]
    pos: Value,
    #[inst(value)]
    value: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmKeccak256 {
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmAddress {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBalance {
    #[inst(value)]
    contract_addr: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmOrigin {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCaller {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCallValue {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCallDataLoad {
    data_offset: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCallDataCopy {
    #[inst(value)]
    dst_addr: Value,
    #[inst(value)]
    data_offset: Value,
    #[inst(value)]
    len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCodeSize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCodeCopy {
    #[inst(value)]
    dst_addr: Value,
    #[inst(value)]
    code_offset: Value,
    #[inst(value)]
    len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmGasPrice {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExtCodeSize {
    #[inst(value)]
    ext_addr: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmExtCodeCopy {
    #[inst(value)]
    ext_addr: Value,
    #[inst(value)]
    dst_addr: Value,
    #[inst(value)]
    code_offset: Value,
    #[inst(value)]
    len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmReturnDataSize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmReturnDataCopy {
    #[inst(value)]
    dst_addr: Value,
    #[inst(value)]
    data_offset: Value,
    #[inst(value)]
    len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExtCodeHash {
    #[inst(value)]
    ext_addr: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBlockHash {
    #[inst(value)]
    block_num: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCoinBase {
    #[inst(value)]
    block_num: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmTimestamp {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmNumber {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmPrevRandao {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmGasLimit {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmChainId {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmSelfBalance {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBaseFee {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBlobHash {
    #[inst(value)]
    idx: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBlobBaseFee {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmMstore8 {
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    val: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSload {
    #[inst(value)]
    key: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSstore {
    #[inst(value)]
    key: Value,
    #[inst(value)]
    val: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmMsize {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmGas {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmTload {
    #[inst(value)]
    key: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmTstore {
    #[inst(value)]
    key: Value,
    #[inst(value)]
    val: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmLog0 {
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmLog1 {
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
    #[inst(value)]
    topic0: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmLog2 {
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
    #[inst(value)]
    topic0: Value,
    #[inst(value)]
    topic1: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmLog3 {
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
    #[inst(value)]
    topic0: Value,
    #[inst(value)]
    topic1: Value,
    #[inst(value)]
    topic2: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmLog4 {
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
    #[inst(value)]
    topic0: Value,
    #[inst(value)]
    topic1: Value,
    #[inst(value)]
    topic2: Value,
    #[inst(value)]
    topic3: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCreate {
    #[inst(value)]
    val: Value,
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCall {
    #[inst(value)]
    gas: Value,
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    val: Value,
    #[inst(value)]
    arg_addr: Value,
    #[inst(value)]
    arg_len: Value,
    #[inst(value)]
    ret_addr: Value,
    #[inst(value)]
    ret_offset: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmReturn {
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmDelegateCall {
    #[inst(value)]
    gas: Value,
    #[inst(value)]
    ext_addr: Value,
    #[inst(value)]
    arg_addr: Value,
    #[inst(value)]
    arg_len: Value,
    #[inst(value)]
    ret_addr: Value,
    #[inst(value)]
    ret_len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCreate2 {
    #[inst(value)]
    val: Value,
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
    #[inst(value)]
    salt: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmStaticCall {
    #[inst(value)]
    gas: Value,
    #[inst(value)]
    ext_addr: Value,
    #[inst(value)]
    arg_addr: Value,
    #[inst(value)]
    arg_len: Value,
    #[inst(value)]
    ret_addr: Value,
    #[inst(value)]
    ret_len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmRevert {
    #[inst(value)]
    addr: Value,
    #[inst(value)]
    len: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSelfDestruct {
    #[inst(value)]
    addr: Value,
}
