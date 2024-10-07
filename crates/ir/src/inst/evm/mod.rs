use macros::Inst;
pub mod inst_set;

use crate::{impl_display_with_func, value::ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmStop {}
impl_display_with_func!(EvmStop);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmAddMod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
    #[inst(value)]
    modulus: ValueId,
}
impl_display_with_func!(EvmAddMod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmMulMod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
    #[inst(value)]
    modulus: ValueId,
}
impl_display_with_func!(EvmMulMod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExp {
    #[inst(value)]
    base: ValueId,
    #[inst(value)]
    exponent: ValueId,
}
impl_display_with_func!(EvmExp);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmByte {
    #[inst(value)]
    pos: ValueId,
    #[inst(value)]
    value: ValueId,
}
impl_display_with_func!(EvmByte);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmKeccak256 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_display_with_func!(EvmKeccak256);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmAddress {}
impl_display_with_func!(EvmAddress);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBalance {
    #[inst(value)]
    contract_addr: ValueId,
}
impl_display_with_func!(EvmBalance);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmOrigin {}
impl_display_with_func!(EvmOrigin);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCaller {}
impl_display_with_func!(EvmCaller);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCallValue {}
impl_display_with_func!(EvmCallValue);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCallDataLoad {
    data_offset: ValueId,
}
impl_display_with_func!(EvmCallDataLoad);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCallDataCopy {
    #[inst(value)]
    dst_addr: ValueId,
    #[inst(value)]
    data_offset: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_display_with_func!(EvmCallDataCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCodeSize {}
impl_display_with_func!(EvmCodeSize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCodeCopy {
    #[inst(value)]
    dst_addr: ValueId,
    #[inst(value)]
    code_offset: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_display_with_func!(EvmCodeCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmGasPrice {}
impl_display_with_func!(EvmGasPrice);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExtCodeSize {
    #[inst(value)]
    ext_addr: ValueId,
}
impl_display_with_func!(EvmExtCodeSize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
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
impl_display_with_func!(EvmExtCodeCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmReturnDataSize {}
impl_display_with_func!(EvmReturnDataSize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmReturnDataCopy {
    #[inst(value)]
    dst_addr: ValueId,
    #[inst(value)]
    data_offset: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_display_with_func!(EvmReturnDataCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExtCodeHash {
    #[inst(value)]
    ext_addr: ValueId,
}
impl_display_with_func!(EvmExtCodeHash);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBlockHash {
    #[inst(value)]
    block_num: ValueId,
}
impl_display_with_func!(EvmBlockHash);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCoinBase {
    #[inst(value)]
    block_num: ValueId,
}
impl_display_with_func!(EvmCoinBase);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmTimestamp {}
impl_display_with_func!(EvmTimestamp);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmNumber {}
impl_display_with_func!(EvmNumber);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmPrevRandao {}
impl_display_with_func!(EvmPrevRandao);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmGasLimit {}
impl_display_with_func!(EvmGasLimit);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmChainId {}
impl_display_with_func!(EvmChainId);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmSelfBalance {}
impl_display_with_func!(EvmSelfBalance);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBaseFee {}
impl_display_with_func!(EvmBaseFee);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBlobHash {
    #[inst(value)]
    idx: ValueId,
}
impl_display_with_func!(EvmBlobHash);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBlobBaseFee {}
impl_display_with_func!(EvmBlobBaseFee);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmMstore8 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    val: ValueId,
}
impl_display_with_func!(EvmMstore8);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSload {
    #[inst(value)]
    key: ValueId,
}
impl_display_with_func!(EvmSload);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSstore {
    #[inst(value)]
    key: ValueId,
    #[inst(value)]
    val: ValueId,
}
impl_display_with_func!(EvmSstore);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmMsize {}
impl_display_with_func!(EvmMsize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmGas {}
impl_display_with_func!(EvmGas);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmTload {
    #[inst(value)]
    key: ValueId,
}
impl_display_with_func!(EvmTload);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmTstore {
    #[inst(value)]
    key: ValueId,
    #[inst(value)]
    val: ValueId,
}
impl_display_with_func!(EvmTstore);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmLog0 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_display_with_func!(EvmLog0);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmLog1 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
    #[inst(value)]
    topic0: ValueId,
}
impl_display_with_func!(EvmLog1);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
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
impl_display_with_func!(EvmLog2);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
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
impl_display_with_func!(EvmLog3);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
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
impl_display_with_func!(EvmLog4);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCreate {
    #[inst(value)]
    val: ValueId,
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_display_with_func!(EvmCreate);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
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
impl_display_with_func!(EvmCall);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmReturn {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_display_with_func!(EvmReturn);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
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
impl_display_with_func!(EvmDelegateCall);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
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
impl_display_with_func!(EvmCreate2);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
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
impl_display_with_func!(EvmStaticCall);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmRevert {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_display_with_func!(EvmRevert);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmSelfDestruct {
    #[inst(value)]
    addr: ValueId,
}
impl_display_with_func!(EvmSelfDestruct);
