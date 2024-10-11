use macros::Inst;
pub mod inst_set;

use crate::{inst::impl_inst_write, value::ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmStop {}
impl_inst_write!(EvmStop);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmAddMod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
    #[inst(value)]
    modulus: ValueId,
}
impl_inst_write!(EvmAddMod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmMulMod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
    #[inst(value)]
    modulus: ValueId,
}
impl_inst_write!(EvmMulMod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExp {
    #[inst(value)]
    base: ValueId,
    #[inst(value)]
    exponent: ValueId,
}
impl_inst_write!(EvmExp);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmByte {
    #[inst(value)]
    pos: ValueId,
    #[inst(value)]
    value: ValueId,
}
impl_inst_write!(EvmByte);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmKeccak256 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_inst_write!(EvmKeccak256);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmAddress {}
impl_inst_write!(EvmAddress);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmBalance {
    #[inst(value)]
    contract_addr: ValueId,
}
impl_inst_write!(EvmBalance);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmOrigin {}
impl_inst_write!(EvmOrigin);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCaller {}
impl_inst_write!(EvmCaller);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCallValue {}
impl_inst_write!(EvmCallValue);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCallDataLoad {
    data_offset: ValueId,
}
impl_inst_write!(EvmCallDataLoad);

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
impl_inst_write!(EvmCallDataCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCodeSize {}
impl_inst_write!(EvmCodeSize);

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
impl_inst_write!(EvmCodeCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmGasPrice {}
impl_inst_write!(EvmGasPrice);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmExtCodeSize {
    #[inst(value)]
    ext_addr: ValueId,
}
impl_inst_write!(EvmExtCodeSize);

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
impl_inst_write!(EvmExtCodeCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmReturnDataSize {}
impl_inst_write!(EvmReturnDataSize);

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
impl_inst_write!(EvmReturnDataCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmExtCodeHash {
    #[inst(value)]
    ext_addr: ValueId,
}
impl_inst_write!(EvmExtCodeHash);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmBlockHash {
    #[inst(value)]
    block_num: ValueId,
}
impl_inst_write!(EvmBlockHash);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmCoinBase {
    #[inst(value)]
    block_num: ValueId,
}
impl_inst_write!(EvmCoinBase);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmTimestamp {}
impl_inst_write!(EvmTimestamp);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmNumber {}
impl_inst_write!(EvmNumber);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmPrevRandao {}
impl_inst_write!(EvmPrevRandao);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmGasLimit {}
impl_inst_write!(EvmGasLimit);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmChainId {}
impl_inst_write!(EvmChainId);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSelfBalance {}
impl_inst_write!(EvmSelfBalance);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmBaseFee {}
impl_inst_write!(EvmBaseFee);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmBlobHash {
    #[inst(value)]
    idx: ValueId,
}
impl_inst_write!(EvmBlobHash);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmBlobBaseFee {}
impl_inst_write!(EvmBlobBaseFee);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmMstore8 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    val: ValueId,
}
impl_inst_write!(EvmMstore8);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSload {
    #[inst(value)]
    key: ValueId,
}
impl_inst_write!(EvmSload);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSstore {
    #[inst(value)]
    key: ValueId,
    #[inst(value)]
    val: ValueId,
}
impl_inst_write!(EvmSstore);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmMsize {}
impl_inst_write!(EvmMsize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmGas {}
impl_inst_write!(EvmGas);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmTload {
    #[inst(value)]
    key: ValueId,
}
impl_inst_write!(EvmTload);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmTstore {
    #[inst(value)]
    key: ValueId,
    #[inst(value)]
    val: ValueId,
}
impl_inst_write!(EvmTstore);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmLog0 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_inst_write!(EvmLog0);

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
impl_inst_write!(EvmLog1);

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
impl_inst_write!(EvmLog2);

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
impl_inst_write!(EvmLog3);

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
impl_inst_write!(EvmLog4);

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
impl_inst_write!(EvmCreate);

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
impl_inst_write!(EvmCall);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmReturn {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_inst_write!(EvmReturn);

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
impl_inst_write!(EvmDelegateCall);

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
impl_inst_write!(EvmCreate2);

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
impl_inst_write!(EvmStaticCall);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmRevert {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_inst_write!(EvmRevert);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmSelfDestruct {
    #[inst(value)]
    addr: ValueId,
}
impl_inst_write!(EvmSelfDestruct);
