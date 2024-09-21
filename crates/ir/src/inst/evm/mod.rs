use macros::Inst;
pub mod inst_set;

use crate::{impl_ir_write, value::ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmStop {}
impl_ir_write!(EvmStop);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmAddMod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
    #[inst(value)]
    modulus: ValueId,
}
impl_ir_write!(EvmAddMod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmMulMod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
    #[inst(value)]
    modulus: ValueId,
}
impl_ir_write!(EvmMulMod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExp {
    #[inst(value)]
    base: ValueId,
    #[inst(value)]
    exponent: ValueId,
}
impl_ir_write!(EvmExp);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmByte {
    #[inst(value)]
    pos: ValueId,
    #[inst(value)]
    value: ValueId,
}
impl_ir_write!(EvmByte);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmKeccak256 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_ir_write!(EvmKeccak256);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmAddress {}
impl_ir_write!(EvmAddress);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBalance {
    #[inst(value)]
    contract_addr: ValueId,
}
impl_ir_write!(EvmBalance);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmOrigin {}
impl_ir_write!(EvmOrigin);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCaller {}
impl_ir_write!(EvmCaller);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCallValue {}
impl_ir_write!(EvmCallValue);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCallDataLoad {
    data_offset: ValueId,
}
impl_ir_write!(EvmCallDataLoad);

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
impl_ir_write!(EvmCallDataCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCodeSize {}
impl_ir_write!(EvmCodeSize);

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
impl_ir_write!(EvmCodeCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmGasPrice {}
impl_ir_write!(EvmGasPrice);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExtCodeSize {
    #[inst(value)]
    ext_addr: ValueId,
}
impl_ir_write!(EvmExtCodeSize);

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
impl_ir_write!(EvmExtCodeCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmReturnDataSize {}
impl_ir_write!(EvmReturnDataSize);

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
impl_ir_write!(EvmReturnDataCopy);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmExtCodeHash {
    #[inst(value)]
    ext_addr: ValueId,
}
impl_ir_write!(EvmExtCodeHash);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBlockHash {
    #[inst(value)]
    block_num: ValueId,
}
impl_ir_write!(EvmBlockHash);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmCoinBase {
    #[inst(value)]
    block_num: ValueId,
}
impl_ir_write!(EvmCoinBase);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmTimestamp {}
impl_ir_write!(EvmTimestamp);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmNumber {}
impl_ir_write!(EvmNumber);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmPrevRandao {}
impl_ir_write!(EvmPrevRandao);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmGasLimit {}
impl_ir_write!(EvmGasLimit);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmChainId {}
impl_ir_write!(EvmChainId);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmSelfBalance {}
impl_ir_write!(EvmSelfBalance);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBaseFee {}
impl_ir_write!(EvmBaseFee);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBlobHash {
    #[inst(value)]
    idx: ValueId,
}
impl_ir_write!(EvmBlobHash);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmBlobBaseFee {}
impl_ir_write!(EvmBlobBaseFee);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmMstore8 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    val: ValueId,
}
impl_ir_write!(EvmMstore8);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSload {
    #[inst(value)]
    key: ValueId,
}
impl_ir_write!(EvmSload);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmSstore {
    #[inst(value)]
    key: ValueId,
    #[inst(value)]
    val: ValueId,
}
impl_ir_write!(EvmSstore);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmMsize {}
impl_ir_write!(EvmMsize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct EvmGas {}
impl_ir_write!(EvmGas);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmTload {
    #[inst(value)]
    key: ValueId,
}
impl_ir_write!(EvmTload);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmTstore {
    #[inst(value)]
    key: ValueId,
    #[inst(value)]
    val: ValueId,
}
impl_ir_write!(EvmTstore);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct EvmLog0 {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_ir_write!(EvmLog0);

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
impl_ir_write!(EvmLog1);

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
impl_ir_write!(EvmLog2);

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
impl_ir_write!(EvmLog3);

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
impl_ir_write!(EvmLog4);

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
impl_ir_write!(EvmCreate);

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
impl_ir_write!(EvmCall);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmReturn {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_ir_write!(EvmReturn);

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
impl_ir_write!(EvmDelegateCall);

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
impl_ir_write!(EvmCreate2);

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
impl_ir_write!(EvmStaticCall);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmRevert {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    len: ValueId,
}
impl_ir_write!(EvmRevert);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct EvmSelfDestruct {
    #[inst(value)]
    addr: ValueId,
}
impl_ir_write!(EvmSelfDestruct);
