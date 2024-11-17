use macros::inst_set;

use crate::inst::*;

#[inst_set(InstKind = "EvmInstKind")]
pub struct EvmInstSet(
    arith::Neg,
    arith::Add,
    arith::Mul,
    arith::Sub,
    arith::Shl,
    arith::Shr,
    arith::Sar,
    cast::Sext,
    cast::Zext,
    cast::Trunc,
    cast::Bitcast,
    cast::IntToPtr,
    cast::PtrToInt,
    cmp::Lt,
    cmp::Gt,
    cmp::Slt,
    cmp::Sgt,
    cmp::Le,
    cmp::Ge,
    cmp::Sge,
    cmp::Eq,
    cmp::Ne,
    cmp::IsZero,
    control_flow::Jump,
    control_flow::Br,
    control_flow::Phi,
    control_flow::BrTable,
    control_flow::Call,
    control_flow::Return,
    data::Mload,
    data::Mstore,
    data::Gep,
    data::Alloca,
    logic::Not,
    logic::And,
    logic::Or,
    logic::Xor,
    evm::EvmSdiv,
    evm::EvmUdiv,
    evm::EvmUmod,
    evm::EvmSmod,
    evm::EvmStop,
    evm::EvmInvalid,
    evm::EvmAddMod,
    evm::EvmMulMod,
    evm::EvmExp,
    evm::EvmByte,
    evm::EvmKeccak256,
    evm::EvmAddress,
    evm::EvmBalance,
    evm::EvmOrigin,
    evm::EvmCaller,
    evm::EvmCallValue,
    evm::EvmCallDataLoad,
    evm::EvmCallDataCopy,
    evm::EvmCallDataSize,
    evm::EvmCodeSize,
    evm::EvmCodeCopy,
    evm::EvmExtCodeCopy,
    evm::EvmReturnDataSize,
    evm::EvmReturnDataCopy,
    evm::EvmExtCodeHash,
    evm::EvmBlockHash,
    evm::EvmCoinBase,
    evm::EvmTimestamp,
    evm::EvmNumber,
    evm::EvmPrevRandao,
    evm::EvmGasLimit,
    evm::EvmChainId,
    evm::EvmSelfBalance,
    evm::EvmBaseFee,
    evm::EvmBlobHash,
    evm::EvmBlobBaseFee,
    evm::EvmMstore8,
    evm::EvmSload,
    evm::EvmSstore,
    evm::EvmMsize,
    evm::EvmGas,
    evm::EvmTload,
    evm::EvmMcopy,
    evm::EvmTstore,
    evm::EvmLog0,
    evm::EvmLog1,
    evm::EvmLog2,
    evm::EvmLog3,
    evm::EvmLog4,
    evm::EvmCreate,
    evm::EvmCall,
    evm::EvmCallCode,
    evm::EvmReturn,
    evm::EvmDelegateCall,
    evm::EvmCreate2,
    evm::EvmStaticCall,
    evm::EvmRevert,
    evm::EvmSelfDestruct,
    evm::EvmMalloc,
);
