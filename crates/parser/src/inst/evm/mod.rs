use ir::inst::evm::*;

super::impl_inst_build! {EvmUdiv, (lhs: ValueId, rhs:ValueId)}
super::impl_inst_build! {EvmSdiv, (lhs: ValueId, rhs:ValueId)}
super::impl_inst_build! {EvmUmod, (lhs: ValueId, rhs:ValueId)}
super::impl_inst_build! {EvmSmod, (lhs: ValueId, rhs:ValueId)}
super::impl_inst_build! {EvmStop, ()}
super::impl_inst_build! {EvmInvalid, ()}
super::impl_inst_build! {EvmAddMod, (lhs: ValueId, rhs: ValueId, modulus: ValueId)}
super::impl_inst_build! {EvmMulMod, (lhs: ValueId, rhs: ValueId, modulus: ValueId)}
super::impl_inst_build! {EvmExp, (base: ValueId, exponent: ValueId)}
super::impl_inst_build! {EvmByte, (pos: ValueId, value: ValueId)}
super::impl_inst_build! {EvmKeccak256, (addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmAddress, ()}
super::impl_inst_build! {EvmBalance, (contract_addr: ValueId)}
super::impl_inst_build! {EvmOrigin, ()}
super::impl_inst_build! {EvmCaller, ()}
super::impl_inst_build! {EvmCallValue, ()}
super::impl_inst_build! {EvmCalldataLoad, (data_offset: ValueId)}
super::impl_inst_build! {EvmCalldataCopy, (dst_addr: ValueId, data_offset: ValueId, len: ValueId)}
super::impl_inst_build! {EvmCalldataSize, ()}
super::impl_inst_build! {EvmCodeSize, ()}
super::impl_inst_build! {EvmCodeCopy, (dst_addr: ValueId, code_offset: ValueId, len: ValueId)}
super::impl_inst_build! {EvmGasPrice, ()}
super::impl_inst_build! {EvmExtCodeSize, (ext_addr: ValueId)}
super::impl_inst_build! {EvmExtCodeCopy, (ext_addr: ValueId, dst_addr: ValueId, code_offset: ValueId, len: ValueId)}
super::impl_inst_build! {EvmReturnDataSize, ()}
super::impl_inst_build! {EvmReturnDataCopy, (dst_addr: ValueId, data_offset: ValueId, len: ValueId)}
super::impl_inst_build! {EvmExtCodeHash, (ext_addr: ValueId)}
super::impl_inst_build! {EvmBlockHash, (block_num: ValueId)}
super::impl_inst_build! {EvmCoinBase, ()}
super::impl_inst_build! {EvmTimestamp, ()}
super::impl_inst_build! {EvmNumber, ()}
super::impl_inst_build! {EvmPrevRandao, ()}
super::impl_inst_build! {EvmGasLimit, ()}
super::impl_inst_build! {EvmChainId, ()}
super::impl_inst_build! {EvmSelfBalance, ()}
super::impl_inst_build! {EvmBaseFee, ()}
super::impl_inst_build! {EvmBlobHash, (idx: ValueId)}
super::impl_inst_build! {EvmBlobBaseFee, ()}
super::impl_inst_build! {EvmMstore8, (addr: ValueId, val: ValueId)}
super::impl_inst_build! {EvmSload, (key: ValueId)}
super::impl_inst_build! {EvmSstore, (key: ValueId, val: ValueId)}
super::impl_inst_build! {EvmMsize, ()}
super::impl_inst_build! {EvmGas, ()}
super::impl_inst_build! {EvmTload, (key: ValueId)}
super::impl_inst_build! {EvmTstore, (key: ValueId, val: ValueId)}
super::impl_inst_build! {EvmMcopy, (dest: ValueId, addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmLog0, (addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmLog1, (addr: ValueId, len: ValueId, topic0: ValueId)}
super::impl_inst_build! {EvmLog2, (addr: ValueId, len: ValueId, topic0: ValueId, topic1: ValueId)}
super::impl_inst_build! {EvmLog3, (addr: ValueId, len: ValueId, topic0: ValueId, topic1: ValueId, topic2: ValueId)}
super::impl_inst_build! {EvmLog4, (addr: ValueId, len: ValueId, topic0: ValueId, topic1: ValueId, topic2: ValueId, topic3: ValueId)}
super::impl_inst_build! {EvmCreate, (val: ValueId, addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmCall, (gas: ValueId, addr: ValueId, val: ValueId, arg_addr: ValueId, arg_len: ValueId, ret_addr: ValueId, ret_offset: ValueId)}
super::impl_inst_build! {EvmCallCode, (gas: ValueId, addr: ValueId, val: ValueId, arg_addr: ValueId, arg_len: ValueId, ret_addr: ValueId, ret_offset: ValueId)}
super::impl_inst_build! {EvmReturn, (addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmDelegateCall, (gas: ValueId, ext_addr: ValueId, arg_addr: ValueId, arg_len: ValueId, ret_addr: ValueId, ret_len: ValueId)}
super::impl_inst_build! {EvmCreate2, (val: ValueId, addr: ValueId, len: ValueId, salt: ValueId)}
super::impl_inst_build! {EvmStaticCall, (gas: ValueId, ext_addr: ValueId, arg_addr: ValueId, arg_len: ValueId, ret_addr: ValueId, ret_len: ValueId)}
super::impl_inst_build! {EvmRevert, (addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmSelfDestruct, (addr: ValueId)}
super::impl_inst_build! {EvmMalloc, (size: ValueId)}
super::impl_inst_build! {EvmContractSize, (contract: FuncRef)}
