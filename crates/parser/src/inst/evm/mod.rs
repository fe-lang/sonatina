use ir::inst::evm::*;

super::impl_inst_build! {EvmStop, has_evm_stop, ()}
super::impl_inst_build! {EvmAddMod, has_evm_add_mod, (lhs: ValueId, rhs: ValueId, modulus: ValueId)}
super::impl_inst_build! {EvmMulMod, has_evm_mul_mod, (lhs: ValueId, rhs: ValueId, modulus: ValueId)}
super::impl_inst_build! {EvmExp, has_evm_exp, (base: ValueId, exponent: ValueId)}
super::impl_inst_build! {EvmByte, has_evm_byte, (pos: ValueId, value: ValueId)}
super::impl_inst_build! {EvmKeccak256, has_evm_keccak256, (addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmAddress, has_evm_address, ()}
super::impl_inst_build! {EvmBalance, has_evm_balance, (contract_addr: ValueId)}
super::impl_inst_build! {EvmOrigin, has_evm_origin, ()}
super::impl_inst_build! {EvmCaller, has_evm_caller, ()}
super::impl_inst_build! {EvmCallValue, has_evm_call_value, ()}
super::impl_inst_build! {EvmCallDataLoad, has_evm_call_data_load, (data_offset: ValueId)}
super::impl_inst_build! {EvmCallDataCopy, has_evm_call_data_copy, (dst_addr: ValueId, data_offset: ValueId, len: ValueId)}
super::impl_inst_build! {EvmCodeSize, has_evm_code_size, ()}
super::impl_inst_build! {EvmCodeCopy, has_evm_code_copy, (dst_addr: ValueId, code_offset: ValueId, len: ValueId)}
super::impl_inst_build! {EvmGasPrice, has_evm_gas_price, ()}
super::impl_inst_build! {EvmExtCodeSize, has_evm_ext_code_size, (ext_addr: ValueId)}
super::impl_inst_build! {EvmExtCodeCopy, has_evm_ext_code_copy, (ext_addr: ValueId, dst_addr: ValueId, code_offset: ValueId, len: ValueId)}
super::impl_inst_build! {EvmReturnDataSize, has_evm_return_data_size, ()}
super::impl_inst_build! {EvmReturnDataCopy, has_evm_return_data_copy, (dst_addr: ValueId, data_offset: ValueId, len: ValueId)}
super::impl_inst_build! {EvmExtCodeHash, has_evm_ext_code_hash, (ext_addr: ValueId)}
super::impl_inst_build! {EvmBlockHash, has_evm_block_hash, (block_num: ValueId)}
super::impl_inst_build! {EvmCoinBase, has_evm_coin_base, (block_num: ValueId)}
super::impl_inst_build! {EvmTimestamp, has_evm_timestamp, ()}
super::impl_inst_build! {EvmNumber, has_evm_number, ()}
super::impl_inst_build! {EvmPrevRandao, has_evm_prev_randao, ()}
super::impl_inst_build! {EvmGasLimit, has_evm_gas_limit, ()}
super::impl_inst_build! {EvmChainId, has_evm_chain_id, ()}
super::impl_inst_build! {EvmSelfBalance, has_evm_self_balance, ()}
super::impl_inst_build! {EvmBaseFee, has_evm_base_fee, ()}
super::impl_inst_build! {EvmBlobHash, has_evm_blob_hash, (idx: ValueId)}
super::impl_inst_build! {EvmBlobBaseFee, has_evm_blob_base_fee, ()}
super::impl_inst_build! {EvmMstore8, has_evm_mstore8, (addr: ValueId, val: ValueId)}
super::impl_inst_build! {EvmSload, has_evm_sload, (key: ValueId)}
super::impl_inst_build! {EvmSstore, has_evm_sstore, (key: ValueId, val: ValueId)}
super::impl_inst_build! {EvmMsize, has_evm_msize, ()}
super::impl_inst_build! {EvmGas, has_evm_gas, ()}
super::impl_inst_build! {EvmTload, has_evm_tload, (key: ValueId)}
super::impl_inst_build! {EvmTstore, has_evm_tstore, (key: ValueId, val: ValueId)}
super::impl_inst_build! {EvmLog0, has_evm_log0, (addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmLog1, has_evm_log1, (addr: ValueId, len: ValueId, topic0: ValueId)}
super::impl_inst_build! {EvmLog2, has_evm_log2, (addr: ValueId, len: ValueId, topic0: ValueId, topic1: ValueId)}
super::impl_inst_build! {EvmLog3, has_evm_log3, (addr: ValueId, len: ValueId, topic0: ValueId, topic1: ValueId, topic2: ValueId)}
super::impl_inst_build! {EvmLog4, has_evm_log4, (addr: ValueId, len: ValueId, topic0: ValueId, topic1: ValueId, topic2: ValueId, topic3: ValueId)}
super::impl_inst_build! {EvmCreate, has_evm_create, (val: ValueId, addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmCall, has_evm_call, (gas: ValueId, addr: ValueId, val: ValueId, arg_addr: ValueId, arg_len: ValueId, ret_addr: ValueId, ret_offset: ValueId)}
super::impl_inst_build! {EvmReturn, has_evm_return, (addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmDelegateCall, has_evm_delegate_call, (gas: ValueId, ext_addr: ValueId, arg_addr: ValueId, arg_len: ValueId, ret_addr: ValueId, ret_len: ValueId)}
super::impl_inst_build! {EvmCreate2, has_evm_create2, (val: ValueId, addr: ValueId, len: ValueId, salt: ValueId)}
super::impl_inst_build! {EvmStaticCall, has_evm_static_call, (gas: ValueId, ext_addr: ValueId, arg_addr: ValueId, arg_len: ValueId, ret_addr: ValueId, ret_len: ValueId)}
super::impl_inst_build! {EvmRevert, has_evm_revert, (addr: ValueId, len: ValueId)}
super::impl_inst_build! {EvmSelfDestruct, has_evm_self_destruct, (addr: ValueId)}
