use std::any::TypeId;

use sonatina_ir::{
    Function, Inst, InstSetExt, Module, Type,
    inst::{
        arith, cmp, control_flow, data,
        evm::{self, machine_inst_set::EvmMachineInstKind},
        logic,
    },
    isa::{Isa, evm::EvmMachine},
    module::FuncRef,
};

pub(crate) fn verify_machine_module(module: &Module, funcs: &[FuncRef]) -> Result<(), String> {
    for &func in funcs {
        module
            .func_store
            .view(func, |function| verify_machine_function(func, function))?;
    }
    Ok(())
}

pub(crate) fn verify_machine_function(
    func_ref: FuncRef,
    function: &Function,
) -> Result<(), String> {
    if let Some(sig) = function.ctx().get_sig(func_ref) {
        for &ty in sig.args() {
            verify_machine_type(func_ref, function, ty, "function argument type")?;
        }
        for &ty in sig.ret_tys() {
            verify_machine_type(func_ref, function, ty, "function return type")?;
        }
    }

    for &arg in &function.arg_values {
        verify_machine_type(
            func_ref,
            function,
            function.dfg.value_ty(arg),
            "function argument value",
        )?;
    }
    for value in function.dfg.value_ids() {
        verify_machine_type(
            func_ref,
            function,
            function.dfg.value_ty(value),
            "value type",
        )?;
    }

    let is = EvmMachine::new(function.ctx().triple).inst_set();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let inst_data = function.dfg.inst(inst);
            if !inst_belongs_to_machine(inst_data) {
                return Err(format!(
                    "EVM machine IR contains unsupported instruction at inst{}: {}",
                    inst.as_u32(),
                    inst_data.as_text()
                ));
            }
            match is.resolve_inst(function.dfg.inst(inst)) {
                EvmMachineInstKind::Add(_)
                | EvmMachineInstKind::Mul(_)
                | EvmMachineInstKind::Sub(_)
                | EvmMachineInstKind::Shl(_)
                | EvmMachineInstKind::Shr(_)
                | EvmMachineInstKind::Sar(_)
                | EvmMachineInstKind::Not(_)
                | EvmMachineInstKind::And(_)
                | EvmMachineInstKind::Or(_)
                | EvmMachineInstKind::Xor(_)
                | EvmMachineInstKind::Lt(_)
                | EvmMachineInstKind::Gt(_)
                | EvmMachineInstKind::Slt(_)
                | EvmMachineInstKind::Sgt(_)
                | EvmMachineInstKind::Eq(_)
                | EvmMachineInstKind::IsZero(_)
                | EvmMachineInstKind::Jump(_)
                | EvmMachineInstKind::Br(_)
                | EvmMachineInstKind::Phi(_)
                | EvmMachineInstKind::BrTable(_)
                | EvmMachineInstKind::Call(_)
                | EvmMachineInstKind::Return(_)
                | EvmMachineInstKind::Unreachable(_)
                | EvmMachineInstKind::GetFunctionPtr(_)
                | EvmMachineInstKind::SymAddr(_)
                | EvmMachineInstKind::SymSize(_)
                | EvmMachineInstKind::EvmUdiv(_)
                | EvmMachineInstKind::EvmSdiv(_)
                | EvmMachineInstKind::EvmUmod(_)
                | EvmMachineInstKind::EvmSmod(_)
                | EvmMachineInstKind::EvmAddMod(_)
                | EvmMachineInstKind::EvmMulMod(_)
                | EvmMachineInstKind::EvmExp(_)
                | EvmMachineInstKind::EvmSignExtend(_)
                | EvmMachineInstKind::EvmByte(_)
                | EvmMachineInstKind::EvmClz(_)
                | EvmMachineInstKind::EvmUaddsat(_)
                | EvmMachineInstKind::EvmSaddsat(_)
                | EvmMachineInstKind::EvmUsubsat(_)
                | EvmMachineInstKind::EvmSsubsat(_)
                | EvmMachineInstKind::EvmUmulsat(_)
                | EvmMachineInstKind::EvmSmulsat(_)
                | EvmMachineInstKind::EvmKeccak256(_)
                | EvmMachineInstKind::EvmAddress(_)
                | EvmMachineInstKind::EvmBalance(_)
                | EvmMachineInstKind::EvmOrigin(_)
                | EvmMachineInstKind::EvmCaller(_)
                | EvmMachineInstKind::EvmCallValue(_)
                | EvmMachineInstKind::EvmCalldataLoad(_)
                | EvmMachineInstKind::EvmCalldataCopy(_)
                | EvmMachineInstKind::EvmCalldataSize(_)
                | EvmMachineInstKind::EvmCodeSize(_)
                | EvmMachineInstKind::EvmCodeCopy(_)
                | EvmMachineInstKind::EvmGasPrice(_)
                | EvmMachineInstKind::EvmExtCodeSize(_)
                | EvmMachineInstKind::EvmExtCodeCopy(_)
                | EvmMachineInstKind::EvmReturnDataSize(_)
                | EvmMachineInstKind::EvmReturnDataCopy(_)
                | EvmMachineInstKind::EvmExtCodeHash(_)
                | EvmMachineInstKind::EvmBlockHash(_)
                | EvmMachineInstKind::EvmCoinBase(_)
                | EvmMachineInstKind::EvmTimestamp(_)
                | EvmMachineInstKind::EvmNumber(_)
                | EvmMachineInstKind::EvmPrevRandao(_)
                | EvmMachineInstKind::EvmGasLimit(_)
                | EvmMachineInstKind::EvmChainId(_)
                | EvmMachineInstKind::EvmSelfBalance(_)
                | EvmMachineInstKind::EvmBaseFee(_)
                | EvmMachineInstKind::EvmBlobHash(_)
                | EvmMachineInstKind::EvmBlobBaseFee(_)
                | EvmMachineInstKind::EvmMload(_)
                | EvmMachineInstKind::EvmMstore(_)
                | EvmMachineInstKind::EvmMstore8(_)
                | EvmMachineInstKind::EvmSload(_)
                | EvmMachineInstKind::EvmSstore(_)
                | EvmMachineInstKind::EvmMsize(_)
                | EvmMachineInstKind::EvmGas(_)
                | EvmMachineInstKind::EvmTload(_)
                | EvmMachineInstKind::EvmTstore(_)
                | EvmMachineInstKind::EvmMcopy(_)
                | EvmMachineInstKind::EvmLog0(_)
                | EvmMachineInstKind::EvmLog1(_)
                | EvmMachineInstKind::EvmLog2(_)
                | EvmMachineInstKind::EvmLog3(_)
                | EvmMachineInstKind::EvmLog4(_)
                | EvmMachineInstKind::EvmCreate(_)
                | EvmMachineInstKind::EvmCall(_)
                | EvmMachineInstKind::EvmCallCode(_)
                | EvmMachineInstKind::EvmReturn(_)
                | EvmMachineInstKind::EvmDelegateCall(_)
                | EvmMachineInstKind::EvmCreate2(_)
                | EvmMachineInstKind::EvmStaticCall(_)
                | EvmMachineInstKind::EvmRevert(_)
                | EvmMachineInstKind::EvmSelfDestruct(_)
                | EvmMachineInstKind::EvmStop(_)
                | EvmMachineInstKind::EvmInvalid(_) => {}
            }
        }
    }

    Ok(())
}

fn verify_machine_type(
    func_ref: FuncRef,
    function: &Function,
    ty: Type,
    context: &str,
) -> Result<(), String> {
    if matches!(ty, Type::I1 | Type::I256 | Type::Unit) {
        Ok(())
    } else {
        let name = function
            .ctx()
            .get_sig(func_ref)
            .map_or_else(|| format!("{func_ref:?}"), |sig| format!("%{}", sig.name()));
        Err(format!(
            "EVM machine {context} must be i1, i256, or unit, found {ty:?} in {name}"
        ))
    }
}

fn inst_belongs_to_machine(inst: &dyn Inst) -> bool {
    let tid = inst.type_id();
    machine_inst_type_id(tid)
}

macro_rules! machine_inst_type_ids {
    ($tid:expr, $($ty:path),+ $(,)?) => {
        false $(|| $tid == TypeId::of::<$ty>())+
    };
}

fn machine_inst_type_id(tid: TypeId) -> bool {
    machine_inst_type_ids!(
        tid,
        arith::Add,
        arith::Mul,
        arith::Sub,
        arith::Shl,
        arith::Shr,
        arith::Sar,
        logic::Not,
        logic::And,
        logic::Or,
        logic::Xor,
        cmp::Lt,
        cmp::Gt,
        cmp::Slt,
        cmp::Sgt,
        cmp::Eq,
        cmp::IsZero,
        control_flow::Jump,
        control_flow::Br,
        control_flow::Phi,
        control_flow::BrTable,
        control_flow::Call,
        control_flow::Return,
        control_flow::Unreachable,
        data::GetFunctionPtr,
        data::SymAddr,
        data::SymSize,
        evm::EvmUdiv,
        evm::EvmSdiv,
        evm::EvmUmod,
        evm::EvmSmod,
        evm::EvmAddMod,
        evm::EvmMulMod,
        evm::EvmExp,
        evm::EvmSignExtend,
        evm::EvmByte,
        evm::EvmClz,
        evm::EvmUaddsat,
        evm::EvmSaddsat,
        evm::EvmUsubsat,
        evm::EvmSsubsat,
        evm::EvmUmulsat,
        evm::EvmSmulsat,
        evm::EvmKeccak256,
        evm::EvmAddress,
        evm::EvmBalance,
        evm::EvmOrigin,
        evm::EvmCaller,
        evm::EvmCallValue,
        evm::EvmCalldataLoad,
        evm::EvmCalldataCopy,
        evm::EvmCalldataSize,
        evm::EvmCodeSize,
        evm::EvmCodeCopy,
        evm::EvmGasPrice,
        evm::EvmExtCodeSize,
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
        evm::EvmMload,
        evm::EvmMstore,
        evm::EvmMstore8,
        evm::EvmSload,
        evm::EvmSstore,
        evm::EvmMsize,
        evm::EvmGas,
        evm::EvmTload,
        evm::EvmTstore,
        evm::EvmMcopy,
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
        evm::EvmStop,
        evm::EvmInvalid,
    )
}
