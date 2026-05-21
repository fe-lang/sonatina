use sonatina_ir::{
    Function, InstSetExt, Module, Type, ValueId,
    inst::evm::machine_inst_set::EvmMachineInstKind,
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
        )
        .map_err(|err| format!("{err} at v{}", value.as_u32()))?;
    }

    let is = EvmMachine::new(function.ctx().triple).inst_set();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let inst_data = function.dfg.inst(inst);
            if !is.contains_inst(inst_data) {
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
                | EvmMachineInstKind::Sar(_) => {
                    verify_machine_arithmetic_inst(func_ref, function, inst)?
                }
                EvmMachineInstKind::Not(_)
                | EvmMachineInstKind::And(_)
                | EvmMachineInstKind::Or(_)
                | EvmMachineInstKind::Xor(_) => {
                    verify_machine_logic_inst(func_ref, function, inst)?
                }
                EvmMachineInstKind::Lt(_)
                | EvmMachineInstKind::Gt(_)
                | EvmMachineInstKind::Slt(_)
                | EvmMachineInstKind::Sgt(_)
                | EvmMachineInstKind::Eq(_)
                | EvmMachineInstKind::IsZero(_) => {
                    verify_machine_bool_inst(func_ref, function, inst)?
                }
                EvmMachineInstKind::Br(br) => {
                    verify_machine_branch_cond(func_ref, function, inst, *br.cond())?
                }
                _ => {}
            }
        }
    }

    Ok(())
}

fn verify_machine_arithmetic_inst(
    func_ref: FuncRef,
    function: &Function,
    inst: sonatina_ir::InstId,
) -> Result<(), String> {
    let result_ty = function
        .dfg
        .inst_results(inst)
        .first()
        .copied()
        .map(|result| function.dfg.value_ty(result));
    if result_ty != Some(Type::I256) {
        return Err(format!(
            "EVM machine word instruction inst{} in func {} must produce i256, found {:?}",
            inst.as_u32(),
            func_ref.as_u32(),
            result_ty
        ));
    }

    for operand in function.dfg.inst(inst).collect_values() {
        if !value_is_machine_word(function, operand) {
            return Err(format!(
                "EVM machine word instruction inst{} in func {} has non-word operand v{}.{:?}",
                inst.as_u32(),
                func_ref.as_u32(),
                operand.as_u32(),
                function.dfg.value_ty(operand)
            ));
        }
    }
    Ok(())
}

fn verify_machine_logic_inst(
    func_ref: FuncRef,
    function: &Function,
    inst: sonatina_ir::InstId,
) -> Result<(), String> {
    verify_machine_arithmetic_inst(func_ref, function, inst)
}

fn verify_machine_bool_inst(
    func_ref: FuncRef,
    function: &Function,
    inst: sonatina_ir::InstId,
) -> Result<(), String> {
    let result_ty = function
        .dfg
        .inst_results(inst)
        .first()
        .copied()
        .map(|result| function.dfg.value_ty(result));
    if result_ty != Some(Type::I256) {
        return Err(format!(
            "EVM machine boolean instruction inst{} in func {} must produce i256, found {:?}",
            inst.as_u32(),
            func_ref.as_u32(),
            result_ty
        ));
    }

    for operand in function.dfg.inst(inst).collect_values() {
        if !value_is_machine_word(function, operand) {
            return Err(format!(
                "EVM machine boolean instruction inst{} in func {} has non-word operand v{}.{:?}",
                inst.as_u32(),
                func_ref.as_u32(),
                operand.as_u32(),
                function.dfg.value_ty(operand)
            ));
        }
    }
    Ok(())
}

fn verify_machine_branch_cond(
    func_ref: FuncRef,
    function: &Function,
    inst: sonatina_ir::InstId,
    cond: ValueId,
) -> Result<(), String> {
    let cond_ty = function.dfg.value_ty(cond);
    if value_is_machine_word(function, cond) {
        return Ok(());
    }
    Err(format!(
        "EVM machine branch inst{} in func {} condition must be i256, found v{}.{cond_ty:?}",
        inst.as_u32(),
        func_ref.as_u32(),
        cond.as_u32()
    ))
}

fn value_is_machine_word(function: &Function, value: ValueId) -> bool {
    function.dfg.value_ty(value) == Type::I256
}

fn verify_machine_type(
    func_ref: FuncRef,
    function: &Function,
    ty: Type,
    context: &str,
) -> Result<(), String> {
    if matches!(ty, Type::I256 | Type::Unit) {
        Ok(())
    } else {
        let name = function
            .ctx()
            .get_sig(func_ref)
            .map_or_else(|| format!("{func_ref:?}"), |sig| format!("%{}", sig.name()));
        Err(format!(
            "EVM machine {context} must be i256 or unit, found {ty:?} in {name}"
        ))
    }
}
