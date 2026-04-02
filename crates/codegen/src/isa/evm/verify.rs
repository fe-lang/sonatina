use rustc_hash::FxHashSet;
use sonatina_ir::{
    Function, InstSetExt, Module, Type,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
    types::{CompoundType, CompoundTypeRef},
};

pub(crate) fn collect_unsupported_evm_multi_return(
    module: &Module,
    funcs: &[FuncRef],
    entry: Option<FuncRef>,
) -> Vec<(FuncRef, String)> {
    let mut errors = Vec::new();

    for &func in funcs {
        let Some(sig) = module.ctx.get_sig(func) else {
            continue;
        };
        let func_name = format!("%{}", sig.name());
        let ret_count = sig.ret_tys().len();
        let mut push_error = |message| errors.push((func, message));

        if ret_count > 16 {
            push_error(format!(
                "EVM backend supports at most 16 internal return values, but function {func_name} has {ret_count}"
            ));
        }
        if entry == Some(func) && ret_count > 1 {
            push_error(format!(
                "EVM backend does not support section entry {func_name} with {ret_count} return values"
            ));
        }
        if ret_count > 1 && !sig.linkage().has_definition() {
            push_error(format!(
                "EVM backend does not support declaration-only function {func_name} with {ret_count} return values"
            ));
        }

        module.func_store.view(func, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if let Some(call) = function.dfg.call_info(inst) {
                        let call_results = function.dfg.inst_results(inst);
                        let callee = call.callee();
                        let callee_name = module
                            .ctx
                            .get_sig(callee)
                            .map(|sig| format!("%{}", sig.name()))
                            .unwrap_or_else(|| format!("{callee:?}"));

                        if call_results.len() > 16 {
                            push_error(format!(
                                "EVM backend supports at most 16 call results, but inst{} has {} results to {callee_name}",
                                inst.as_u32(),
                                call_results.len()
                            ));
                        }

                        if let Some(callee_sig) = module.ctx.get_sig(callee) {
                            let callee_ret_count = callee_sig.ret_tys().len();
                            if callee_ret_count > 16 {
                                push_error(format!(
                                    "EVM backend supports at most 16 internal return values, but callee {callee_name} has {callee_ret_count}",
                                ));
                            }
                            if callee_ret_count > 1 && !callee_sig.linkage().has_definition() {
                                push_error(format!(
                                    "EVM backend does not support external or declaration-only multi-return calls to {callee_name}"
                                ));
                            }
                            if call_results.len() != callee_ret_count {
                                push_error(format!(
                                    "call inst{} result count {} does not match callee {callee_name} return count {callee_ret_count}",
                                    inst.as_u32(),
                                    call_results.len(),
                                ));
                            }
                        }
                    }

                    if let Some(return_args) = function.dfg.return_args(inst) {
                        if return_args.len() > 16 {
                            push_error(format!(
                                "EVM backend supports at most 16 return values, but return inst{} has {}",
                                inst.as_u32(),
                                return_args.len()
                            ));
                        }
                        if return_args.len() != sig.ret_tys().len() {
                            push_error(format!(
                                "return inst{} value count {} does not match function signature return count {}",
                                inst.as_u32(),
                                return_args.len(),
                                sig.ret_tys().len()
                            ));
                        }
                    }
                }
            }
        });
    }

    errors
}

pub(crate) fn validate_supported_lowering_ir(
    func_ref: FuncRef,
    func: &Function,
) -> Result<(), String> {
    if let Some(sig) = func.ctx().get_sig(func_ref) {
        for &arg in sig.args() {
            validate_type_is_legalized_evm(func.ctx(), arg, "function argument type")?;
        }
        for &ret in sig.ret_tys() {
            validate_type_is_legalized_evm(func.ctx(), ret, "function return type")?;
        }
    }

    for &arg in &func.arg_values {
        validate_type_is_legalized_evm(
            func.ctx(),
            func.dfg.value_ty(arg),
            "function argument value",
        )?;
    }
    for value in func.dfg.value_ids() {
        validate_type_is_legalized_evm(func.ctx(), func.dfg.value_ty(value), "value type")?;
    }

    let evm_inst_set = Evm::new(func.ctx().triple).inst_set();
    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            match evm_inst_set.resolve_inst(func.dfg.inst(inst)) {
                EvmInstKind::Uaddo(_)
                | EvmInstKind::Uaddsat(_)
                | EvmInstKind::Saddo(_)
                | EvmInstKind::Saddsat(_)
                | EvmInstKind::Usubo(_)
                | EvmInstKind::Usubsat(_)
                | EvmInstKind::Ssubo(_)
                | EvmInstKind::Ssubsat(_)
                | EvmInstKind::Umulo(_)
                | EvmInstKind::Umulsat(_)
                | EvmInstKind::Smulo(_)
                | EvmInstKind::Smulsat(_)
                | EvmInstKind::Snego(_)
                | EvmInstKind::EvmUdivo(_)
                | EvmInstKind::EvmSdivo(_)
                | EvmInstKind::EvmUmodo(_)
                | EvmInstKind::EvmSmodo(_) => {
                    return Err(format!(
                        "multi-result arithmetic must be legalized before EVM lowering: {}",
                        func.dfg.inst(inst).as_text()
                    ));
                }
                EvmInstKind::Sdiv(_)
                | EvmInstKind::Udiv(_)
                | EvmInstKind::Umod(_)
                | EvmInstKind::Smod(_) => {
                    return Err(format!(
                        "generic integer div/mod must be legalized to EVM-specific ops before lowering: {}",
                        func.dfg.inst(inst).as_text()
                    ));
                }
                EvmInstKind::Sext(_) | EvmInstKind::Zext(_) | EvmInstKind::Trunc(_) => {
                    return Err(format!(
                        "integer casts must be eliminated before EVM lowering: {}",
                        func.dfg.inst(inst).as_text()
                    ));
                }
                EvmInstKind::Not(not) if func.dfg.value_ty(*not.arg()) == Type::I1 => {
                    return Err("not on i1 must be legalized before EVM lowering".to_string());
                }
                EvmInstKind::Bitcast(bitcast) => {
                    validate_type_is_legalized_evm(func.ctx(), *bitcast.ty(), "bitcast type")?;
                }
                EvmInstKind::IntToPtr(int_to_ptr) => {
                    validate_type_is_legalized_evm(func.ctx(), *int_to_ptr.ty(), "inttoptr type")?;
                }
                EvmInstKind::PtrToInt(ptr_to_int) => {
                    validate_type_is_legalized_evm(func.ctx(), *ptr_to_int.ty(), "ptrtoint type")?;
                }
                EvmInstKind::Mload(mload) => {
                    validate_type_is_legalized_evm(func.ctx(), *mload.ty(), "mload type")?;
                }
                EvmInstKind::Mstore(mstore) => {
                    validate_type_is_legalized_evm(func.ctx(), *mstore.ty(), "mstore type")?;
                }
                EvmInstKind::Alloca(alloca) => {
                    validate_type_is_legalized_evm(func.ctx(), *alloca.ty(), "alloca type")?;
                }
                _ => {}
            }

            let results = func.dfg.inst_results(inst);
            if results.len() <= 1 {
                continue;
            }

            if !func.dfg.is_call(inst) {
                return Err(format!(
                    "multi-result instruction `{}` must be legalized before EVM lowering",
                    func.dfg.inst(inst).as_text()
                ));
            }
        }
    }

    Ok(())
}

fn type_is_legalized_evm(ctx: &ModuleCtx, ty: Type, seen: &mut FxHashSet<CompoundTypeRef>) -> bool {
    match ty {
        Type::I1 | Type::I256 | Type::Unit => true,
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 => false,
        Type::EnumTag(_) => false,
        Type::Compound(compound) => {
            if !seen.insert(compound) {
                return true;
            }

            match ctx.with_ty_store(|store| store.resolve_compound(compound).clone()) {
                CompoundType::Array { elem, .. } | CompoundType::Ptr(elem) => {
                    type_is_legalized_evm(ctx, elem, seen)
                }
                CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => false,
                CompoundType::Func { args, ret_tys } => args
                    .iter()
                    .chain(ret_tys.iter())
                    .all(|&ty| type_is_legalized_evm(ctx, ty, seen)),
                CompoundType::Struct(data) => data
                    .fields
                    .iter()
                    .all(|&field| type_is_legalized_evm(ctx, field, seen)),
                CompoundType::Enum(_) => false,
            }
        }
    }
}

fn validate_type_is_legalized_evm(ctx: &ModuleCtx, ty: Type, context: &str) -> Result<(), String> {
    let mut seen = FxHashSet::default();
    if type_is_legalized_evm(ctx, ty, &mut seen) {
        Ok(())
    } else {
        Err(format!(
            "{context} must be legalized to the EVM scalar subset, found {ty:?}"
        ))
    }
}
