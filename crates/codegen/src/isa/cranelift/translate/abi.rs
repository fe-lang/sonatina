use cranelift_codegen::{
    ir::{self as clif, ArgumentPurpose},
    isa::CallConv,
};
use cranelift_module::Module as ClifModule;
use sonatina_ir::{Linkage, Signature, Type, module::ModuleCtx, types::CompoundType};
use sonatina_triple::TargetTriple;

/// Whether translated values of `ty` are addresses of their storage.
/// i256 values are four limbs instead, though passed by reference.
pub(super) fn uses_indirect_value_representation(ctx: &ModuleCtx, ty: Type) -> bool {
    matches!(
        ty.resolve_compound(ctx),
        Some(CompoundType::Array { .. } | CompoundType::Struct(_) | CompoundType::Enum(_))
    )
}

/// Whether values of `ty` are passed and returned through memory.
fn passes_by_reference(ctx: &ModuleCtx, ty: Type) -> bool {
    ty == Type::I256 || uses_indirect_value_representation(ctx, ty)
}

/// Private functions, which only this module calls, pass and return i256
/// values as four i64 limbs, and return up to eight words in registers
/// through Cranelift's tail calling convention.
pub(super) fn uses_register_abi(sig: &Signature) -> bool {
    sig.linkage() == Linkage::Private
}

pub(super) fn returns_indirect(ctx: &ModuleCtx, sig: &Signature) -> bool {
    sig.ret_tys().len() == 1
        && indirect_return_storage_type(ctx, sig.ret_tys()[0], uses_register_abi(sig)).is_some()
}

/// The storage a return value of `ty` takes in the caller, when it returns
/// through memory. `registers` is whether its function uses the register ABI.
pub(super) fn indirect_return_storage_type(
    ctx: &ModuleCtx,
    ty: Type,
    registers: bool,
) -> Option<Type> {
    if registers && ty == Type::I256 {
        None
    } else if passes_by_reference(ctx, ty) {
        Some(ty)
    } else if let Some(CompoundType::ConstRef(inner)) = ty.resolve_compound(ctx) {
        Some(inner)
    } else {
        None
    }
}

pub(super) fn validate_cranelift_signature(ctx: &ModuleCtx, sig: &Signature) -> Result<(), String> {
    if sig
        .args()
        .iter()
        .chain(sig.ret_tys())
        .any(|ty| *ty == Type::Unit)
    {
        return Err(format!(
            "Cranelift backend does not support explicit unit values in function signatures: {}",
            sig.name()
        ));
    }
    if sig.ret_tys().len() > 1
        && sig
            .ret_tys()
            .iter()
            .any(|ty| indirect_return_storage_type(ctx, *ty, uses_register_abi(sig)).is_some())
    {
        return Err(format!(
            "Cranelift backend does not support multi-return signatures containing indirect return types: {}",
            sig.name()
        ));
    }
    Ok(())
}

pub(super) fn sonatina_sig_to_clif(
    ctx: &ModuleCtx,
    sig: &Signature,
    clif_module: &impl ClifModule,
) -> clif::Signature {
    let mut clif_sig = clif_module.make_signature();
    let pointer_type = clif_module.target_config().pointer_type();
    let registers = uses_register_abi(sig);
    if registers {
        clif_sig.call_conv = CallConv::Tail;
    }

    // Values represented as pointers to owned storage return through a
    // caller-allocated buffer so the result outlives the callee frame.
    if returns_indirect(ctx, sig) {
        clif_sig.params.push(clif::AbiParam::special(
            pointer_type,
            ArgumentPurpose::StructReturn,
        ));
    }

    for &arg_ty in sig.args() {
        push_abi_params(ctx, &mut clif_sig.params, arg_ty, registers, pointer_type);
    }

    if !returns_indirect(ctx, sig) {
        for &ret_ty in sig.ret_tys() {
            push_abi_params(ctx, &mut clif_sig.returns, ret_ty, registers, pointer_type);
        }
    }
    clif_sig
}

fn push_abi_params(
    ctx: &ModuleCtx,
    params: &mut Vec<clif::AbiParam>,
    ty: Type,
    registers: bool,
    pointer_type: clif::Type,
) {
    if registers && ty == Type::I256 {
        params.extend([clif::AbiParam::new(clif::types::I64); 4]);
    } else if let Some(clif_ty) = sonatina_type_to_clif(ty, pointer_type) {
        params.push(scalar_abi_param(ctx, clif_ty));
    }
}

fn scalar_abi_param(ctx: &ModuleCtx, ty: clif::Type) -> clif::AbiParam {
    let param = clif::AbiParam::new(ty);
    if ctx.triple == TargetTriple::SP1 && ty == clif::types::I32 {
        // The RV64 C ABI sign-extends all 32-bit arguments and results,
        // including unsigned values. Native host behavior is unchanged.
        param.sext()
    } else {
        param
    }
}

pub(super) fn sonatina_type_to_clif(ty: Type, pointer_type: clif::Type) -> Option<clif::Type> {
    match ty {
        Type::Unit => None,
        Type::I1 | Type::I8 => Some(clif::types::I8),
        Type::I16 => Some(clif::types::I16),
        Type::I32 => Some(clif::types::I32),
        Type::I64 => Some(clif::types::I64),
        Type::I128 => Some(clif::types::I128),
        // I256 and compound values are passed as native pointers to
        // caller- or stack-owned storage.
        Type::I256 | Type::Compound(_) => Some(pointer_type),
        _ => None,
    }
}

pub(super) fn sonatina_type_to_clif_or_err(
    ty: Type,
    pointer_type: clif::Type,
) -> Result<clif::Type, String> {
    sonatina_type_to_clif(ty, pointer_type)
        .ok_or_else(|| format!("unsupported type for cranelift: {ty:?}"))
}

pub(super) fn sonatina_scalar_type_to_clif_or_err(ty: Type) -> Result<clif::Type, String> {
    match ty {
        Type::I1 | Type::I8 => Ok(clif::types::I8),
        Type::I16 => Ok(clif::types::I16),
        Type::I32 => Ok(clif::types::I32),
        Type::I64 => Ok(clif::types::I64),
        Type::I128 => Ok(clif::types::I128),
        _ => Err(format!("unsupported scalar type for cranelift: {ty:?}")),
    }
}
