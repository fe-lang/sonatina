use std::iter;

use cranelift_codegen::{
    ir::{self as clif, ArgumentPurpose, InstBuilder},
    isa::CallConv,
};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{FuncId, Module as ClifModule};
use sonatina_ir::{Linkage, Signature, Type, module::ModuleCtx};
use sonatina_triple::TargetTriple;

use super::{Parts, is_aggregate, register_parts};

/// The parts in which a function of `linkage` passes and returns `ty`
/// values: private functions pass aggregates held in registers as their
/// parts, while public and external ones keep the platform's references.
pub(super) fn passed_parts(ctx: &ModuleCtx, linkage: Linkage, ty: Type) -> Option<Parts> {
    linkage
        .is_private()
        .then(|| register_parts(ctx, ty))
        .flatten()
}

/// Whether a function of `linkage` passes and returns `ty` values through
/// memory. A `constref` is the address of its constant, which outlives every
/// frame.
pub(super) fn passes_by_reference(ctx: &ModuleCtx, linkage: Linkage, ty: Type) -> bool {
    ty == Type::I256 || is_aggregate(ctx, ty) && passed_parts(ctx, linkage, ty).is_none()
}

pub(super) fn returns_indirect(ctx: &ModuleCtx, sig: &Signature) -> bool {
    matches!(sig.ret_tys(), [ty] if passes_by_reference(ctx, sig.linkage(), *ty))
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
            .any(|ty| passes_by_reference(ctx, sig.linkage(), *ty))
    {
        return Err(format!(
            "Cranelift backend does not support multi-return signatures containing indirect return types: {}",
            sig.name()
        ));
    }
    if sig.is_variadic() && ctx.triple == TargetTriple::SP1 {
        return Err(format!(
            "SP1 does not support variadic functions: {}",
            sig.name()
        ));
    }
    Ok(())
}

/// The function a call to the variadic `sig`, `func_id` in the object,
/// calls: its symbol, with a signature of the call's own that passes the
/// fixed arguments as `sig` does and the call's extra arguments after them.
/// `args` are the call's arguments, which this arranges for that signature.
///
/// Apple's AArch64 convention passes every extra argument on the stack, in
/// an eight-byte slot of its own. The verifier gives each fixed argument one
/// of x0-x7, so zeros fill the rest of them, and each extra argument widens
/// to `i64`. Other conventions pass extra arguments as they do fixed ones.
/// On x86-64 System V, `%al` should bound the vector registers the call
/// uses; it stays unset, and a callee that reads it at most saves vector
/// registers it need not.
pub(super) fn variadic_callee(
    ctx: &ModuleCtx,
    sig: &Signature,
    func_id: FuncId,
    args: &mut Vec<clif::Value>,
    clif_module: &impl ClifModule,
    builder: &mut FunctionBuilder,
) -> clif::FuncRef {
    let mut clif_sig = sonatina_sig_to_clif(ctx, sig, clif_module);
    let fixed = clif_sig.params.len();
    let mut extras = args.split_off(fixed);
    if clif_sig.call_conv == CallConv::AppleAarch64 {
        let padding = 8usize.saturating_sub(sig.args().len());
        args.extend(iter::repeat_with(|| builder.ins().iconst(clif::types::I64, 0)).take(padding));
        for extra in &mut extras {
            if builder.func.dfg.value_type(*extra) != clif::types::I64 {
                *extra = builder.ins().uextend(clif::types::I64, *extra);
            }
        }
    }
    args.extend(extras);
    clif_sig.params.extend(
        args[fixed..]
            .iter()
            .map(|&arg| clif::AbiParam::new(builder.func.dfg.value_type(arg))),
    );
    let signature = builder.import_signature(clif_sig);
    let name = builder
        .func
        .declare_imported_user_function(clif::UserExternalName {
            namespace: 0,
            index: func_id.as_u32(),
        });
    builder.import_function(clif::ExtFuncData {
        name: clif::ExternalName::user(name),
        signature,
        colocated: false,
        patchable: false,
    })
}

pub(super) fn sonatina_sig_to_clif(
    ctx: &ModuleCtx,
    sig: &Signature,
    clif_module: &impl ClifModule,
) -> clif::Signature {
    let mut clif_sig = clif_module.make_signature();
    let pointer_type = clif_module.target_config().pointer_type();

    // Values represented as pointers to owned storage return through a
    // caller-allocated buffer so the result outlives the callee frame.
    if returns_indirect(ctx, sig) {
        clif_sig.params.push(clif::AbiParam::special(
            pointer_type,
            ArgumentPurpose::StructReturn,
        ));
    }

    let abi_params = |ty: Type| -> Vec<clif::AbiParam> {
        match passed_parts(ctx, sig.linkage(), ty) {
            Some(parts) => parts
                .iter()
                .filter_map(|part| sonatina_type_to_clif(part.ty, pointer_type))
                .map(|clif_ty| scalar_abi_param(ctx, clif_ty))
                .collect(),
            None => sonatina_type_to_clif(ty, pointer_type)
                .map(|clif_ty| scalar_abi_param(ctx, clif_ty))
                .into_iter()
                .collect(),
        }
    };
    for &arg_ty in sig.args() {
        clif_sig.params.extend(abi_params(arg_ty));
    }

    if !returns_indirect(ctx, sig) {
        for &ret_ty in sig.ret_tys() {
            clif_sig.returns.extend(abi_params(ret_ty));
        }
    }
    clif_sig
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
