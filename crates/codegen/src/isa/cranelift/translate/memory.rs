use std::collections::HashMap;

use cranelift_codegen::{
    ir::{self as clif, InstBuilder, MemFlagsData, StackSlotData, StackSlotKind},
    isa::TargetFrontendConfig,
};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::{Function, Type, Value, ValueId, module::ModuleCtx, types::CompoundType};

use super::{
    create_stack_slot_for_type, load_i256_limb, resize_int_value, resolve_value, signed_scalar,
    sonatina_type_to_clif_or_err, uses_indirect_value_representation,
};

/// Copies and fills of at most this many bytes use inline loads and stores.
/// Larger ones call `memcpy` or `memset`, so their code size is constant.
const INLINE_MEMORY_BYTES: u32 = 128;

/// Copies `size` bytes between distinct, non-overlapping storage.
pub(super) fn copy_bytes(
    src: clif::Value,
    dst: clif::Value,
    size: u32,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) {
    if size > INLINE_MEMORY_BYTES {
        let size = builder.ins().iconst(config.pointer_type(), i64::from(size));
        builder.call_memcpy(config, dst, src, size);
        return;
    }
    for (offset, ty) in storage_chunks(size) {
        let value = builder.ins().load(ty, MemFlagsData::new(), src, offset);
        builder.ins().store(MemFlagsData::new(), value, dst, offset);
    }
}

pub(super) fn zero_bytes(
    dst: clif::Value,
    size: u32,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) {
    if size > INLINE_MEMORY_BYTES {
        let zero = builder.ins().iconst(clif::types::I8, 0);
        let size = builder.ins().iconst(config.pointer_type(), i64::from(size));
        builder.call_memset(config, dst, zero, size);
        return;
    }
    for (offset, ty) in storage_chunks(size) {
        let zero = builder.ins().iconst(ty, 0);
        builder.ins().store(MemFlagsData::new(), zero, dst, offset);
    }
}

pub(super) fn is_undef(function: &Function, value: ValueId) -> bool {
    matches!(function.dfg.value(value), Value::Undef { .. })
}

/// Zeroes the bytes of `dst..dst + size` outside the `written` ranges.
pub(super) fn zero_unwritten(
    dst: clif::Value,
    size: u32,
    mut written: Vec<(u32, u32)>,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) {
    written.sort_unstable();
    let mut zeroed = 0;
    for (offset, len) in written.into_iter().chain([(size, 0)]) {
        if offset > zeroed {
            let gap = builder.ins().iadd_imm_s(dst, i64::from(zeroed));
            zero_bytes(gap, offset - zeroed, config, builder);
        }
        zeroed = zeroed.max(offset + len);
    }
}

/// Writes the `size`-byte contents of `value` to `dst`. Native undef values
/// are zero, so an undef value zeroes `dst` without a zeroed temporary.
pub(super) fn store_indirect(
    function: &Function,
    value: ValueId,
    dst: clif::Value,
    size: u32,
    value_map: &HashMap<ValueId, clif::Value>,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    if is_undef(function, value) {
        zero_bytes(dst, size, config, builder);
    } else {
        let src = resolve_value(function, value, value_map, builder)?;
        copy_bytes(src, dst, size, config, builder);
    }
    Ok(())
}

/// Resolves `value` like `resolve_value`, but reads an undef aggregate from a
/// fresh zeroed slot. Consumers that only copy a value use `store_indirect`.
pub(super) fn resolve_operand(
    function: &Function,
    value: ValueId,
    value_map: &HashMap<ValueId, clif::Value>,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let ty = function.dfg.value_ty(value);
    if !is_undef(function, value) || !uses_indirect_value_representation(function.ctx(), ty) {
        return resolve_value(function, value, value_map, builder);
    }
    let address = create_stack_slot_for_type(ty, function.ctx(), builder)?;
    zero_bytes(
        address,
        value_storage_size(ty, function.ctx())?,
        config,
        builder,
    );
    Ok(address)
}

pub(super) fn translate_bitcast(
    value: clif::Value,
    from_ty: Type,
    to_ty: Type,
    ctx: &ModuleCtx,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let size = value_storage_size(from_ty, ctx)?;
    if size != value_storage_size(to_ty, ctx)? {
        return Err(format!(
            "bitcast requires equal-sized types: {from_ty:?} to {to_ty:?}"
        ));
    }
    let from_indirect = uses_indirect_value_representation(ctx, from_ty);
    if uses_indirect_value_representation(ctx, to_ty) {
        // A cast creates a value, not an alias to its source storage. Allocate
        // for the destination layout, which may require stronger alignment.
        let dest = create_stack_slot_for_type(to_ty, ctx, builder)?;
        if from_indirect {
            copy_bytes(value, dest, size, config, builder);
        } else {
            builder.ins().store(MemFlagsData::new(), value, dest, 0);
        }
        Ok(dest)
    } else {
        let clif_ty = sonatina_type_to_clif_or_err(to_ty, config.pointer_type())?;
        if from_indirect {
            Ok(builder.ins().load(clif_ty, MemFlagsData::new(), value, 0))
        } else if builder.func.dfg.value_type(value) == clif_ty {
            Ok(value)
        } else {
            Err(format!(
                "unsupported scalar bitcast: {from_ty:?} to {to_ty:?}"
            ))
        }
    }
}

fn storage_chunks(size: u32) -> impl Iterator<Item = (i32, clif::Type)> {
    let mut offset = 0;
    std::iter::from_fn(move || {
        let (bytes, ty) = match size - offset {
            0 => return None,
            1 => (1, clif::types::I8),
            2..=3 => (2, clif::types::I16),
            4..=7 => (4, clif::types::I32),
            _ => (8, clif::types::I64),
        };
        let chunk = (offset as i32, ty);
        offset += bytes;
        Some(chunk)
    })
}

pub(super) fn translate_aggregate_projection(
    ctx: &ModuleCtx,
    function: &Function,
    values: &[ValueId],
    inst_name: &str,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let Some((&base_value, indices)) = values.split_first() else {
        return Err(format!("{inst_name} requires a base value"));
    };
    let base = resolve_value(function, base_value, value_map, builder)?;
    let mut offset = 0i64;
    let mut current_ty = function.dfg.value_ty(base_value);

    for idx_value in indices {
        let idx = constant_value_index(function, *idx_value, inst_name)?;
        let (field_offset, elem_ty) = aggregate_elem_offset(ctx, current_ty, idx)?;
        offset += i64::from(field_offset);
        current_ty = elem_ty;
    }

    Ok(if offset == 0 {
        base
    } else {
        builder.ins().iadd_imm_s(base, offset)
    })
}

pub(super) fn translate_gep(
    ctx: &ModuleCtx,
    function: &Function,
    values: &[ValueId],
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let Some((&base_value, indices)) = values.split_first() else {
        return Err("gep requires a base pointer".into());
    };
    let mut addr = resolve_value(function, base_value, value_map, builder)?;
    let mut current_ty = function.dfg.value_ty(base_value);

    for &idx_value in indices {
        let Some(compound) = current_ty.resolve_compound(ctx) else {
            return Err(format!(
                "cannot index through non-compound type {current_ty:?}"
            ));
        };
        match compound {
            CompoundType::Ptr(elem) | CompoundType::Array { elem, .. } => {
                let index = resolve_index(function, idx_value, true, value_map, builder)?;
                let elem_size = builder
                    .ins()
                    .iconst(clif::types::I64, i64::from(value_storage_size(elem, ctx)?));
                let offset = builder.ins().imul(index, elem_size);
                addr = builder.ins().iadd(addr, offset);
                current_ty = elem;
            }
            CompoundType::Struct(_) => {
                let idx = constant_value_index(function, idx_value, "gep")?;
                let (offset, field_ty) = aggregate_elem_offset(ctx, current_ty, idx)?;
                addr = builder.ins().iadd_imm_s(addr, i64::from(offset));
                current_ty = field_ty;
            }
            CompoundType::Func { .. }
            | CompoundType::Enum(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_) => {
                return Err(format!("cannot index through {compound:?}"));
            }
        }
    }

    Ok(addr)
}

pub(super) fn resolve_index(
    function: &Function,
    value: ValueId,
    signed: bool,
    value_map: &HashMap<ValueId, clif::Value>,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let ty = function.dfg.value_ty(value);
    let value = resolve_value(function, value, value_map, builder)?;
    let value = if ty == Type::I256 {
        load_i256_limb(value, 0, builder)
    } else {
        value
    };
    let value = if signed {
        signed_scalar(value, ty, builder)
    } else {
        value
    };
    Ok(resize_int_value(value, clif::types::I64, signed, builder))
}

pub(super) fn value_storage_size(ty: Type, ctx: &ModuleCtx) -> Result<u32, String> {
    let size = ctx
        .size_of(ty)
        .map_err(|error| format!("cannot lay out type {ty:?}: {error:?}"))?;
    u32::try_from(size).map_err(|_| format!("type {ty:?} is too large for Cranelift"))
}

pub(super) fn value_storage_alignment(ty: Type, ctx: &ModuleCtx) -> Result<u64, String> {
    let alignment = ctx
        .align_of(ty)
        .map_err(|error| format!("cannot align type {ty:?}: {error:?}"))?;
    if !alignment.is_power_of_two() {
        return Err(format!(
            "type {ty:?} has non-power-of-two alignment {alignment}"
        ));
    }
    Ok(alignment as u64)
}

pub(super) fn stack_slot_data(ty: Type, ctx: &ModuleCtx) -> Result<StackSlotData, String> {
    let alignment = value_storage_alignment(ty, ctx)?;
    let align_shift = u8::try_from(alignment.trailing_zeros())
        .map_err(|_| format!("type {ty:?} alignment {alignment} is too large for Cranelift"))?;
    Ok(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        value_storage_size(ty, ctx)?.max(1),
        align_shift,
    ))
}

pub(super) fn aggregate_elem_offset(
    ctx: &ModuleCtx,
    aggregate_ty: Type,
    idx: usize,
) -> Result<(i32, Type), String> {
    if let Some((offset, ty)) = ctx.aggregate_elem_offset(aggregate_ty, idx) {
        return Ok((
            i32::try_from(offset)
                .map_err(|_| format!("aggregate offset {offset} overflows i32"))?,
            ty,
        ));
    }
    if let Some(
        sonatina_ir::types::CompoundType::ObjRef(inner)
        | sonatina_ir::types::CompoundType::ConstRef(inner),
    ) = aggregate_ty.resolve_compound(ctx)
    {
        return aggregate_elem_offset(ctx, inner, idx);
    }
    Err(format!(
        "cannot compute aggregate element offset for {aggregate_ty:?}[{idx}]"
    ))
}

pub(super) fn constant_value_index(
    function: &Function,
    value_id: ValueId,
    inst_name: &str,
) -> Result<usize, String> {
    function
        .dfg
        .value_imm(value_id)
        .and_then(|imm| imm.to_nonnegative_usize())
        .ok_or_else(|| format!("{inst_name} index must be a nonnegative constant"))
}

pub(super) fn compute_element_size(obj_ty: Type, ctx: &ModuleCtx) -> Result<usize, String> {
    match obj_ty.resolve_compound(ctx) {
        Some(CompoundType::Array { elem, .. }) => ctx
            .size_of(elem)
            .map_err(|error| format!("cannot lay out array element {elem:?}: {error:?}")),
        Some(CompoundType::ObjRef(inner) | CompoundType::ConstRef(inner)) => {
            compute_element_size(inner, ctx)
        }
        _ => Err(format!("cannot index non-array value of type {obj_ty:?}")),
    }
}
