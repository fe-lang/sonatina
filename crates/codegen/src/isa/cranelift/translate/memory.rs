use std::collections::HashMap;

use cranelift_codegen::ir::{
    self as clif, InstBuilder, MemFlagsData, StackSlotData, StackSlotKind,
};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::{
    Function, Immediate, Type, Value, ValueId, global_variable::GvInitializer, module::ModuleCtx,
    types::CompoundType,
};

use super::{load_i256_limb, resize_int_value, resolve_value, signed_scalar};

pub(super) fn storage_chunks(size: u32) -> impl Iterator<Item = (i32, clif::Type)> {
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

pub(super) fn materialize_gv_initializer(
    init: &GvInitializer,
    ty: Type,
    base: clif::Value,
    offset: i32,
    ctx: &ModuleCtx,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    match init {
        GvInitializer::Immediate(imm) => {
            let matches_type = imm.ty() == ty
                || (ty.is_pointer(ctx) && imm.ty() == ctx.type_layout.pointer_repl());
            if !matches_type {
                return Err(format!(
                    "global initializer type mismatch: expected {ty:?}, found {:?}",
                    imm.ty()
                ));
            }

            match imm {
                Immediate::I1(v) => {
                    let val = builder.ins().iconst(clif::types::I8, i64::from(*v));
                    builder.ins().store(MemFlagsData::new(), val, base, offset);
                }
                Immediate::I8(v) => {
                    let val = builder.ins().iconst(clif::types::I8, i64::from(*v));
                    builder.ins().store(MemFlagsData::new(), val, base, offset);
                }
                Immediate::I16(v) => {
                    let val = builder.ins().iconst(clif::types::I16, i64::from(*v));
                    builder.ins().store(MemFlagsData::new(), val, base, offset);
                }
                Immediate::I32(v) => {
                    let val = builder.ins().iconst(clif::types::I32, i64::from(*v));
                    builder.ins().store(MemFlagsData::new(), val, base, offset);
                }
                Immediate::I64(v) => {
                    let val = builder.ins().iconst(clif::types::I64, *v);
                    builder.ins().store(MemFlagsData::new(), val, base, offset);
                }
                Immediate::I128(v) => {
                    store_little_endian_words(&v.to_le_bytes(), base, offset, builder)?;
                }
                Immediate::I256(v) => {
                    store_little_endian_words(
                        &v.to_u256().to_little_endian(),
                        base,
                        offset,
                        builder,
                    )?;
                }
                Immediate::EnumTag { .. } => {
                    return Err("enum-tag global initializer survived legalization".to_string());
                }
            }
        }
        GvInitializer::Array(elems) => {
            let Some(CompoundType::Array { elem, len }) = ty.resolve_compound(ctx) else {
                return Err(format!("array initializer used for non-array type {ty:?}"));
            };
            if elems.len() != len {
                return Err(format!(
                    "array initializer length mismatch: expected {len}, found {}",
                    elems.len()
                ));
            }
            let elem_size = value_storage_size(elem, ctx)?;
            for (index, elem_init) in elems.iter().enumerate() {
                let elem_offset = u32::try_from(index)
                    .ok()
                    .and_then(|index| index.checked_mul(elem_size))
                    .and_then(|offset| i32::try_from(offset).ok())
                    .and_then(|elem_offset| offset.checked_add(elem_offset))
                    .ok_or_else(|| "array initializer offset overflows i32".to_string())?;
                materialize_gv_initializer(elem_init, elem, base, elem_offset, ctx, builder)?;
            }
        }
        GvInitializer::Struct(fields) => {
            let Some(CompoundType::Struct(data)) = ty.resolve_compound(ctx) else {
                return Err(format!(
                    "struct initializer used for non-struct type {ty:?}"
                ));
            };
            if fields.len() != data.fields.len() {
                return Err(format!(
                    "struct initializer field count mismatch: expected {}, found {}",
                    data.fields.len(),
                    fields.len()
                ));
            }
            for (index, (field_init, field_ty)) in fields.iter().zip(data.fields).enumerate() {
                let (field_offset, _) = aggregate_elem_offset(ctx, ty, index)?;
                let field_offset = offset
                    .checked_add(field_offset)
                    .ok_or_else(|| "struct initializer offset overflows i32".to_string())?;
                materialize_gv_initializer(field_init, field_ty, base, field_offset, ctx, builder)?;
            }
        }
    }
    Ok(())
}

pub(super) fn store_little_endian_words(
    bytes: &[u8],
    base: clif::Value,
    offset: i32,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let (words, remainder) = bytes.as_chunks::<8>();
    if !remainder.is_empty() {
        return Err("wide immediate contains an incomplete word".to_string());
    }
    for (index, bytes) in words.iter().enumerate() {
        let word_offset = i32::try_from(index * 8)
            .ok()
            .and_then(|word_offset| offset.checked_add(word_offset))
            .ok_or_else(|| "wide immediate offset overflows i32".to_string())?;
        let value = builder
            .ins()
            .iconst(clif::types::I64, u64::from_le_bytes(*bytes) as i64);
        builder
            .ins()
            .store(MemFlagsData::new(), value, base, word_offset);
    }
    Ok(())
}

pub(super) fn value_storage_size(ty: Type, ctx: &ModuleCtx) -> Result<u32, String> {
    let size = ctx
        .size_of(ty)
        .map_err(|error| format!("cannot lay out type {ty:?}: {error:?}"))?;
    u32::try_from(size).map_err(|_| format!("type {ty:?} is too large for Cranelift"))
}

pub(super) fn stack_slot_data(ty: Type, ctx: &ModuleCtx) -> Result<StackSlotData, String> {
    let alignment = ctx
        .align_of(ty)
        .map_err(|error| format!("cannot align type {ty:?}: {error:?}"))?;
    if !alignment.is_power_of_two() {
        return Err(format!(
            "type {ty:?} has non-power-of-two alignment {alignment}"
        ));
    }
    let align_shift = u8::try_from(alignment.trailing_zeros())
        .map_err(|_| format!("type {ty:?} alignment {alignment} is too large for Cranelift"))?;
    Ok(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        value_storage_size(ty, ctx)?.max(1),
        align_shift,
    ))
}

pub(super) fn referenced_value_storage_size(ty: Type, ctx: &ModuleCtx) -> Result<u32, String> {
    match ty.resolve_compound(ctx) {
        Some(CompoundType::ObjRef(inner) | CompoundType::ConstRef(inner)) => {
            value_storage_size(inner, ctx)
        }
        _ => Err(format!(
            "expected object or constant reference type, got {ty:?}"
        )),
    }
}

pub(super) fn referenced_value_stack_slot_data(
    ty: Type,
    ctx: &ModuleCtx,
) -> Result<StackSlotData, String> {
    match ty.resolve_compound(ctx) {
        Some(CompoundType::ObjRef(inner) | CompoundType::ConstRef(inner)) => {
            stack_slot_data(inner, ctx)
        }
        _ => Err(format!(
            "expected object or constant reference type, got {ty:?}"
        )),
    }
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

pub(super) fn is_undef_value(function: &Function, value_id: ValueId) -> bool {
    matches!(function.dfg.value(value_id), Value::Undef { .. })
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
