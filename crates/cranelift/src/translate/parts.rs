//! Small aggregates held in registers (`register_parts`), translated to one
//! Cranelift value per part rather than to the address of storage. Storage
//! is written only where the value must be in memory: a store, a reference
//! passed to a public or external function, a materialized object, a cast.

use std::ops::Range;

use cranelift_codegen::ir::{self as clif, InstBuilder, MemFlagsData};
use cranelift_frontend::FunctionBuilder;
use smallvec::{SmallVec, smallvec};
use sonatina_codegen::isa::native::MAX_PARTS;
pub(super) use sonatina_codegen::isa::native::{
    Parts, is_aggregate, register_parts, uses_indirect_value_representation,
};
use sonatina_ir::{Function, Type, Value, ValueId, module::ModuleCtx};

use super::{
    LOAD_FLAGS, ValueMap, create_stack_slot_for_type, normalize_scalar, resolve_value,
    sonatina_scalar_type_to_clif_or_err, sonatina_type_to_clif_or_err, value_pieces,
    value_storage_size,
};

pub(super) type PartValues = SmallVec<[clif::Value; MAX_PARTS]>;

/// The Cranelift type of the target's pointers.
pub(super) fn pointer_clif_type(ctx: &ModuleCtx) -> Result<clif::Type, String> {
    sonatina_scalar_type_to_clif_or_err(ctx.type_layout.pointer_repl())
}

/// The parts of `parts` within `offset..offset + size` of the value: a
/// field's, or an enum variant field's.
pub(super) fn parts_within(parts: &Parts, offset: u32, size: u32) -> Range<usize> {
    let from = |bound: u32| {
        parts
            .iter()
            .position(|part| part.offset >= bound)
            .unwrap_or(parts.len())
    };
    from(offset)..from(offset + size)
}

/// The part values of `value`, a value of a type held in registers. Undef
/// reads as zero, as everywhere in native code.
pub(super) fn resolve_parts(
    function: &Function,
    value: ValueId,
    parts: &Parts,
    value_map: &ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<PartValues, String> {
    if let Some(values) = value_map.parts(&value) {
        return Ok(values.clone());
    }
    match function.dfg.value(value) {
        Value::Undef { .. } => zero_parts(function.ctx(), parts, builder),
        other => Err(format!(
            "unresolved register aggregate v{}: {other:?}",
            value.0
        )),
    }
}

/// Zero for each part.
pub(super) fn zero_parts(
    ctx: &ModuleCtx,
    parts: &Parts,
    builder: &mut FunctionBuilder,
) -> Result<PartValues, String> {
    let pointer_type = pointer_clif_type(ctx)?;
    parts
        .iter()
        .map(|part| {
            let ty = sonatina_type_to_clif_or_err(part.ty, pointer_type)?;
            Ok(builder.ins().iconst(ty, 0))
        })
        .collect()
}

/// Loads each part from storage at `src + offset`, at its own width.
pub(super) fn load_parts(
    ctx: &ModuleCtx,
    parts: &Parts,
    src: clif::Value,
    offset: i32,
    builder: &mut FunctionBuilder,
) -> Result<PartValues, String> {
    let pointer_type = pointer_clif_type(ctx)?;
    parts
        .iter()
        .map(|part| {
            let ty = sonatina_type_to_clif_or_err(part.ty, pointer_type)?;
            let value = builder
                .ins()
                .load(ty, LOAD_FLAGS, src, offset + part.offset as i32);
            Ok(normalize_scalar(value, part.ty, builder))
        })
        .collect()
}

/// Stores a `ty` value's parts to storage at `dst + offset`, and zeros to
/// its padding, as copies of values in storage write.
pub(super) fn store_parts(
    ctx: &ModuleCtx,
    ty: Type,
    parts: &Parts,
    values: &[clif::Value],
    dst: clif::Value,
    offset: i32,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    for (part, &value) in parts.iter().zip(values) {
        builder
            .ins()
            .store(MemFlagsData::new(), value, dst, offset + part.offset as i32);
    }
    for (padding, piece_ty) in value_pieces(ty, value_storage_size(ty, ctx)?, ctx)?
        .into_iter()
        .filter_map(|piece| piece.padding())
    {
        let zero = builder.ins().iconst(piece_ty, 0);
        builder
            .ins()
            .store(MemFlagsData::new(), zero, dst, offset + padding);
    }
    Ok(())
}

/// The address of a fresh stack slot holding a `ty` value's parts.
pub(super) fn materialize_parts(
    ctx: &ModuleCtx,
    ty: Type,
    parts: &Parts,
    values: &[clif::Value],
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let address = create_stack_slot_for_type(ty, ctx, builder)?;
    store_parts(ctx, ty, parts, values, address, 0, builder)?;
    Ok(address)
}

/// The part values of `value`, a field of an aggregate held in registers: a
/// scalar's own value, the parts of an aggregate held in registers, and none
/// for an aggregate without parts.
pub(super) fn field_part_values(
    function: &Function,
    value: ValueId,
    value_map: &ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<PartValues, String> {
    let ctx = function.ctx();
    let ty = function.dfg.value_ty(value);
    if let Some(parts) = register_parts(ctx, ty) {
        resolve_parts(function, value, &parts, value_map, builder)
    } else if is_aggregate(ctx, ty) {
        Ok(PartValues::new())
    } else {
        Ok(smallvec![resolve_value(
            function, value, value_map, builder
        )?])
    }
}

/// Records `values`, some parts of an aggregate held in registers, as the
/// translation of its field `value`. A field aggregate without parts gets
/// storage of its own, which holds no bytes.
pub(super) fn insert_field_part_values(
    ctx: &ModuleCtx,
    value: ValueId,
    ty: Type,
    values: &[clif::Value],
    value_map: &mut ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    if register_parts(ctx, ty).is_some() {
        value_map.insert_parts(value, values.into());
    } else if is_aggregate(ctx, ty) {
        value_map.insert(value, create_stack_slot_for_type(ty, ctx, builder)?);
    } else {
        let [part] = values else {
            return Err(format!(
                "scalar field v{} spans {} parts",
                value.0,
                values.len()
            ));
        };
        value_map.insert(value, *part);
    }
    Ok(())
}

/// Overwrites the parts of `values` within `offset..offset + size` with
/// `field`.
pub(super) fn replace_parts(
    parts: &Parts,
    values: &mut PartValues,
    offset: u32,
    size: u32,
    field: &[clif::Value],
) -> Result<(), String> {
    let range = parts_within(parts, offset, size);
    if range.len() != field.len() {
        return Err(format!(
            "a field at offset {offset} has {} parts, not {}",
            range.len(),
            field.len()
        ));
    }
    values[range].copy_from_slice(field);
    Ok(())
}
