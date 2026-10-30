//! Small aggregates held in registers. A struct, array or enum of a few
//! integer and pointer fields is translated to one Cranelift value per scalar
//! field, an enum's tag first, rather than to the address of storage. Storage
//! is written only where the value must be in memory: a store, a reference
//! passed to a public or external function, a materialized object, a cast.

use std::ops::Range;

use cranelift_codegen::ir::{self as clif, InstBuilder, MemFlagsData};
use cranelift_frontend::FunctionBuilder;
use smallvec::SmallVec;
use sonatina_ir::{Function, Type, Value, ValueId, module::ModuleCtx, types::CompoundType};

use super::{
    ValueMap, create_stack_slot_for_type, normalize_scalar, resolve_value,
    sonatina_scalar_type_to_clif_or_err, sonatina_type_to_clif_or_err, value_pieces,
    value_storage_size,
};

/// Values held in registers have at most this many parts.
const MAX_PARTS: usize = 4;

/// A scalar field, element or enum tag of a value held in registers, at its
/// offset in the value's storage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Part {
    pub offset: u32,
    pub ty: Type,
}

pub(super) type Parts = SmallVec<[Part; MAX_PARTS]>;
pub(super) type PartValues = SmallVec<[clif::Value; MAX_PARTS]>;

/// The parts of `ty` if translation holds its values in registers: a struct,
/// array or enum whose scalar fields are at most `MAX_PARTS` integers and
/// pointers of at most a word, of which only one enum variant has any.
pub(super) fn register_parts(ctx: &ModuleCtx, ty: Type) -> Option<Parts> {
    let mut parts = Parts::new();
    (is_aggregate(ctx, ty) && collect_parts(ctx, ty, 0, &mut parts) && !parts.is_empty())
        .then_some(parts)
}

/// Whether `ty` is a struct, array or enum.
pub(super) fn is_aggregate(ctx: &ModuleCtx, ty: Type) -> bool {
    matches!(
        ty.resolve_compound(ctx),
        Some(CompoundType::Array { .. } | CompoundType::Struct(_) | CompoundType::Enum(_))
    )
}

fn collect_parts(ctx: &ModuleCtx, ty: Type, base: u32, parts: &mut Parts) -> bool {
    match ty.resolve_compound(ctx) {
        Some(CompoundType::Struct(data)) => {
            !data.packed
                && (0..data.fields.len()).all(|idx| {
                    ctx.aggregate_elem_offset(ty, idx)
                        .is_some_and(|(offset, field)| {
                            collect_parts(ctx, field, base + offset as u32, parts)
                        })
                })
        }
        Some(CompoundType::Array { elem, len }) => {
            len <= MAX_PARTS
                && ctx.size_of(elem).is_ok_and(|stride| {
                    (0..len).all(|index| {
                        collect_parts(ctx, elem, base + (index * stride) as u32, parts)
                    })
                })
        }
        Some(CompoundType::Enum(data)) => {
            let mut with_fields = data
                .variants
                .iter()
                .enumerate()
                .filter(|(_, variant)| !variant.fields.is_empty());
            let fields = with_fields.next();
            with_fields.next().is_none()
                && push_part(parts, base, data.tag_ty())
                && fields.is_none_or(|(variant, variant_data)| {
                    (0..variant_data.fields.len()).all(|field| {
                        ctx.enum_variant_field_offset(ty, variant, field)
                            .is_some_and(|(offset, field_ty)| {
                                collect_parts(ctx, field_ty, base + offset as u32, parts)
                            })
                    })
                })
        }
        Some(CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_)) => {
            push_part(parts, base, ty)
        }
        Some(CompoundType::Func { .. }) => false,
        None => push_part(parts, base, ty),
    }
}

fn push_part(parts: &mut Parts, offset: u32, ty: Type) -> bool {
    let scalar = matches!(
        ty,
        Type::I1 | Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::Compound(_)
    );
    scalar && parts.len() < MAX_PARTS && {
        parts.push(Part { offset, ty });
        true
    }
}

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
            let value =
                builder
                    .ins()
                    .load(ty, MemFlagsData::new(), src, offset + part.offset as i32);
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
        Ok(smallvec::smallvec![resolve_value(
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
