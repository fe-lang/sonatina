use cranelift_codegen::{
    ir::{
        self as clif, InstBuilder, InstructionData, MemFlagsData, Opcode, StackSlotData,
        StackSlotKind,
    },
    isa::TargetFrontendConfig,
};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::{
    Function, Immediate, Type, Value, ValueId,
    global_variable::GvInitializer,
    inst::data::{ConstLoad, ConstRef},
    module::ModuleCtx,
    types::CompoundType,
};

use super::{
    LOAD_FLAGS, ValueMap, is_aggregate, load_limbs, load_parts, pointer_clif_type, register_parts,
    resize_int_value, resolve_i256, resolve_parts, resolve_value, signed_scalar,
    sonatina_type_to_clif_or_err, store_limbs, store_parts, uses_indirect_value_representation,
};

/// Copies and fills of at most this many bytes use inline loads and stores.
/// Larger ones call `memcpy` or `memset`, so their code size is constant.
pub(super) const INLINE_MEMORY_BYTES: u32 = 128;

/// Copies the `ty` value at `src` to distinct, non-overlapping storage at
/// `dst`.
pub(super) fn copy_value(
    ty: Type,
    src: clif::Value,
    dst: clif::Value,
    ctx: &ModuleCtx,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let size = value_storage_size(ty, ctx)?;
    if size > INLINE_MEMORY_BYTES {
        let size = builder.ins().iconst(config.pointer_type(), i64::from(size));
        builder.call_memcpy(config, dst, src, size);
        return Ok(());
    }
    for piece in value_pieces(ty, size, ctx)? {
        if let Piece::Field(offset, ty) = piece {
            let value = builder.ins().load(ty, LOAD_FLAGS, src, offset);
            builder.ins().store(MemFlagsData::new(), value, dst, offset);
        }
    }
    Ok(())
}

/// Copies the `ty` value at `src`, of at most `INLINE_MEMORY_BYTES`, to `dst`,
/// which may overlap it.
pub(super) fn move_value(
    ty: Type,
    src: clif::Value,
    dst: clif::Value,
    ctx: &ModuleCtx,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let size = value_storage_size(ty, ctx)?;
    debug_assert!(size <= INLINE_MEMORY_BYTES);
    move_pieces(value_pieces(ty, size, ctx)?, src, dst, builder);
    Ok(())
}

/// Stores a forwarded load's value, read from its source `src`, at `dst`. A
/// load forwarded to its one copy, which may overlap its source, is small
/// enough to move inline; a larger one reads a local object that nothing
/// writes after the load, which no other storage overlaps.
pub(super) fn forward_value(
    ty: Type,
    src: clif::Value,
    dst: clif::Value,
    ctx: &ModuleCtx,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    if value_storage_size(ty, ctx)? <= INLINE_MEMORY_BYTES {
        move_value(ty, src, dst, ctx, builder)
    } else {
        copy_value(ty, src, dst, ctx, config, builder)
    }
}

/// Copies at most `INLINE_MEMORY_BYTES` between storage that may overlap.
pub(super) fn move_bytes(
    src: clif::Value,
    dst: clif::Value,
    size: u32,
    builder: &mut FunctionBuilder,
) {
    debug_assert!(size <= INLINE_MEMORY_BYTES);
    let pieces = aligned_chunks(0, size).map(|(offset, ty)| Piece::Field(offset, ty));
    move_pieces(pieces, src, dst, builder);
}

/// Copies `pieces` from `src` to `dst`, loading every field piece before
/// storing any, so the ranges may overlap.
fn move_pieces(
    pieces: impl IntoIterator<Item = Piece>,
    src: clif::Value,
    dst: clif::Value,
    builder: &mut FunctionBuilder,
) {
    let values: Vec<_> = pieces
        .into_iter()
        .filter_map(|piece| match piece {
            Piece::Field(offset, ty) => {
                Some((offset, builder.ins().load(ty, LOAD_FLAGS, src, offset)))
            }
            Piece::Padding(..) => None,
        })
        .collect();
    for (offset, value) in values {
        builder.ins().store(MemFlagsData::new(), value, dst, offset);
    }
}

/// A piece of a value's storage: bytes of a field, which a copy moves with
/// one load and one store, or padding, which it skips.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Piece {
    Field(i32, clif::Type),
    Padding(i32, clif::Type),
}

/// The pieces of a copy of a `size`-byte `ty` value. The CPU forwards a store
/// to a load only if the store covers the load; otherwise the load waits for
/// the store to reach the cache. Fields are written by their own stores, often
/// narrower than a word, so the pieces split wherever a scalar field starts or
/// ends, then as `aligned_chunks`, as zero fills split too. Padding is not
/// part of the value, and often nothing has written it, so a copy skips it.
pub(super) fn value_pieces(ty: Type, size: u32, ctx: &ModuleCtx) -> Result<Vec<Piece>, String> {
    let mut fields = Vec::new();
    field_ranges(ty, 0, ctx, &mut fields)?;
    let mut bounds: Vec<u32> = fields
        .iter()
        .flat_map(|&(start, end)| [start, end])
        .chain([0, size])
        .collect();
    bounds.sort_unstable();
    bounds.dedup();
    Ok(bounds
        .windows(2)
        .flat_map(|range| {
            let (start, end) = (range[0], range[1]);
            let field = fields
                .iter()
                .any(|&(first, last)| first <= start && end <= last);
            aligned_chunks(start, end).map(move |(offset, ty)| {
                if field {
                    Piece::Field(offset, ty)
                } else {
                    Piece::Padding(offset, ty)
                }
            })
        })
        .collect())
}

/// Pushes the byte ranges, from `base`, of the scalar fields of a `ty` value.
/// An array of scalars narrower than a word counts as one field: such arrays
/// are mostly written whole, and splitting them would multiply the pieces.
/// Enum variants share payload bytes. Within each word, fields of different
/// variants that overlap count as one, so a narrow field does not split a
/// wider one, whose reads would span several stores; `store_variant` stores
/// the narrow field whole. They stay apart where a variant has several fields
/// in the word, each with its own store.
fn field_ranges(
    ty: Type,
    base: u32,
    ctx: &ModuleCtx,
    fields: &mut Vec<(u32, u32)>,
) -> Result<(), String> {
    match ty.resolve_compound(ctx) {
        Some(CompoundType::Struct(data)) if !data.packed => {
            for idx in 0..data.fields.len() {
                let (offset, field) = aggregate_elem_offset(ctx, ty, idx)?;
                field_ranges(field, base + offset as u32, ctx, fields)?;
            }
        }
        Some(CompoundType::Array { elem, len })
            if is_aggregate(ctx, elem) || value_storage_size(elem, ctx)? >= 8 =>
        {
            let stride = value_storage_size(elem, ctx)?;
            for index in 0..len as u32 {
                field_ranges(elem, base + index * stride, ctx, fields)?;
            }
        }
        Some(CompoundType::Enum(data)) => {
            fields.push((base, base + value_storage_size(data.tag_ty(), ctx)?));
            let mut variants = Vec::new();
            for (variant, variant_data) in data.variants.iter().enumerate() {
                let mut leaves = Vec::new();
                for field in 0..variant_data.fields.len() {
                    let (offset, field_ty) = ctx
                        .enum_variant_field_offset(ty, variant, field)
                        .ok_or_else(|| format!("cannot lay out field {field} of {ty:?}"))?;
                    field_ranges(field_ty, base + offset as u32, ctx, &mut leaves)?;
                }
                // Each field's part in each word it spans.
                let words = |(start, end): (u32, u32)| {
                    (start / 8..end.div_ceil(8))
                        .map(move |word| (start.max(word * 8), end.min(word * 8 + 8)))
                };
                variants.push(leaves.into_iter().flat_map(words).collect::<Vec<_>>());
            }
            let mut leaves: Vec<_> = variants.iter().flatten().copied().collect();
            leaves.sort_unstable();
            let mut overlaps: Vec<(u32, u32)> = Vec::new();
            for (start, end) in leaves {
                match overlaps.last_mut() {
                    Some(last) if start < last.1 => last.1 = last.1.max(end),
                    _ => overlaps.push((start, end)),
                }
            }
            for (start, end) in overlaps {
                let within = |&&(first, last): &&(u32, u32)| start <= first && last <= end;
                if variants
                    .iter()
                    .all(|leaves| leaves.iter().filter(within).count() <= 1)
                {
                    fields.push((start, end));
                } else {
                    fields.extend(variants.iter().flatten().filter(within));
                }
            }
        }
        _ => fields.push((base, base + value_storage_size(ty, ctx)?)),
    }
    Ok(())
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
    zero_range(dst, 0, size, builder);
}

/// Zeroes `dst + start..dst + end` in `aligned_chunks`.
fn zero_range(dst: clif::Value, start: u32, end: u32, builder: &mut FunctionBuilder) {
    for (offset, ty) in aligned_chunks(start, end) {
        let zero = builder.ins().iconst(ty, 0);
        builder.ins().store(MemFlagsData::new(), zero, dst, offset);
    }
}

/// Whether `value` is a whole constant global whose initializer is all zero
/// bits, such as the `[0; N]` an array starts as: storing it writes zeros,
/// with no loads.
fn is_zero_constant(function: &Function, value: ValueId) -> bool {
    let Some(global) = function
        .dfg
        .value_inst(value)
        .and_then(|inst| function.dfg.downcast::<&ConstLoad>(inst))
        .and_then(|load| function.dfg.value_inst(*load.object()))
        .and_then(|inst| function.dfg.downcast::<&ConstRef>(inst))
        .map(|const_ref| const_ref.global().gv())
    else {
        return false;
    };
    function.ctx().with_gv_store(|globals| {
        globals
            .gv_data(global)
            .initializer
            .as_ref()
            .is_none_or(is_zero_initializer)
    })
}

fn is_zero_initializer(init: &GvInitializer) -> bool {
    match init {
        GvInitializer::Immediate(Immediate::EnumTag { .. }) => false,
        GvInitializer::Immediate(imm) => imm.as_i256().is_zero(),
        GvInitializer::Array(elements) | GvInitializer::Struct(elements) => {
            elements.iter().all(is_zero_initializer)
        }
    }
}

pub(super) fn is_undef(function: &Function, value: ValueId) -> bool {
    matches!(function.dfg.value(value), Value::Undef { .. })
}

/// Zeroes the field bytes of the `ty` value at `dst` outside the `written`
/// ranges: the fields an insert chain on undef leaves, which read as zero.
/// Padding is not part of the value, so it keeps whatever it holds; a value
/// too large for inline copies has its gaps zeroed whole.
pub(super) fn zero_unwritten_fields(
    ty: Type,
    dst: clif::Value,
    mut written: Vec<(u32, u32)>,
    ctx: &ModuleCtx,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let size = value_storage_size(ty, ctx)?;
    written.sort_unstable();
    if size > INLINE_MEMORY_BYTES {
        let mut zeroed = 0;
        for (offset, len) in written.into_iter().chain([(size, 0)]) {
            if offset > zeroed && offset - zeroed > INLINE_MEMORY_BYTES {
                let gap = builder.ins().iadd_imm_s(dst, i64::from(zeroed));
                zero_bytes(gap, offset - zeroed, config, builder);
            } else if offset > zeroed {
                zero_range(dst, zeroed, offset, builder);
            }
            zeroed = zeroed.max(offset + len);
        }
        return Ok(());
    }
    for piece in value_pieces(ty, size, ctx)? {
        let Piece::Field(offset, piece_ty) = piece else {
            continue;
        };
        let mut start = offset as u32;
        let end = start + piece_ty.bytes();
        for &(at, len) in &written {
            if at >= end {
                break;
            }
            if at > start {
                zero_range(dst, start, at, builder);
            }
            start = start.max(at + len);
        }
        if start < end {
            zero_range(dst, start, end, builder);
        }
    }
    Ok(())
}

/// Loads the scalar or i256 value `result` of type `ty` from `src + offset`.
#[allow(clippy::too_many_arguments)]
pub(super) fn load_value(
    result: ValueId,
    ty: Type,
    src: clif::Value,
    offset: i32,
    flags: MemFlagsData,
    value_map: &mut ValueMap,
    ctx: &ModuleCtx,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    if ty == Type::I256 {
        let limbs = load_limbs(src, offset, flags, builder);
        value_map.insert_limbs(result, limbs);
    } else if let Some(parts) = register_parts(ctx, ty) {
        let values = load_parts(ctx, &parts, src, offset, flags, builder)?;
        value_map.insert_parts(result, values);
    } else {
        let clif_ty = sonatina_type_to_clif_or_err(ty, pointer_clif_type(ctx)?)?;
        let loaded = builder.ins().load(clif_ty, flags, src, offset);
        value_map.insert(result, loaded);
    }
    Ok(())
}

/// Stores the scalar, i256 or register-held aggregate `value` at
/// `dst + offset`.
pub(super) fn store_value(
    function: &Function,
    value: ValueId,
    dst: clif::Value,
    offset: i32,
    value_map: &ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let ty = function.dfg.value_ty(value);
    if ty == Type::I256 {
        let limbs = resolve_i256(function, value, value_map, builder)?;
        store_limbs(limbs, dst, offset, MemFlagsData::new(), builder);
    } else if let Some(parts) = register_parts(function.ctx(), ty) {
        let values = resolve_parts(function, value, &parts, value_map, builder)?;
        store_parts(&parts, &values, dst, offset, builder);
    } else {
        let value = resolve_value(function, value, value_map, builder)?;
        builder.ins().store(MemFlagsData::new(), value, dst, offset);
    }
    Ok(())
}

/// Writes `value`, stored as a `ty`, to `dst`. Native undef values are zero,
/// so an undef value zeroes `dst` without a zeroed temporary.
pub(super) fn store_indirect(
    function: &Function,
    value: ValueId,
    dst: clif::Value,
    ty: Type,
    value_map: &ValueMap,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    if is_undef(function, value) || is_zero_constant(function, value) {
        zero_bytes(
            dst,
            value_storage_size(ty, function.ctx())?,
            config,
            builder,
        );
    } else {
        let src = resolve_value(function, value, value_map, builder)?;
        copy_value(ty, src, dst, function.ctx(), config, builder)?;
    }
    Ok(())
}

/// Resolves `value` like `resolve_value`, but reads an undef aggregate from a
/// fresh zeroed slot. Consumers that only copy a value use `store_indirect`.
pub(super) fn resolve_operand(
    function: &Function,
    value: ValueId,
    value_map: &ValueMap,
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
            copy_value(from_ty, value, dest, ctx, config, builder)?;
        } else {
            builder.ins().store(MemFlagsData::new(), value, dest, 0);
        }
        Ok(dest)
    } else {
        let clif_ty = sonatina_type_to_clif_or_err(to_ty, config.pointer_type())?;
        if from_indirect {
            Ok(builder.ins().load(clif_ty, LOAD_FLAGS, value, 0))
        } else if builder.func.dfg.value_type(value) == clif_ty {
            Ok(value)
        } else {
            Err(format!(
                "unsupported scalar bitcast: {from_ty:?} to {to_ty:?}"
            ))
        }
    }
}

/// Splits `start..end` into loads or stores of at most a word, each at an
/// offset its size divides. Two such splits of overlapping ranges put each
/// piece of one within a piece of the other, or around it.
fn aligned_chunks(start: u32, end: u32) -> impl Iterator<Item = (i32, clif::Type)> {
    let mut offset = start;
    std::iter::from_fn(move || {
        let (bytes, ty) = [
            (8, clif::types::I64),
            (4, clif::types::I32),
            (2, clif::types::I16),
            (1, clif::types::I8),
        ]
        .into_iter()
        .find(|&(bytes, _)| offset.is_multiple_of(bytes) && offset + bytes <= end)?;
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
    value_map: &ValueMap,
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
    value_map: &ValueMap,
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
                let elem_size = i64::from(value_storage_size(elem, ctx)?);
                // A constant index adds a constant, which a load or store
                // can take as its displacement.
                addr = match iconst_value(index, &builder.func.dfg) {
                    Some(index) => builder
                        .ins()
                        .iadd_imm_s(addr, index.wrapping_mul(elem_size)),
                    None => {
                        let elem_size = builder.ins().iconst(clif::types::I64, elem_size);
                        let offset = builder.ins().imul(index, elem_size);
                        builder.ins().iadd(addr, offset)
                    }
                };
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

/// `address` as a base and a constant displacement, through the adds of
/// constants that address arithmetic builds. A load or store that takes the
/// displacement itself leaves the add to the address's other uses. Cranelift
/// computes a value before its first use, so a stack top that a tail call
/// passes on after loading the words below it would otherwise be computed at
/// the first load and held in a register of its own until the call.
/// Displacements stay within half of `i32`'s range, which leaves room for the
/// offsets of a value's pieces.
pub(super) fn split_displacement(
    address: clif::Value,
    dfg: &clif::DataFlowGraph,
) -> (clif::Value, i32) {
    let addend = |value| i32::try_from(iconst_value(value, dfg)?).ok();
    let (mut base, mut displacement) = (address, 0i32);
    while let Some(InstructionData::Binary {
        opcode: Opcode::Iadd,
        args: [lhs, rhs],
    }) = dfg.value_def(base).inst().map(|inst| dfg.insts[inst])
        && let Some((next, addend)) = addend(rhs)
            .map(|addend| (lhs, addend))
            .or_else(|| addend(lhs).map(|addend| (rhs, addend)))
        && let Some(sum) = displacement
            .checked_add(addend)
            .filter(|sum| sum.unsigned_abs() <= i32::MAX as u32 / 2)
    {
        base = next;
        displacement = sum;
    }
    (base, displacement)
}

/// The value of an `iconst`.
pub(super) fn iconst_value(value: clif::Value, dfg: &clif::DataFlowGraph) -> Option<i64> {
    match dfg.insts[dfg.value_def(value).inst()?] {
        InstructionData::UnaryImm {
            opcode: Opcode::Iconst,
            imm,
        } => Some(imm.bits()),
        _ => None,
    }
}

pub(super) fn resolve_index(
    function: &Function,
    value: ValueId,
    signed: bool,
    value_map: &ValueMap,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let ty = function.dfg.value_ty(value);
    let value = if ty == Type::I256 {
        resolve_i256(function, value, value_map, builder)?[0]
    } else {
        resolve_value(function, value, value_map, builder)?
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

pub(super) fn create_stack_slot_for_type(
    ty: Type,
    ctx: &ModuleCtx,
    builder: &mut FunctionBuilder,
) -> Result<clif::Value, String> {
    let slot = builder.create_sized_stack_slot(stack_slot_data(ty, ctx)?);
    Ok(builder.ins().stack_addr(clif::types::I64, slot, 0))
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

#[cfg(test)]
mod tests {
    use cranelift_codegen::ir::{
        self as clif, InstBuilder,
        types::{I8, I16, I32, I64},
    };
    use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
    use sonatina_ir::types::CompoundType;

    use super::{
        Piece::{self, Field, Padding},
        split_displacement, value_pieces, value_storage_size,
    };

    /// The pieces of a copy of `@T`, declared by `types`.
    fn pieces(types: &str) -> Vec<Piece> {
        let source = format!(
            "target = \"x86_64-unknown-native\"\n{types}\nfunc public %f(v0.*@T) {{\nblock0:\n    return;\n}}\n"
        );
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        let func = module.funcs()[0];
        let ptr = module.ctx.func_sig(func, |sig| sig.args()[0]);
        let Some(CompoundType::Ptr(ty)) = ptr.resolve_compound(&module.ctx) else {
            panic!("%f takes a pointer");
        };
        let size = value_storage_size(ty, &module.ctx).unwrap();
        value_pieces(ty, size, &module.ctx).unwrap()
    }

    #[test]
    fn displacements_split_off_adds_of_constants() {
        let mut func = clif::Function::new();
        func.signature.params.push(clif::AbiParam::new(I64));
        let mut context = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut func, &mut context);
        let block = builder.create_block();
        builder.append_block_params_for_function_params(block);
        builder.switch_to_block(block);
        let base = builder.block_params(block)[0];
        let below = builder.ins().iadd_imm_s(base, -64);
        let above = builder.ins().iadd_imm_s(below, 32);
        let eight = builder.ins().iconst(I64, 8);
        let swapped = builder.ins().iadd(eight, above);
        let index = builder.ins().imul(base, eight);
        let indexed = builder.ins().iadd(base, index);
        let past = builder.ins().iadd_imm_s(indexed, 16);
        let far = builder.ins().iadd_imm_s(base, i64::from(i32::MAX));
        let dfg = &builder.func.dfg;
        assert_eq!(split_displacement(above, dfg), (base, -32));
        assert_eq!(split_displacement(swapped, dfg), (base, -24));
        // A variable addend stops the walk, as does a displacement too wide
        // for a value's pieces to add their offsets to.
        assert_eq!(split_displacement(past, dfg), (indexed, 16));
        assert_eq!(split_displacement(far, dfg), (far, 0));
        assert_eq!(split_displacement(base, dfg), (base, 0));
    }

    #[test]
    fn pieces_split_at_narrow_fields_and_zero_padding() {
        // The tag, its padding, then the payload word.
        assert_eq!(
            pieces("type @T = enum { #None, #Some(*i8) };"),
            [
                Field(0, I8),
                Padding(1, I8),
                Padding(2, I16),
                Padding(4, I32),
                Field(8, I64)
            ]
        );
        assert_eq!(
            pieces("type @T = { i1, i32, i16 };"),
            [
                Field(0, I8),
                Padding(1, I8),
                Padding(2, I16),
                Field(4, I32),
                Field(8, I16),
                Padding(10, I16)
            ]
        );
    }

    #[test]
    fn narrow_variant_fields_do_not_split_wider_ones() {
        let tag = [
            Field(0, I8),
            Padding(1, I8),
            Padding(2, I16),
            Padding(4, I32),
        ];
        assert_eq!(
            pieces("type @T = enum { #Byte(i8), #Word(i64) };"),
            [&tag[..], &[Field(8, I64)]].concat()
        );
        // Each word holds one field per variant.
        assert_eq!(
            pieces("type @T = enum { #A(i8, i64), #B(i64, i16), #C(i32) };"),
            [&tag[..], &[Field(8, I64), Field(16, I64)]].concat()
        );
        // An i256 spans several pieces, from its own alignment.
        assert_eq!(
            pieces("type @T = enum { #Byte(i8), #Big(i256) };"),
            [
                &tag[..],
                &[
                    Padding(8, I64),
                    Field(16, I64),
                    Field(24, I64),
                    Field(32, I64),
                    Field(40, I64)
                ]
            ]
            .concat()
        );
    }

    #[test]
    fn fields_of_a_variant_in_other_words_do_not_split_a_word() {
        // fevm's journal entry: `#Account`'s three fields lie in different
        // words, each of which every variant fills with one field, so the
        // u256 fields copy as whole words.
        assert_eq!(
            pieces(
                "type @Field = enum { #Balance, #Nonce };
type @Opt = enum { #None, #Some(i256) };
type @Kind = enum { #Account(@Field, i256, i1), #Storage(i256, i256, i1), #Delegation(@Opt, i1) };
type @T = { i256, @Kind };"
            ),
            [
                Field(0, I64),
                Field(8, I64),
                Field(16, I64),
                Field(24, I64),
                Field(32, I8),
                Padding(33, I8),
                Padding(34, I16),
                Padding(36, I32),
                Padding(40, I64),
                Field(48, I64),
                Field(56, I64),
                Field(64, I64),
                Field(72, I64),
                Field(80, I64),
                Field(88, I64),
                Field(96, I64),
                Field(104, I64),
                Field(112, I8),
                Padding(113, I8),
                Padding(114, I16),
                Padding(116, I32),
                Padding(120, I64)
            ]
        );
    }

    #[test]
    fn variants_with_several_fields_in_a_word_split_it() {
        // A word load would span the stores of `#Two`'s fields.
        assert_eq!(
            pieces("type @T = enum { #Two(i8, i8), #Word(i64) };"),
            [
                Field(0, I8),
                Padding(1, I8),
                Padding(2, I16),
                Padding(4, I32),
                Field(8, I8),
                Field(9, I8),
                Field(10, I16),
                Field(12, I32)
            ]
        );
    }

    #[test]
    fn pieces_keep_words_and_byte_arrays_whole() {
        assert_eq!(
            pieces("type @T = { i64, [i8; 12], i256 };"),
            [
                Field(0, I64),
                Field(8, I64),
                Field(16, I32),
                Padding(20, I32),
                Padding(24, I64),
                Field(32, I64),
                Field(40, I64),
                Field(48, I64),
                Field(56, I64)
            ]
        );
    }
}
