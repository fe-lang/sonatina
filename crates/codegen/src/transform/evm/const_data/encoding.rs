use sonatina_ir::{
    Immediate, Module, Type, global_variable::GvInitializer, module::ModuleCtx, types::CompoundType,
};

use crate::transform::{aggregate::shape, evm::scalar_words::evm_scalar_word_bytes};

pub(super) fn const_leaf_count(module: &sonatina_ir::module::ModuleCtx, ty: Type) -> Option<u32> {
    if ty.is_integral() {
        return Some(1);
    }
    match ty.resolve_compound(module)? {
        CompoundType::Array { elem, len } => {
            const_leaf_count(module, elem)?.checked_mul(u32::try_from(len).ok()?)
        }
        CompoundType::Struct(s) => {
            if s.packed {
                return None;
            }
            s.fields.into_iter().try_fold(0u32, |count, field| {
                count.checked_add(const_leaf_count(module, field)?)
            })
        }
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Enum(_)
        | CompoundType::Func { .. } => None,
    }
}

pub(super) fn encode_const_words(
    module: &Module,
    ty: Type,
    init: &GvInitializer,
    out: &mut Vec<u8>,
) -> Option<()> {
    if ty.is_integral() {
        let GvInitializer::Immediate(imm) = init else {
            return None;
        };
        if imm.ty() != ty {
            return None;
        }
        out.extend_from_slice(&evm_scalar_word_bytes(*imm)?);
        return Some(());
    }

    match (ty.resolve_compound(&module.ctx)?, init) {
        (CompoundType::Array { elem, len }, GvInitializer::Array(items)) => {
            if items.len() != len {
                return None;
            }
            for item in items {
                encode_const_words(module, elem, item, out)?;
            }
            Some(())
        }
        (CompoundType::Struct(s), GvInitializer::Struct(fields)) => {
            if s.packed || fields.len() != s.fields.len() {
                return None;
            }
            for (field_ty, field) in s.fields.into_iter().zip(fields) {
                encode_const_words(module, field_ty, field, out)?;
            }
            Some(())
        }
        _ => None,
    }
}

pub(super) fn encode_runtime_object_const_bytes(
    module: &ModuleCtx,
    ty: Type,
    init: &GvInitializer,
) -> Option<Vec<u8>> {
    if ty.is_integral() {
        let GvInitializer::Immediate(imm) = init else {
            return None;
        };
        if imm.ty() != ty {
            return None;
        }
        return Some(evm_scalar_word_bytes(*imm)?.to_vec());
    }

    match (ty.resolve_compound(module)?, init) {
        (CompoundType::Array { elem, len }, GvInitializer::Array(items)) => {
            if items.len() != len {
                return None;
            }
            let mut bytes = Vec::with_capacity(shape::runtime_size_bytes(module, ty)? as usize);
            for item in items {
                bytes.extend(encode_runtime_object_const_bytes(module, elem, item)?);
            }
            Some(bytes)
        }
        (CompoundType::Struct(s), GvInitializer::Struct(fields)) => {
            if s.packed || fields.len() != s.fields.len() {
                return None;
            }
            let mut bytes = vec![0; shape::runtime_size_bytes(module, ty)? as usize];
            for (idx, (field_ty, field)) in s.fields.iter().copied().zip(fields).enumerate() {
                let (offset, _) =
                    shape::struct_field_offset_bytes(&s.fields, s.packed, idx, module)?;
                let field_bytes = encode_runtime_object_const_bytes(module, field_ty, field)?;
                let offset = offset as usize;
                bytes
                    .get_mut(offset..offset + field_bytes.len())?
                    .copy_from_slice(&field_bytes);
            }
            Some(bytes)
        }
        _ => None,
    }
}

pub(super) fn initializer_all_zero(module: &ModuleCtx, ty: Type, init: &GvInitializer) -> bool {
    if ty.is_integral() {
        return matches!(init, GvInitializer::Immediate(imm) if imm.ty() == ty && imm.is_zero());
    }

    match (ty.resolve_compound(module), init) {
        (Some(CompoundType::Array { elem, len }), GvInitializer::Array(items)) => {
            items.len() == len
                && items
                    .iter()
                    .all(|item| initializer_all_zero(module, elem, item))
        }
        (Some(CompoundType::Struct(s)), GvInitializer::Struct(fields)) => {
            !s.packed
                && fields.len() == s.fields.len()
                && s.fields
                    .iter()
                    .copied()
                    .zip(fields)
                    .all(|(field_ty, field)| initializer_all_zero(module, field_ty, field))
        }
        _ => false,
    }
}

pub(super) fn initializer_scalar_splat(
    module: &ModuleCtx,
    ty: Type,
    init: &GvInitializer,
) -> Option<Immediate> {
    let mut splat = None;
    record_initializer_splat(module, ty, init, &mut splat)?;
    splat
}

fn record_initializer_splat(
    module: &ModuleCtx,
    ty: Type,
    init: &GvInitializer,
    splat: &mut Option<Immediate>,
) -> Option<()> {
    if ty.is_integral() {
        let GvInitializer::Immediate(imm) = init else {
            return None;
        };
        if imm.ty() != ty || splat.as_ref().is_some_and(|&existing| existing != *imm) {
            return None;
        }
        *splat = Some(*imm);
        return Some(());
    }

    match (ty.resolve_compound(module)?, init) {
        (CompoundType::Array { elem, len }, GvInitializer::Array(items)) => {
            if items.len() != len {
                return None;
            }
            for item in items {
                record_initializer_splat(module, elem, item, splat)?;
            }
            Some(())
        }
        (CompoundType::Struct(s), GvInitializer::Struct(fields)) => {
            if s.packed || fields.len() != s.fields.len() {
                return None;
            }
            for (field_ty, field) in s.fields.iter().copied().zip(fields) {
                record_initializer_splat(module, field_ty, field, splat)?;
            }
            Some(())
        }
        _ => None,
    }
}

// EVM readonly const refs currently use word blobs: one 32-byte slot per scalar leaf.
// Bulk-copying into an object is only valid when the runtime object layout is exactly the
// same contiguous leaf layout, with no extra padding between recursively flattened fields.
pub(super) fn word_blob_copy_len_bytes(module: &ModuleCtx, ty: Type) -> Option<u32> {
    if ty.is_integral() {
        return (module.size_of(ty).ok()? == 32).then_some(32);
    }

    match ty.resolve_compound(module)? {
        CompoundType::Array { elem, len } => {
            let elem_size = word_blob_copy_len_bytes(module, elem)?;
            let runtime_elem_size = shape::runtime_size_bytes(module, elem)?;
            let runtime_size = shape::runtime_size_bytes(module, ty)?;
            let total_size = elem_size.checked_mul(u32::try_from(len).ok()?)?;
            (runtime_elem_size == elem_size && runtime_size == total_size).then_some(total_size)
        }
        CompoundType::Struct(s) => {
            if s.packed {
                return None;
            }

            let mut total_size = 0u32;
            for (idx, field_ty) in s.fields.iter().copied().enumerate() {
                let (field_offset, _) =
                    shape::struct_field_offset_bytes(&s.fields, s.packed, idx, module)?;
                if field_offset != total_size {
                    return None;
                }
                total_size = total_size.checked_add(word_blob_copy_len_bytes(module, field_ty)?)?;
            }

            (shape::runtime_size_bytes(module, ty)? == total_size).then_some(total_size)
        }
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Enum(_)
        | CompoundType::Func { .. } => None,
    }
}

pub(super) fn should_inline_obj_init(module: &ModuleCtx, ty: Type) -> bool {
    const MAX_INLINE_LEAVES: u32 = 4;
    const_leaf_count(module, ty).is_some_and(|leaves| leaves <= MAX_INLINE_LEAVES)
}

pub(super) const MAX_SPLIT_OBJ_INIT_ARRAY_LEN: usize = 8;

pub(super) fn should_split_obj_init(module: &ModuleCtx, ty: Type, init: &GvInitializer) -> bool {
    let Some(children) = obj_init_children(module, ty, init) else {
        return false;
    };

    let mut has_inline_child = false;
    let mut has_large_child = false;
    for (child_ty, child_init) in children {
        has_inline_child |= child_ty.is_integral() || should_inline_obj_init(module, child_ty);
        has_large_child |= !child_ty.is_integral() && !should_inline_obj_init(module, child_ty);
        if obj_init_child_avoids_blob(module, child_ty, child_init)
            || should_split_obj_init(module, child_ty, child_init)
        {
            return true;
        }
    }

    has_inline_child && has_large_child
}

fn obj_init_child_avoids_blob(module: &ModuleCtx, ty: Type, init: &GvInitializer) -> bool {
    !ty.is_integral()
        && !should_inline_obj_init(module, ty)
        && (initializer_all_zero(module, ty, init)
            || initializer_scalar_splat(module, ty, init)
                .is_some_and(|_| word_blob_copy_len_bytes(module, ty).is_some_and(|len| len > 32)))
}

fn obj_init_children<'a>(
    module: &ModuleCtx,
    ty: Type,
    init: &'a GvInitializer,
) -> Option<Vec<(Type, &'a GvInitializer)>> {
    match (ty.resolve_compound(module)?, init) {
        (CompoundType::Array { elem, len }, GvInitializer::Array(items)) => (items.len() == len
            && len <= MAX_SPLIT_OBJ_INIT_ARRAY_LEN)
            .then(|| items.iter().map(|item| (elem, item)).collect()),
        (CompoundType::Struct(s), GvInitializer::Struct(fields)) => {
            if s.packed || fields.len() != s.fields.len() {
                return None;
            }
            Some(s.fields.iter().copied().zip(fields.iter()).collect())
        }
        _ => None,
    }
}
