//! Enums laid out as `NativeTypeLayout` places them: the tag at offset zero
//! and every variant's fields from one shared payload offset.

use cranelift_codegen::{
    ir::{self as clif, InstBuilder, MemFlagsData},
    isa::TargetFrontendConfig,
};
use cranelift_frontend::FunctionBuilder;
use sonatina_ir::{Function, Type, ValueId, module::ModuleCtx, types::EnumVariantRef};

use super::{
    abi::{sonatina_scalar_type_to_clif_or_err, uses_indirect_value_representation},
    memory::{store_indirect, store_value, value_storage_size},
    values::ValueMap,
};

/// The offset and type of field `field` of `variant`.
pub(super) fn variant_field_offset(
    ctx: &ModuleCtx,
    variant: EnumVariantRef,
    field: usize,
) -> Result<(i32, Type), String> {
    let enum_ty = Type::Compound(variant.enum_ty());
    let (offset, ty) = ctx
        .enum_variant_field_offset(enum_ty, variant.index() as usize, field)
        .ok_or_else(|| format!("cannot lay out field {field} of {variant:?}"))?;
    let offset =
        i32::try_from(offset).map_err(|_| format!("enum field offset {offset} overflows i32"))?;
    Ok((offset, ty))
}

/// The tag integer type of `variant`'s enum.
pub(super) fn tag_clif_type(
    ctx: &ModuleCtx,
    variant: EnumVariantRef,
) -> Result<clif::Type, String> {
    let tag_ty = ctx
        .with_ty_store(|store| store.enum_data(variant.enum_ty()).map(|data| data.tag_ty()))
        .ok_or_else(|| format!("{variant:?} names no enum"))?;
    sonatina_scalar_type_to_clif_or_err(tag_ty)
}

/// Stores `variant`'s tag in the enum at `dst`.
pub(super) fn store_tag(
    ctx: &ModuleCtx,
    variant: EnumVariantRef,
    dst: clif::Value,
    builder: &mut FunctionBuilder,
) -> Result<(), String> {
    let tag = builder
        .ins()
        .iconst(tag_clif_type(ctx, variant)?, i64::from(variant.index()));
    builder.ins().store(MemFlagsData::new(), tag, dst, 0);
    Ok(())
}

/// Writes `variant`'s tag and the fields `values` to the enum at `dst`, and
/// returns the byte ranges written: the tag's, then each field's.
pub(super) fn store_variant(
    function: &Function,
    variant: EnumVariantRef,
    values: &[ValueId],
    dst: clif::Value,
    value_map: &ValueMap,
    config: TargetFrontendConfig,
    builder: &mut FunctionBuilder,
) -> Result<Vec<(u32, u32)>, String> {
    let ctx = function.ctx();
    let mut written = vec![(0, tag_clif_type(ctx, variant)?.bytes())];
    for (field, &value) in values.iter().enumerate() {
        let (offset, ty) = variant_field_offset(ctx, variant, field)?;
        let size = value_storage_size(ty, ctx)?;
        if uses_indirect_value_representation(ctx, ty) {
            let field_dst = builder.ins().iadd_imm_s(dst, i64::from(offset));
            store_indirect(function, value, field_dst, size, value_map, config, builder)?;
        } else {
            store_value(function, value, dst, offset, value_map, builder)?;
        }
        written.push((offset as u32, size));
    }
    store_tag(ctx, variant, dst, builder)?;
    Ok(written)
}
