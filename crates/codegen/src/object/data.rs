use sonatina_ir::{
    GlobalVariableRef, I256, Immediate, Type, global_variable::GvInitializer, module::ModuleCtx,
    types::CompoundType,
};

#[derive(Debug, Clone)]
pub enum DataEncodingError {
    NotConst,
    MissingInitializer,
    UnsupportedType(Type),
    ShapeMismatch,
}

pub fn encode_gv_initializer_to_bytes(
    ctx: &ModuleCtx,
    gv: GlobalVariableRef,
) -> Result<Vec<u8>, DataEncodingError> {
    let gv_data = ctx.with_gv_store(|s| s.gv_data(gv).clone());

    if !gv_data.is_const {
        return Err(DataEncodingError::NotConst);
    }
    let Some(init) = gv_data.initializer.clone() else {
        return Err(DataEncodingError::MissingInitializer);
    };

    let bytes = encode_initializer(ctx, gv_data.ty, &init)?;
    let expected_size = encoded_size(ctx, gv_data.ty)?;
    if bytes.len() != expected_size {
        return Err(DataEncodingError::ShapeMismatch);
    }

    Ok(bytes)
}

fn encode_initializer(
    ctx: &ModuleCtx,
    ty: Type,
    init: &GvInitializer,
) -> Result<Vec<u8>, DataEncodingError> {
    if ty.is_pointer(ctx) {
        return Err(DataEncodingError::UnsupportedType(ty));
    }

    if ty.is_integral() {
        let GvInitializer::Immediate(imm) = init else {
            return Err(DataEncodingError::ShapeMismatch);
        };

        return encode_int(ty, *imm);
    }

    match ty.resolve_compound(ctx) {
        Some(CompoundType::Array { elem, len }) => {
            let GvInitializer::Array(elems) = init else {
                return Err(DataEncodingError::ShapeMismatch);
            };
            if elems.len() != len {
                return Err(DataEncodingError::ShapeMismatch);
            }

            let mut bytes = Vec::new();
            for elem_init in elems {
                bytes.extend(encode_initializer(ctx, elem, elem_init)?);
            }
            Ok(bytes)
        }

        Some(CompoundType::Struct(s)) => {
            if s.packed {
                return Err(DataEncodingError::UnsupportedType(ty));
            }
            let GvInitializer::Struct(fields) = init else {
                return Err(DataEncodingError::ShapeMismatch);
            };
            if fields.len() != s.fields.len() {
                return Err(DataEncodingError::ShapeMismatch);
            }

            let mut bytes = Vec::new();
            for (field_ty, field_init) in s.fields.into_iter().zip(fields) {
                bytes.extend(encode_initializer(ctx, field_ty, field_init)?);
            }
            Ok(bytes)
        }

        Some(CompoundType::Ptr(_)) => Err(DataEncodingError::UnsupportedType(ty)),
        Some(CompoundType::Func { .. }) => Err(DataEncodingError::UnsupportedType(ty)),
        None => Err(DataEncodingError::UnsupportedType(ty)),
    }
}

fn encode_int(ty: Type, imm: Immediate) -> Result<Vec<u8>, DataEncodingError> {
    let size = scalar_byte_width(ty).ok_or(DataEncodingError::UnsupportedType(ty))?;
    let bytes = encode_i256_be(imm.as_i256(), size);
    Ok(bytes)
}

fn encode_i256_be(val: I256, width: usize) -> Vec<u8> {
    debug_assert!(width <= 32);
    let tmp = val.to_u256().to_big_endian();
    tmp[32 - width..].to_vec()
}

fn encoded_size(ctx: &ModuleCtx, ty: Type) -> Result<usize, DataEncodingError> {
    if ty.is_pointer(ctx) {
        return Err(DataEncodingError::UnsupportedType(ty));
    }

    if let Some(width) = scalar_byte_width(ty) {
        return Ok(width);
    }

    match ty.resolve_compound(ctx) {
        Some(CompoundType::Array { elem, len }) => Ok(encoded_size(ctx, elem)? * len),

        Some(CompoundType::Struct(s)) => {
            if s.packed {
                return Err(DataEncodingError::UnsupportedType(ty));
            }
            let mut size = 0usize;
            for &field in &s.fields {
                size = size
                    .checked_add(encoded_size(ctx, field)?)
                    .ok_or(DataEncodingError::ShapeMismatch)?;
            }
            Ok(size)
        }

        Some(CompoundType::Ptr(_)) => Err(DataEncodingError::UnsupportedType(ty)),
        Some(CompoundType::Func { .. }) => Err(DataEncodingError::UnsupportedType(ty)),
        None => Err(DataEncodingError::UnsupportedType(ty)),
    }
}

fn scalar_byte_width(ty: Type) -> Option<usize> {
    Some(match ty {
        Type::I1 | Type::I8 => 1,
        Type::I16 => 2,
        Type::I32 => 4,
        Type::I64 => 8,
        Type::I128 => 16,
        Type::I256 => 32,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        Linkage,
        builder::test_util::test_isa,
        global_variable::{GlobalVariableData, GvInitializer},
        module::ModuleCtx,
    };

    #[test]
    fn encode_i32_big_endian() {
        let ctx = ModuleCtx::new(&test_isa());
        let gv = ctx.with_gv_store_mut(|s| {
            s.make_gv(GlobalVariableData::constant(
                "x".to_string(),
                Type::I32,
                Linkage::Public,
                GvInitializer::make_imm(0x01020304_i32),
            ))
        });

        let bytes = encode_gv_initializer_to_bytes(&ctx, gv).unwrap();
        assert_eq!(bytes, vec![0x01, 0x02, 0x03, 0x04]);
    }

    #[test]
    fn encode_array_concatenation() {
        let ctx = ModuleCtx::new(&test_isa());
        let array_ty = ctx.with_ty_store_mut(|s| s.make_array(Type::I8, 4));
        let gv = ctx.with_gv_store_mut(|s| {
            s.make_gv(GlobalVariableData::constant(
                "arr".to_string(),
                array_ty,
                Linkage::Public,
                GvInitializer::make_array(vec![
                    GvInitializer::make_imm(1i8),
                    GvInitializer::make_imm(2i8),
                    GvInitializer::make_imm(3i8),
                    GvInitializer::make_imm(4i8),
                ]),
            ))
        });

        let bytes = encode_gv_initializer_to_bytes(&ctx, gv).unwrap();
        assert_eq!(bytes, vec![1, 2, 3, 4]);
    }

    #[test]
    fn encode_struct_concatenation() {
        let ctx = ModuleCtx::new(&test_isa());
        let struct_ty =
            ctx.with_ty_store_mut(|s| s.make_struct("S", &[Type::I8, Type::I16], false));
        let gv = ctx.with_gv_store_mut(|s| {
            s.make_gv(GlobalVariableData::constant(
                "s".to_string(),
                struct_ty,
                Linkage::Public,
                GvInitializer::make_struct(vec![
                    GvInitializer::make_imm(0x11i8),
                    GvInitializer::make_imm(0x2233i16),
                ]),
            ))
        });

        let bytes = encode_gv_initializer_to_bytes(&ctx, gv).unwrap();
        assert_eq!(bytes, vec![0x11, 0x22, 0x33]);
    }

    #[test]
    fn reject_pointer_types() {
        let ctx = ModuleCtx::new(&test_isa());
        let ptr_ty = ctx.with_ty_store_mut(|s| s.make_ptr(Type::I8));
        let gv = ctx.with_gv_store_mut(|s| {
            s.make_gv(GlobalVariableData::constant(
                "p".to_string(),
                ptr_ty,
                Linkage::Public,
                GvInitializer::make_imm(I256::zero()),
            ))
        });

        let err = encode_gv_initializer_to_bytes(&ctx, gv).unwrap_err();
        assert!(matches!(err, DataEncodingError::UnsupportedType(_)));
    }
}
