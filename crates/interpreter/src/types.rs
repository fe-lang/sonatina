use std::mem;

use sonatina_ir::{
    module::ModuleCtx,
    types::{CompoundType, CompoundTypeData},
    Type, I256,
};

pub fn size_of_ty_data(ctx: &ModuleCtx, ty: Type) -> usize {
    match ty {
        Type::I1 => mem::size_of::<bool>(),
        Type::I8 => mem::size_of::<i8>(),
        Type::I16 => mem::size_of::<i16>(),
        Type::I32 => mem::size_of::<i32>(),
        Type::I64 => mem::size_of::<i64>(),
        Type::I128 => mem::size_of::<i128>(),
        Type::I256 => 32,
        Type::Compound(cmpd_ty) => {
            use CompoundTypeData::*;
            let cmpd_ty_data = ctx.with_ty_store(|s| s.resolve_compound(cmpd_ty).clone());
            match cmpd_ty_data {
                Array { len, elem } => len * size_of_ty_data(ctx, elem),
                Ptr(_) => mem::size_of::<usize>(),
                Struct(data) => data.fields.iter().fold(0usize, |acc, field_ty| {
                    acc + size_of_ty_data(ctx, *field_ty)
                }),
            }
        }
        Type::Void => mem::size_of::<()>(),
    }
}

fn to_cmpd_ty(ty: Type) -> Option<CompoundType> {
    match ty {
        Type::Compound(ty) => Some(ty),
        _ => None,
    }
}

pub fn gep(
    ctx: &ModuleCtx,
    base_addr: I256,
    ptr_ty: Type,
    args: impl Iterator<Item = I256>,
) -> I256 {
    let pointee_ty = ctx.with_ty_store(|s| s.deref(ptr_ty)).unwrap();
    debug_assert!(!pointee_ty.is_integral() && !ctx.with_ty_store(|s| s.is_ptr(pointee_ty)));
    let mut cmpd_ty = to_cmpd_ty(pointee_ty);

    let mut offset = 0usize;

    for arg in args {
        let index = arg.to_u256().as_usize();
        let cmpd_ty_data = ctx.with_ty_store(|s| s.resolve_compound(cmpd_ty.unwrap()).clone());
        match cmpd_ty_data {
            CompoundTypeData::Array { elem, .. } => {
                offset += index * size_of_ty_data(ctx, elem);
                cmpd_ty = to_cmpd_ty(elem);
            }
            CompoundTypeData::Struct(data) => {
                for ty in &data.fields[..index] {
                    offset += size_of_ty_data(ctx, *ty);
                }
                cmpd_ty = to_cmpd_ty(data.fields[index]);
            }
            _ => unreachable!(),
        }
    }
    (base_addr.to_u256().as_usize() + offset).into()
}
