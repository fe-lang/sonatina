use ir::{HasInst, ValueId, builder::FunctionBuilder, inst::data::*};
use smallvec::SmallVec;

use crate::{BuildCtx, Error, ast};

super::impl_inst_build! {Mload, (addr: ValueId, ty: Type)}
super::impl_inst_build! {Mstore, (addr: ValueId, value: ValueId, ty: Type)}
super::impl_inst_build_common! {Gep, build_gep}
super::impl_inst_build! {GetFunctionPtr, (func: FuncRef)}
super::impl_inst_build_common! {SymAddr, build_sym_addr}
super::impl_inst_build_common! {SymSize, build_sym_size}
super::impl_inst_build! {Alloca, (ty: Type)}
super::impl_inst_build! {ObjAlloc, (ty: Type)}
super::impl_inst_build_common! {ConstRef, build_const_ref}
super::impl_inst_build_common! {ConstProj, build_const_proj}
super::impl_inst_build! {ConstIndex, (object: ValueId, index: ValueId)}
super::impl_inst_build! {ConstLoad, (object: ValueId)}
super::impl_inst_build_common! {ObjProj, build_obj_proj}
super::impl_inst_build! {ObjIndex, (object: ValueId, index: ValueId)}
super::impl_inst_build! {ObjLoad, (object: ValueId)}
super::impl_inst_build! {ObjStore, (object: ValueId, value: ValueId)}
super::impl_inst_build! {ObjInitConst, (object: ValueId, value: ValueId)}
super::impl_inst_build_common! {EnumMake, build_enum_make}
super::impl_inst_build! {EnumTag, (value: ValueId)}
super::impl_inst_build_common! {EnumIsVariant, build_enum_is_variant}
super::impl_inst_build_common! {EnumAssertVariant, build_enum_assert_variant}
super::impl_inst_build_common! {EnumAssertVariantRef, build_enum_assert_variant_ref}
super::impl_inst_build_common! {EnumExtract, build_enum_extract}
super::impl_inst_build_common! {EnumSetTag, build_enum_set_tag}
super::impl_inst_build_common! {EnumWriteVariant, build_enum_write_variant}
super::impl_inst_build! {EnumGetTag, (object: ValueId)}
super::impl_inst_build_common! {EnumProj, build_enum_proj}
super::impl_inst_build! {ObjMaterializeStack, (object: ValueId)}
super::impl_inst_build! {ObjMaterializeHeap, (object: ValueId)}
super::impl_inst_build! {MemAllocDynamic, (size: ValueId)}
super::impl_inst_build! {InsertValue, (dest: ValueId, idx: ValueId, value: ValueId)}
super::impl_inst_build! {ExtractValue, (dest: ValueId, idx: ValueId)}

fn build_sym_addr(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<SymAddr>,
) -> Result<SymAddr, Box<Error>> {
    let sym = build_symbol_ref(ctx, fb, args)?;
    Ok(SymAddr::new(has_inst, sym))
}

fn build_const_ref(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<ConstRef>,
) -> Result<ConstRef, Box<Error>> {
    let global = build_global_ref(ctx, fb, args)?;
    Ok(ConstRef::new(has_inst, global.into()))
}

fn build_sym_size(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<SymSize>,
) -> Result<SymSize, Box<Error>> {
    let sym = build_symbol_ref(ctx, fb, args)?;
    Ok(SymSize::new(has_inst, sym))
}

fn build_global_ref(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
) -> Result<ir::GlobalVariableRef, Box<Error>> {
    let arg = &args[0];
    let ast::InstArgKind::Value(value) = &arg.kind else {
        return Err(Box::new(Error::InstArgKindMismatch {
            expected: "global value".into(),
            actual: Some(
                match &arg.kind {
                    ast::InstArgKind::Value(_) => "value",
                    ast::InstArgKind::MultiValue(_) => "(value, ...)",
                    ast::InstArgKind::Ty(_) => "type",
                    ast::InstArgKind::Variant(_) => "variant name",
                    ast::InstArgKind::Block(_) => "block",
                    ast::InstArgKind::ValueBlockMap(_) => "(value, block)",
                    ast::InstArgKind::FuncRef(_) => "function name",
                    ast::InstArgKind::EmbedSymbol(_) => "embed symbol",
                    ast::InstArgKind::CurrentSection => "current section symbol",
                }
                .into(),
            ),
            span: arg.span,
        }));
    };
    let ast::ValueKind::Global(name) = &value.kind else {
        return Err(Box::new(Error::InstArgKindMismatch {
            expected: "global value".into(),
            actual: Some("value".into()),
            span: arg.span,
        }));
    };
    let Some(gv) = fb.module_builder.lookup_gv(&name.string) else {
        ctx.errors.push(Error::Undefined(
            crate::UndefinedKind::Value(name.string.clone()),
            value.span,
        ));
        return Ok(ir::GlobalVariableRef::from_u32(0));
    };
    Ok(gv)
}

fn build_symbol_ref(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
) -> Result<SymbolRef, Box<Error>> {
    let arg = &args[0];

    match &arg.kind {
        ast::InstArgKind::FuncRef(func) => {
            Ok(SymbolRef::Func(ctx.func_ref(&mut fb.module_builder, func)))
        }

        ast::InstArgKind::EmbedSymbol(sym) => Ok(SymbolRef::Embed(sym.clone())),
        ast::InstArgKind::CurrentSection => Ok(SymbolRef::CurrentSection),

        ast::InstArgKind::Value(value) => match &value.kind {
            ast::ValueKind::Global(name) => {
                let Some(gv) = fb.module_builder.lookup_gv(&name.string) else {
                    ctx.errors.push(Error::Undefined(
                        crate::UndefinedKind::Value(name.string.clone()),
                        value.span,
                    ));
                    return Ok(SymbolRef::Global(ir::GlobalVariableRef::from_u32(0)));
                };
                Ok(SymbolRef::Global(gv))
            }

            _ => Err(Box::new(Error::InstArgKindMismatch {
                expected: "function name, embed symbol, current section symbol, or global value"
                    .into(),
                actual: Some("value".into()),
                span: arg.span,
            })),
        },

        other => Err(Box::new(Error::InstArgKindMismatch {
            expected: "function name, embed symbol, current section symbol, or global value".into(),
            actual: Some(
                match other {
                    ast::InstArgKind::Value(_) => "value",
                    ast::InstArgKind::MultiValue(_) => "(value, ...)",
                    ast::InstArgKind::Ty(_) => "type",
                    ast::InstArgKind::Variant(_) => "variant name",
                    ast::InstArgKind::Block(_) => "block",
                    ast::InstArgKind::ValueBlockMap(_) => "(value, block)",
                    ast::InstArgKind::FuncRef(_) => "function name",
                    ast::InstArgKind::EmbedSymbol(_) => "embed symbol",
                    ast::InstArgKind::CurrentSection => "current section symbol",
                }
                .into(),
            ),
            span: arg.span,
        })),
    }
}

fn build_const_proj(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<ConstProj>,
) -> Result<ConstProj, Box<Error>> {
    let mut values = SmallVec::new();
    let mut ast_args = args.iter().peekable();
    while ast_args.peek().is_some() {
        values.push(super::process_arg!(ctx, fb, ast_args, ValueId));
    }

    if let Some(arg) = ast_args.next() {
        Err(Box::new(Error::UnexpectedTrailingInstArg(arg.span)))
    } else {
        Ok(ConstProj::new(has_inst, values))
    }
}

fn build_gep(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<Gep>,
) -> Result<Gep, Box<Error>> {
    let mut values = SmallVec::new();
    let mut ast_args = args.iter().peekable();
    while ast_args.peek().is_some() {
        values.push(super::process_arg!(ctx, fb, ast_args, ValueId));
    }

    if let Some(arg) = ast_args.next() {
        Err(Box::new(Error::UnexpectedTrailingInstArg(arg.span)))
    } else {
        Ok(Gep::new(has_inst, values))
    }
}

fn build_obj_proj(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<ObjProj>,
) -> Result<ObjProj, Box<Error>> {
    let mut values = SmallVec::new();
    let mut ast_args = args.iter().peekable();
    while ast_args.peek().is_some() {
        values.push(super::process_arg!(ctx, fb, ast_args, ValueId));
    }

    if let Some(arg) = ast_args.next() {
        Err(Box::new(Error::UnexpectedTrailingInstArg(arg.span)))
    } else {
        Ok(ObjProj::new(has_inst, values))
    }
}

fn build_enum_make(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<EnumMake>,
) -> Result<EnumMake, Box<Error>> {
    let enum_ty = ctx.type_(&fb.module_builder, (&args[0]).try_into()?);
    let variant_name: &ast::VariantName = (&args[1]).try_into()?;
    let variant = ctx.enum_variant(&fb.module_builder, enum_ty, variant_name, args[1].span);
    let values = build_enum_payload_values(ctx, fb, &args[2..])?;
    Ok(EnumMake::new(has_inst, enum_ty, variant, values))
}

fn build_enum_is_variant(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<EnumIsVariant>,
) -> Result<EnumIsVariant, Box<Error>> {
    let value = ctx.value(fb, (&args[0]).try_into()?);
    let variant_name: &ast::VariantName = (&args[1]).try_into()?;
    let enum_ty = fb.func.dfg.value_ty(value);
    let variant = ctx.enum_variant(&fb.module_builder, enum_ty, variant_name, args[1].span);
    Ok(EnumIsVariant::new(has_inst, value, variant))
}

fn build_enum_assert_variant(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<EnumAssertVariant>,
) -> Result<EnumAssertVariant, Box<Error>> {
    let value = ctx.value(fb, (&args[0]).try_into()?);
    let variant_name: &ast::VariantName = (&args[1]).try_into()?;
    let enum_ty = fb.func.dfg.value_ty(value);
    let variant = ctx.enum_variant(&fb.module_builder, enum_ty, variant_name, args[1].span);
    Ok(EnumAssertVariant::new(has_inst, value, variant))
}

fn build_enum_extract(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<EnumExtract>,
) -> Result<EnumExtract, Box<Error>> {
    let value = ctx.value(fb, (&args[0]).try_into()?);
    let variant_name: &ast::VariantName = (&args[1]).try_into()?;
    let field = ctx.value(fb, (&args[2]).try_into()?);
    let enum_ty = fb.func.dfg.value_ty(value);
    let variant = ctx.enum_variant(&fb.module_builder, enum_ty, variant_name, args[1].span);
    Ok(EnumExtract::new(has_inst, value, variant, field))
}

fn build_enum_assert_variant_ref(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<EnumAssertVariantRef>,
) -> Result<EnumAssertVariantRef, Box<Error>> {
    let object = ctx.value(fb, (&args[0]).try_into()?);
    let variant_name: &ast::VariantName = (&args[1]).try_into()?;
    let enum_ty = fb
        .func
        .dfg
        .value_ty(object)
        .resolve_compound(fb.func.ctx())
        .and_then(|cmpd| match cmpd {
            ir::types::CompoundType::ObjRef(elem) => Some(elem),
            _ => None,
        })
        .unwrap_or(ir::Type::Unit);
    let variant = ctx.enum_variant(&fb.module_builder, enum_ty, variant_name, args[1].span);
    Ok(EnumAssertVariantRef::new(has_inst, object, variant))
}

fn build_enum_set_tag(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<EnumSetTag>,
) -> Result<EnumSetTag, Box<Error>> {
    let object = ctx.value(fb, (&args[0]).try_into()?);
    let variant_name: &ast::VariantName = (&args[1]).try_into()?;
    let enum_ty = fb
        .func
        .dfg
        .value_ty(object)
        .resolve_compound(fb.func.ctx())
        .and_then(|cmpd| match cmpd {
            ir::types::CompoundType::ObjRef(elem) => Some(elem),
            _ => None,
        })
        .unwrap_or(ir::Type::Unit);
    let variant = ctx.enum_variant(&fb.module_builder, enum_ty, variant_name, args[1].span);
    Ok(EnumSetTag::new(has_inst, object, variant))
}

fn build_enum_write_variant(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<EnumWriteVariant>,
) -> Result<EnumWriteVariant, Box<Error>> {
    let object = ctx.value(fb, (&args[0]).try_into()?);
    let variant_name: &ast::VariantName = (&args[1]).try_into()?;
    let enum_ty = fb
        .func
        .dfg
        .value_ty(object)
        .resolve_compound(fb.func.ctx())
        .and_then(|cmpd| match cmpd {
            ir::types::CompoundType::ObjRef(elem) => Some(elem),
            _ => None,
        })
        .unwrap_or(ir::Type::Unit);
    let variant = ctx.enum_variant(&fb.module_builder, enum_ty, variant_name, args[1].span);
    let values = build_enum_payload_values(ctx, fb, &args[2..])?;
    Ok(EnumWriteVariant::new(has_inst, object, variant, values))
}

fn build_enum_proj(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<EnumProj>,
) -> Result<EnumProj, Box<Error>> {
    let object = ctx.value(fb, (&args[0]).try_into()?);
    let variant_name: &ast::VariantName = (&args[1]).try_into()?;
    let field = ctx.value(fb, (&args[2]).try_into()?);
    let enum_ty = fb
        .func
        .dfg
        .value_ty(object)
        .resolve_compound(fb.func.ctx())
        .and_then(|cmpd| match cmpd {
            ir::types::CompoundType::ObjRef(elem) => Some(elem),
            _ => None,
        })
        .unwrap_or(ir::Type::Unit);
    let variant = ctx.enum_variant(&fb.module_builder, enum_ty, variant_name, args[1].span);
    Ok(EnumProj::new(has_inst, object, variant, field))
}

fn build_enum_payload_values(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
) -> Result<SmallVec<[ValueId; 2]>, Box<Error>> {
    if let [arg] = args
        && let ast::InstArgKind::MultiValue(values) = &arg.kind
    {
        return Ok(values.iter().map(|value| ctx.value(fb, value)).collect());
    }

    args.iter()
        .map(|arg| Ok(ctx.value(fb, arg.try_into()?)))
        .collect()
}
