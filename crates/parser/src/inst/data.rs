use ir::{HasInst, builder::FunctionBuilder, inst::data::*};
use smallvec::SmallVec;

use crate::{BuildCtx, Error, ast};

super::impl_inst_build! {Mload, (addr: ValueId, ty: Type)}
super::impl_inst_build! {Mstore, (addr: ValueId, value: ValueId, ty: Type)}
super::impl_inst_build_common! {Gep, build_gep}
super::impl_inst_build! {GetFunctionPtr, (func: FuncRef)}
super::impl_inst_build_common! {SymAddr, build_sym_addr}
super::impl_inst_build_common! {SymSize, build_sym_size}
super::impl_inst_build! {Alloca, (ty: Type)}
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

fn build_sym_size(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<SymSize>,
) -> Result<SymSize, Box<Error>> {
    let sym = build_symbol_ref(ctx, fb, args)?;
    Ok(SymSize::new(has_inst, sym))
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
                expected: "function name, embed symbol, or global value".into(),
                actual: Some("value".into()),
                span: arg.span,
            })),
        },

        other => Err(Box::new(Error::InstArgKindMismatch {
            expected: "function name, embed symbol, or global value".into(),
            actual: Some(
                match other {
                    ast::InstArgKind::Value(_) => "value",
                    ast::InstArgKind::Ty(_) => "type",
                    ast::InstArgKind::Block(_) => "block",
                    ast::InstArgKind::ValueBlockMap(_) => "(value, block)",
                    ast::InstArgKind::FuncRef(_) => "function name",
                    ast::InstArgKind::EmbedSymbol(_) => "embed symbol",
                }
                .into(),
            ),
            span: arg.span,
        })),
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
