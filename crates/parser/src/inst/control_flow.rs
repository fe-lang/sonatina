use ir::{HasInst, builder::FunctionBuilder, inst::control_flow::*};
use smallvec::SmallVec;

use crate::{BuildCtx, Error, ast, error::ArityBound};

super::impl_inst_build! {Jump, (dest: BlockId)}
super::impl_inst_build! {Br, (cond: ValueId, nz_dest: BlockId, z_dest: BlockId)}
super::impl_inst_build_common! {BrTable, ArityBound::AtLeast(1), build_br_table}
super::impl_inst_build_common! {Phi, ArityBound::AtLeast(1), build_phi}
super::impl_inst_build_common! {Call, ArityBound::AtLeast(1), build_call}
super::impl_inst_build_common! {Return, ArityBound::AtMost(1), build_return}
super::impl_inst_build! {Unreachable, ()}

fn build_br_table(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<BrTable>,
) -> Result<BrTable, Box<Error>> {
    let mut args = args.iter().peekable();
    let scrutinee = super::process_arg!(ctx, fb, args, ValueId);

    let default = (*args.peek().unwrap())
        .try_into()
        .map(|block: &ast::BlockId| {
            args.next();
            ctx.block(block)
        })
        .ok();

    let mut table = Vec::new();
    for arg in args {
        let (value, block) = arg.try_into()?;
        let value = ctx.value(fb, value);
        let block = ctx.block(block);
        table.push((value, block));
    }

    Ok(BrTable::new(has_inst, scrutinee, default, table))
}

fn build_phi(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<Phi>,
) -> Result<Phi, Box<Error>> {
    let mut ast_args = args.iter().peekable();
    let mut args = Vec::new();

    while let Some(&ast_arg) = ast_args.peek() {
        let Ok((value, block)) = ast_arg.try_into() else {
            break;
        };

        let value = ctx.value(fb, value);
        let block = ctx.block(block);
        args.push((value, block));

        ast_args.next();
    }

    if let Some(arg) = ast_args.next() {
        Err(Box::new(Error::UnexpectedTrailingInstArg(arg.span)))
    } else {
        Ok(Phi::new(has_inst, args))
    }
}

fn build_call(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<Call>,
) -> Result<Call, Box<Error>> {
    let mut ast_args = args.iter().peekable();
    let callee = super::process_arg!(ctx, fb, ast_args, FuncRef);

    let mut args = SmallVec::new();
    while let Some(&ast_arg) = ast_args.peek() {
        let Ok(value) = ast_arg.try_into() else {
            break;
        };

        let value = ctx.value(fb, value);
        args.push(value);

        ast_args.next();
    }

    if let Some(arg) = ast_args.next() {
        Err(Box::new(Error::UnexpectedTrailingInstArg(arg.span)))
    } else {
        Ok(Call::new(has_inst, callee, args))
    }
}

fn build_return(
    ctx: &mut BuildCtx,
    fb: &mut FunctionBuilder<ir::func_cursor::InstInserter>,
    args: &[ast::InstArg],
    has_inst: &dyn HasInst<Return>,
) -> Result<Return, Box<Error>> {
    let mut ast_args = args.iter().peekable();

    let arg = if ast_args.peek().is_some() {
        Some(super::process_arg!(ctx, fb, ast_args, ValueId))
    } else {
        None
    };

    if let Some(arg) = ast_args.next() {
        Err(Box::new(Error::UnexpectedTrailingInstArg(arg.span)))
    } else {
        Ok(Return::new(has_inst, arg))
    }
}
