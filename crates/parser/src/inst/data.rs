use ir::{builder::FunctionBuilder, inst::data::*, HasInst};
use smallvec::SmallVec;

use crate::{ast, error::ArityBound, BuildCtx, Error};

super::impl_inst_build! {Mload, (addr: ValueId, ty: Type)}
super::impl_inst_build! {Mstore, (addr: ValueId, value: ValueId, ty: Type)}
super::impl_inst_build_common! {Gep, ArityBound::AtLeast(2), build_gep}
super::impl_inst_build! {Alloca, (ty: Type)}

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
