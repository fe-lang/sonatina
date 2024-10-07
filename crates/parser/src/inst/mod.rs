use ir::{builder::FunctionBuilder, func_cursor::InstInserter, inst, Inst};

use crate::{ast, BuildCtx, Error, UndefinedKind};

mod arith;
mod cast;
mod cmp;
mod control_flow;
mod data;
mod logic;

impl InstBuild for Box<dyn Inst> {
    fn build(
        ctx: &mut BuildCtx,
        fb: &mut FunctionBuilder<InstInserter>,
        ast_inst: &ast::Inst,
    ) -> Result<Box<dyn Inst>, Error> {
        let name = &ast_inst.name;
        // TODO: Refactor this huge matching.
        let inst = match name.name.as_str() {
            "add" => {
                let add = inst::arith::Add::build(ctx, fb, ast_inst)?;
                Box::new(add)
            }

            _ => {
                return Err(Error::Undefined(
                    UndefinedKind::Inst(name.name.clone()),
                    name.span,
                ))
            }
        };

        assert_eq!(inst.as_text(), ast_inst.name.name.as_str());
        Ok(inst)
    }
}

pub(super) trait InstBuild: Sized {
    fn build(
        ctx: &mut BuildCtx,
        fb: &mut FunctionBuilder<InstInserter>,
        ast_inst: &ast::Inst,
    ) -> Result<Self, Error>;
}

macro_rules! impl_inst_build {
    ($ty:ty, $has_inst:ident, ($($arg_name:ident: $arg_kind:ident ),*)) => {
        crate::inst::impl_inst_build_common!(
            $ty,
            $has_inst,
            crate::error::ArityBound::Exact(crate::inst::__count_args!($( $arg_kind ),*)),
            |ctx: &mut crate::BuildCtx,
            fb: &mut ir::builder::FunctionBuilder<ir::func_cursor::InstInserter>,
            args: &Vec<crate::ast::InstArg>,
            has_inst| {
                let mut arg_iter = args.iter();
                $(
                    let $arg_name = crate::inst::process_arg!(ctx, fb, &mut arg_iter, $arg_kind);
                )*
                Ok(<$ty>::new(has_inst, $( $arg_name ),*))
            }
        );
    };
}

macro_rules! impl_inst_build_common {
    ($ty:ty, $has_inst:ident, $expected_args:expr, $build_expr:expr) => {
        impl crate::inst::InstBuild for $ty {
            #[allow(unused)]
            fn build(
                ctx: &mut crate::BuildCtx,
                fb: &mut ir::builder::FunctionBuilder<ir::func_cursor::InstInserter>,
                ast_inst: &crate::ast::Inst,
            ) -> Result<Self, crate::Error> {
                assert_eq!(Self::inst_name(), ast_inst.name.name.as_str());

                let Some(has_inst) = fb.inst_set().$has_inst() else {
                    return Err(crate::Error::UnsupportedInst {
                        triple: fb.ctx().triple.clone(),
                        inst: ast_inst.name.name.clone(),
                        span: ast_inst.name.span,
                    });
                };

                let args = &ast_inst.args;
                let arg_num = args.len();
                $expected_args.verify_arity(arg_num, ast_inst.span)?;

                $build_expr(ctx, fb, args, has_inst)
            }
        }
    };
}

macro_rules! process_arg {
    ($ctx:ident, $fb:ident, $arg_iter:expr, ValueId) => {
        $ctx.value($fb, $arg_iter.next().unwrap().try_into()?)
    };

    ($ctx:ident, $fb:ident, $arg_iter:expr, Type) => {
        $ctx.type_(
            &mut $fb.module_builder,
            $arg_iter.next().unwrap().try_into()?,
        )
    };

    ($ctx:ident, $fb:ident, $arg_iter:expr, BlockId) => {
        $ctx.block($arg_iter.next().unwrap().try_into()?)
    };

    ($ctx:ident, $fb:ident, $arg_iter:expr, FuncRef) => {
        $ctx.func_ref(
            &mut $fb.module_builder,
            $arg_iter.next().unwrap().try_into()?,
        )
    };
}

macro_rules! __count_args {
    () => { 0 };
    ($first:tt $(, $rest:tt)*) => { 1 + crate::inst::__count_args!($($rest),*) };
}

use __count_args;
use impl_inst_build;
use impl_inst_build_common;
use process_arg;
