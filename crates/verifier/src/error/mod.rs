mod kind;
mod stacktrace;

pub use kind::ErrorKind;
pub use stacktrace::{Stacktrace, StacktraceBuilder};

use stacktrace::DisplayStacktrace;

use std::fmt;

use sonatina_ir::{Function, Insn};

use crate::error::kind::DisplayErrorKind;

#[derive(Debug, Clone, Copy)]
pub struct Error {
    kind: ErrorKind,
    pub stacktrace: Stacktrace,
    _parent: Option<Insn>, // origin if use of insn result is root of error
}

impl Error {
    pub fn new(kind: ErrorKind, stacktrace: Stacktrace) -> Self {
        Self {
            kind,
            stacktrace,
            _parent: None,
        }
    }
}

pub struct DisplayVerifierError<'a> {
    err: Error,
    func: &'a Function,
}

impl<'a> DisplayVerifierError<'a> {
    pub fn new(err: Error, func: &'a Function) -> Self {
        Self { err, func }
    }
}

impl<'a> fmt::Display for DisplayVerifierError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { err, func } = *self;
        let Error {
            kind,
            stacktrace,
            _parent,
        } = err;
        let kind = DisplayErrorKind::new(kind, func);
        let stacktrace = DisplayStacktrace::new(&stacktrace, func);

        write!(f, "{kind}\n{stacktrace}")
    }
}

#[cfg(test)]
mod test {
    use sonatina_ir::{builder::test_util::test_func_builder, Type};
    use stacktrace::StacktraceBuilder;

    use super::*;

    #[test]
    fn display_verifier_error() {
        let mut func_builder = test_func_builder(&[], Type::Void);

        let b0 = func_builder.append_block();

        func_builder.switch_to_block(b0);
        let value0 = func_builder.make_imm_value(28i32);
        let value1 = func_builder.make_imm_value(0i8);
        let ret = func_builder.add(value0, value1);
        func_builder.ret(ret.into());

        func_builder.seal_all();

        let module = func_builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();

        let func = &module.funcs[func_ref];
        let insn = func.layout.iter_insn(b0).next().unwrap();

        let stacktrace = StacktraceBuilder::new(func_ref)
            .block(b0)
            .insn(insn)
            .value(value1)
            .ty(Type::I8)
            .build();

        let err = Error::new(ErrorKind::InsnArgWrongType(Type::I8), stacktrace);

        let err = DisplayVerifierError::new(err, func);

        assert_eq!(
            "argument type inconsistent with instruction, i8
stacktrace
0: i8
1: 0.i8
2: v2.i32 = add 28.i32 0.i8;
3: block0
4: func public %test_func() -> ()",
            err.to_string()
        );
    }
}
