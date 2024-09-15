mod kind;
mod trace_info;

pub use kind::ErrorKind;
pub use trace_info::{TraceInfo, TraceInfoBuilder};

use trace_info::DisplayTraceInfo;

use std::{error, fmt};

use sonatina_ir::Function;

use crate::error::kind::DisplayErrorKind;

/// Verifier error.
#[derive(Debug, Clone, Copy)]
pub struct ErrorData {
    kind: ErrorKind,
    trace_info: TraceInfo,
}

impl ErrorData {
    pub fn new(kind: ErrorKind, trace_info: TraceInfo) -> Self {
        Self { kind, trace_info }
    }
}

/// Reportable verifier error.
#[derive(Debug)]
pub struct Error<'a> {
    err: ErrorData,
    func: &'a Function,
}

impl<'a> Error<'a> {
    pub fn new(err: ErrorData, func: &'a Function) -> Self {
        Self { err, func }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { err, func } = *self;
        let ErrorData { kind, trace_info } = err;
        let kind = DisplayErrorKind::new(kind, func);
        let trace_info = DisplayTraceInfo::new(&trace_info, func);

        write!(f, "{kind}\n{trace_info}")
    }
}

impl<'a> error::Error for Error<'a> {}

#[cfg(test)]
mod test {
    use sonatina_ir::{builder::test_util::test_func_builder, Type};
    use trace_info::TraceInfoBuilder;

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

        let trace_info = TraceInfoBuilder::new(func_ref)
            .block(b0)
            .insn(insn)
            .value(value1)
            .ty(Type::I8)
            .build();

        let err = ErrorData::new(ErrorKind::InsnArgWrongType(Type::I8), trace_info);

        let err = Error::new(err, func);

        assert_eq!(
            "argument type inconsistent with instruction, i8
trace_info:
0: i8
1: 0.i8
2: v2.i32 = add 28.i32 0.i8;
3: block0
4: func public %test_func() -> ()",
            err.to_string()
        );
    }
}
