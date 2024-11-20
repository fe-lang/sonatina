pub mod kind;

mod trace_info;

use std::fmt;

use cranelift_entity::entity_impl;
use kind::DisplayErrorKind;
pub use kind::ErrorKind;
use sonatina_ir::{module::FuncRef, Function};
use trace_info::DisplayTraceInfo;
pub use trace_info::{TraceInfo, TraceInfoBuilder};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ErrorRef(u32);
entity_impl!(ErrorRef, "err");

/// Verifier error.
#[derive(Debug, Clone, Copy)]
pub struct ErrorData {
    pub kind: ErrorKind,
    trace_info: TraceInfo,
}

impl ErrorData {
    pub fn new(kind: ErrorKind, trace_info: TraceInfo) -> Self {
        Self { kind, trace_info }
    }
}

/// Reportable verifier error.
pub struct Error<'a> {
    err: ErrorData,
    func: &'a Function,
    func_ref: FuncRef,
}

impl<'a> Error<'a> {
    pub fn new(err: ErrorData, func: &'a Function, func_ref: FuncRef) -> Self {
        Self {
            err,
            func,
            func_ref,
        }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ErrorData { kind, trace_info } = self.err;
        let kind = DisplayErrorKind::new(kind, self.func, self.func_ref);
        let trace_info = DisplayTraceInfo::new(&trace_info, self.func, self.func_ref);

        write!(f, "{kind}\n{trace_info}")
    }
}

#[cfg(test)]
mod test {
    use sonatina_ir::{
        builder::test_util::{test_func_builder, test_module_builder},
        inst::{arith::Add, control_flow::Return},
        isa::Isa,
        Type,
    };
    use trace_info::TraceInfoBuilder;

    use super::*;

    #[test]
    fn display_verifier_error() {
        let mut mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mut mb, &[], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();

        builder.switch_to_block(b0);
        let value0 = builder.make_imm_value(28i32);
        let value1 = builder.make_imm_value(0i8);

        let ret = builder.insert_inst_with(|| Add::new(is, value0, value1), Type::I32);
        builder.insert_inst_no_result_with(|| Return::new(is, Some(ret)));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];

        let err_msg = module.funcs.view(func_ref, |func| {
            let inst = func.layout.iter_inst(b0).next().unwrap();

            let trace_info = TraceInfoBuilder::new(func_ref)
                .block(b0)
                .inst_id(inst)
                .value(value1)
                .ty(Type::I8)
                .build();

            let err = ErrorData::new(ErrorKind::InstArgWrongType(Type::I8), trace_info);
            Error::new(err, func, func_ref).to_string()
        });

        assert_eq!(
            "argument type inconsistent with instruction, i8
trace_info:
0: i8
1: 0.i8
2: v2.i32 = add 28.i32 0.i8;
3: block0
4: func public %test_func() -> unit",
            err_msg
        );
    }
}
