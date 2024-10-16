//! Verification context

use sonatina_ir::{module::FuncRef, ControlFlowGraph, Function};

use crate::{
    error::{ErrorData, ErrorKind, TraceInfo},
    ErrorStack,
};

pub struct VerificationCtx<'a> {
    pub func_ref: FuncRef,
    pub func: &'a Function,
    pub cfg: ControlFlowGraph,
    pub error_stack: ErrorStack,
}

impl<'a> VerificationCtx<'a> {
    pub fn new(func_ref: FuncRef, func: &'a Function) -> Self {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);

        Self {
            func_ref,
            func,
            cfg,
            error_stack: ErrorStack::default(),
        }
    }

    pub fn report_nonfatal(&mut self, errs: &[ErrorData]) {
        for e in errs {
            let _err_ref = self.error_stack.push(*e);
        }
    }

    pub fn report_fatal(&mut self, kind: ErrorKind, trace_info: TraceInfo) {
        self.error_stack.fatal_error = Some(ErrorData::new(kind, trace_info));
    }
}
