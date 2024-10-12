//! Verification context

use sonatina_ir::{ControlFlowGraph, Function};

use crate::ErrorStack;

pub struct VerificationCtx<'a> {
    pub func: &'a Function,
    pub cfg: ControlFlowGraph,
    pub error_stack: ErrorStack,
}

impl<'a> VerificationCtx<'a> {
    pub fn new(func: &'a Function) -> Self {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);

        Self {
            func,
            cfg,
            error_stack: ErrorStack::default(),
        }
    }
}
