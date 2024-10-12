//! Verification context

use cranelift_entity::{PrimaryMap, SecondaryMap};
use sonatina_ir::{module::FuncRef, ControlFlowGraph, Function, Module};

use crate::{pass::PassRef, ErrorStack};

pub struct VerificationCtx {
    pub pass_ctx: PrimaryMap<PassRef, FuncRef>,
    pub func_ctx: SecondaryMap<FuncRef, FuncCtx>,
    pub module: Module,
    pub error_stack: ErrorStack,
}

impl VerificationCtx {
    pub fn new(
        pass_ctx: PrimaryMap<PassRef, FuncRef>,
        func_ctx: SecondaryMap<FuncRef, FuncCtx>,
        module: Module,
    ) -> Self {
        Self {
            pass_ctx,
            func_ctx,
            module,
            error_stack: ErrorStack::default(),
        }
    }

    pub fn func_of(&self, pass_ref: PassRef) -> FuncRef {
        self.pass_ctx[pass_ref]
    }

    pub fn func_data(&self, func_ref: FuncRef) -> &Function {
        &self.module.funcs[func_ref]
    }

    pub fn func_data_of(&self, pass_ref: PassRef) -> &Function {
        let func_ref = self.func_of(pass_ref);
        self.func_data(func_ref)
    }

    pub fn cfg(&self, func_ref: FuncRef) -> &ControlFlowGraph {
        &self.func_ctx[func_ref].0
    }
}

#[derive(Default, Clone, PartialEq, Eq)]
pub struct FuncCtx(ControlFlowGraph);

impl FuncCtx {
    pub fn new(func: &Function) -> Self {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);

        Self(cfg)
    }

    pub fn is_default(&self) -> bool {
        *self == Self::default()
    }
}
