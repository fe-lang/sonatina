use crate::ir::{
    insn::{BinaryOp, UnaryOp},
    Immediate,
};

use crate::isle::prelude::*;

#[allow(clippy::all)]
mod generated_code;

pub fn simplify(dfg: &mut DataFlowGraph, insn: Insn) -> Option<SimplifyResult> {
    generated_code::constructor_simplify(&mut SimplifyContext { dfg }, insn)
}

pub enum SimplifyResult {
    Value { val: Value },
    Insn { data: InsnData },
}

struct SimplifyContext<'a> {
    dfg: &'a mut DataFlowGraph,
}

impl<'a> SimplifyContext<'a> {
    pub(crate) fn dfg(&mut self) -> &mut DataFlowGraph {
        self.dfg
    }
}

impl<'a> generated_code::Context for SimplifyContext<'a> {
    impl_prelude_ctx!();

    fn is_zero(&mut self, arg0: Value) -> bool {
        self.dfg()
            .value_imm(arg0)
            .map(|imm| imm.is_zero())
            .unwrap_or_default()
    }

    fn is_one(&mut self, arg0: Value) -> bool {
        self.dfg()
            .value_imm(arg0)
            .map(|imm| imm.is_one())
            .unwrap_or_default()
    }

    fn is_two(&mut self, arg0: Value) -> bool {
        self.dfg()
            .value_imm(arg0)
            .map(|imm| imm.is_two())
            .unwrap_or_default()
    }

    fn make_zero(&mut self, arg0: &Type) -> Value {
        let imm = Immediate::zero(arg0);
        self.dfg().make_imm_value(imm)
    }

    fn make_one(&mut self, arg0: &Type) -> Value {
        let imm = Immediate::one(arg0);
        self.dfg().make_imm_value(imm)
    }

    fn make_all_one(&mut self, arg0: &Type) -> Value {
        let imm = Immediate::all_one(arg0);
        self.dfg().make_imm_value(imm)
    }

    fn is_same(&mut self, arg0: Value, arg1: Value) -> bool {
        if arg0 == arg1 {
            return true;
        }

        match (self.dfg.value_imm(arg0), self.dfg.value_imm(arg1)) {
            (Some(imm0), Some(imm1)) => imm0 == imm1,
            _ => false,
        }
    }
}
