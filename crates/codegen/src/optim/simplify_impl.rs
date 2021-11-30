use crate::ir::{
    insn::{BinaryOp, UnaryOp},
    Immediate,
};

use crate::isle::prelude::*;

#[allow(clippy::all)]
mod generated_code;

pub fn simplify(dfg: &mut DataFlowGraph, insn: Insn) -> Option<SimplifyResult> {
    if let Some(res) = generated_code::constructor_simplify(&mut SimplifyContext { dfg }, insn) {
        Some(res)
    } else {
        let insn = try_swap_arg(dfg, insn)?;
        generated_code::constructor_simplify(&mut SimplifyContext { dfg }, insn)
    }
}

pub enum SimplifyResult {
    Value { val: Value },
    Insn { data: InsnData },
}

fn try_swap_arg(dfg: &mut DataFlowGraph, insn: Insn) -> Option<Insn> {
    match *dfg.insn_data(insn) {
        InsnData::Binary {
            code,
            args: [lhs, rhs],
        } => {
            if code.is_commutative() {
                let data = InsnData::Binary {
                    code,
                    args: [rhs, lhs],
                };
                Some(dfg.make_insn(data))
            } else {
                None
            }
        }
        _ => None,
    }
}

impl BinaryOp {
    fn is_commutative(self) -> bool {
        use BinaryOp::*;

        matches!(self, Add | Mul | And | Or | Xor)
    }
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

    fn is_all_one(&mut self, arg0: Value) -> bool {
        self.dfg()
            .value_imm(arg0)
            .map(|imm| imm.is_all_one())
            .unwrap_or_default()
    }

    fn is_same(&mut self, arg0: Value, arg1: Value) -> bool {
        self.dfg().is_same_value(arg0, arg1)
    }

    fn is_two(&mut self, arg0: Value) -> bool {
        self.dfg()
            .value_imm(arg0)
            .map(|imm| imm.is_two())
            .unwrap_or_default()
    }

    fn is_power_of_two(&mut self, arg0: Value) -> bool {
        self.dfg()
            .value_imm(arg0)
            .map(|imm| imm.is_power_of_two())
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
}
