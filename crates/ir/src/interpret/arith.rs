use super::{EvalValue, Interpret, State};
use crate::inst::arith::*;

impl Interpret for Neg {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let val = state.lookup_val(*self.arg());
        val.with_imm(|value| -value)
    }
}

impl Interpret for Add {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs + rhs)
    }
}

impl Interpret for Sub {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| EvalValue::Imm(lhs - rhs))
    }
}

impl Interpret for Mul {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs - rhs)
    }
}

impl Interpret for Sdiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.sdiv(rhs))
    }
}

impl Interpret for Udiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.udiv(rhs))
    }
}

impl Interpret for Shl {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());

        EvalValue::zip_with_imm(bits, value, |bits, value| value << bits)
    }
}

impl Interpret for Shr {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());

        EvalValue::zip_with_imm(bits, value, |bits, value| value >> bits)
    }
}
