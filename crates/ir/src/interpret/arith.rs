use super::{Action, EvalValue, Interpret, State};
use crate::inst::arith::*;

impl Interpret for Neg {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let val = state.lookup_val(*self.arg());
        val.with_imm(|value| -value)
    }
}

impl Interpret for Add {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs + rhs)
    }
}

impl Interpret for Sub {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| EvalValue::Imm(lhs - rhs))
    }
}

impl Interpret for Mul {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs * rhs)
    }
}

impl Interpret for Sdiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.sdiv(rhs))
    }
}

impl Interpret for Udiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.udiv(rhs))
    }
}

impl Interpret for Umod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.urem(rhs))
    }
}

impl Interpret for Smod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.srem(rhs))
    }
}

impl Interpret for Shl {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());
        EvalValue::zip_with_imm(bits, value, |bits, value| value << bits)
    }
}

impl Interpret for Shr {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());

        EvalValue::zip_with_imm(bits, value, |bits, value| value >> bits)
    }
}

impl Interpret for Sar {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let bits = state.lookup_val(*self.bits());
        let value = state.lookup_val(*self.value());

        EvalValue::zip_with_imm(bits, value, |bits, value| {
            let shifted = value >> bits;
            if value.is_positive() {
                shifted
            } else {
                -shifted
            }
        })
    }
}
