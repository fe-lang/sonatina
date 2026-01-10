use super::{Action, EvalValue, Interpret, State};
use crate::{Immediate, inst::cmp::*};

impl Interpret for Lt {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.lt(rhs))
    }
}

impl Interpret for Gt {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.gt(rhs))
    }
}

impl Interpret for Slt {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.slt(rhs))
    }
}

impl Interpret for Sgt {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.sgt(rhs))
    }
}

impl Interpret for Le {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.le(rhs))
    }
}

impl Interpret for Ge {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.ge(rhs))
    }
}

impl Interpret for Sle {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.sle(rhs))
    }
}

impl Interpret for Sge {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.sge(rhs))
    }
}

impl Interpret for Eq {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.imm_eq(rhs))
    }
}

impl Interpret for Ne {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs.imm_ne(rhs))
    }
}

impl Interpret for IsZero {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let val = state.lookup_val(*self.lhs());
        state.set_action(Action::Continue);

        val.with_imm(|value| Immediate::from(value.is_zero()))
    }
}
