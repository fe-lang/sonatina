use super::{Action, EvalValue, Interpret, State, single_result};
use crate::inst::logic::*;

impl Interpret for Not {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let arg = state.lookup_val(*self.arg());
        state.set_action(Action::Continue);

        single_result(arg.with_imm(|arg| !arg))
    }
}

impl Interpret for And {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs & rhs))
    }
}

impl Interpret for Or {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs | rhs))
    }
}

impl Interpret for Xor {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        state.set_action(Action::Continue);

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| lhs ^ rhs))
    }
}
