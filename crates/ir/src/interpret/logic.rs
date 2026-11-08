use super::{Action, EvalValue, Interpret, State, single_result};
use crate::{Immediate, inst::logic::*};

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

impl Interpret for Bswap {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let arg = state.lookup_val(*self.arg());
        state.set_action(Action::Continue);

        single_result(arg.with_imm(Immediate::bswap))
    }
}

impl Interpret for Clz {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let arg = state.lookup_val(*self.arg());
        state.set_action(Action::Continue);

        single_result(arg.with_imm(Immediate::clz))
    }
}

impl Interpret for Ctz {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let arg = state.lookup_val(*self.arg());
        state.set_action(Action::Continue);

        single_result(arg.with_imm(Immediate::ctz))
    }
}

impl Interpret for Select {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let cond = state.lookup_val(*self.cond());
        state.set_action(Action::Continue);
        let Some(cond) = cond.as_imm() else {
            return single_result(EvalValue::Undef);
        };
        let chosen = if cond.is_zero() {
            *self.else_value()
        } else {
            *self.then_value()
        };
        single_result(state.lookup_val(chosen))
    }
}
