use super::{Action, EvalValue, Interpret, State};
use crate::inst::evm::*;

impl Interpret for EvmUdiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(
            lhs,
            rhs,
            |lhs, rhs| {
                if rhs.is_zero() { rhs } else { lhs.udiv(rhs) }
            },
        )
    }
}

impl Interpret for EvmSdiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(
            lhs,
            rhs,
            |lhs, rhs| {
                if rhs.is_zero() { rhs } else { lhs.sdiv(rhs) }
            },
        )
    }
}

impl Interpret for EvmUmod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(
            lhs,
            rhs,
            |lhs, rhs| {
                if rhs.is_zero() { rhs } else { lhs.urem(rhs) }
            },
        )
    }
}

impl Interpret for EvmSmod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(
            lhs,
            rhs,
            |lhs, rhs| {
                if rhs.is_zero() { rhs } else { lhs.srem(rhs) }
            },
        )
    }
}

impl Interpret for EvmAddMod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                rhs
            } else {
                (lhs + rhs).urem(rhs)
            }
        })
    }
}

impl Interpret for EvmMulMod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);
        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() {
                rhs
            } else {
                (lhs * rhs).urem(rhs)
            }
        })
    }
}
