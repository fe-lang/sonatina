use super::{Action, EvalValue, Interpret, State};
use crate::inst::control_flow::*;

impl Interpret for Jump {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::JumpTo(*self.dest()));
        EvalValue::Undef
    }
}

impl Interpret for Br {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let Some(cond) = state.lookup_val(*self.cond()).as_imm() else {
            state.set_action(Action::FallThrough);
            return EvalValue::Undef;
        };

        let dest = if cond.is_zero() {
            *self.z_dest()
        } else {
            *self.nz_dest()
        };

        state.set_action(Action::JumpTo(dest));
        EvalValue::Undef
    }
}

impl Interpret for BrTable {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let Some(scrutinee) = state.lookup_val(*self.scrutinee()).as_imm() else {
            state.set_action(Action::FallThrough);
            return EvalValue::Undef;
        };

        for (value, block) in self.table() {
            let Some(value) = state.lookup_val(*value).as_imm() else {
                continue;
            };

            if scrutinee == value {
                state.set_action(Action::JumpTo(*block));
                return EvalValue::Undef;
            }
        }

        if let Some(default) = self.default() {
            state.set_action(Action::JumpTo(*default))
        } else {
            state.set_action(Action::FallThrough)
        }

        EvalValue::Undef
    }
}

impl Interpret for Phi {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let prev_block = state.prev_block();
        for (value, block) in self.args() {
            if prev_block == *block {
                return state.lookup_val(*value);
            }
        }

        EvalValue::Undef
    }
}

impl Interpret for Call {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let func = *self.callee();
        let args = self
            .args()
            .iter()
            .map(|arg| state.lookup_val(*arg))
            .collect();

        state.eval_func(func, args)
    }
}

impl Interpret for Return {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let ret_val = if let Some(val) = self.arg() {
            state.lookup_val(*val)
        } else {
            EvalValue::Undef
        };

        state.set_action(Action::Return(ret_val));
        EvalValue::Undef
    }
}
