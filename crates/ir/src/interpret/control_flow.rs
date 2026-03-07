use super::{Action, EvalValue, Interpret, State, no_result, single_result};
use crate::inst::control_flow::*;

impl Interpret for Jump {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::JumpTo(*self.dest()));
        no_result()
    }
}

impl Interpret for Br {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let Some(cond) = state.lookup_val(*self.cond()).as_imm() else {
            state.set_action(Action::FallThrough);
            return no_result();
        };

        let dest = if cond.is_zero() {
            *self.z_dest()
        } else {
            *self.nz_dest()
        };

        state.set_action(Action::JumpTo(dest));
        no_result()
    }
}

impl Interpret for BrTable {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let Some(scrutinee) = state.lookup_val(*self.scrutinee()).as_imm() else {
            state.set_action(Action::FallThrough);
            return no_result();
        };

        for (value, block) in self.table() {
            let Some(value) = state.lookup_val(*value).as_imm() else {
                continue;
            };

            if scrutinee == value {
                state.set_action(Action::JumpTo(*block));
                return no_result();
            }
        }

        if let Some(default) = self.default() {
            state.set_action(Action::JumpTo(*default))
        } else {
            state.set_action(Action::FallThrough)
        }

        no_result()
    }
}

impl Interpret for Phi {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let prev_block = state.prev_block();
        state.set_action(Action::Continue);
        for (value, block) in self.args() {
            if prev_block == *block {
                return single_result(state.lookup_val(*value));
            }
        }

        single_result(EvalValue::Undef)
    }
}

impl Interpret for Call {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let func = *self.callee();
        let args = self
            .args()
            .iter()
            .map(|arg| state.lookup_val(*arg))
            .collect();

        let val = state.call_func(func, args);
        state.set_action(Action::Continue);
        if state
            .dfg()
            .ctx
            .get_sig(func)
            .is_some_and(|sig| sig.ret_ty().is_unit())
        {
            no_result()
        } else {
            single_result(val)
        }
    }
}

impl Interpret for Return {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        let ret_val = if let Some(val) = self.arg() {
            state.lookup_val(*val)
        } else {
            EvalValue::Undef
        };

        state.set_action(Action::Return(ret_val));
        no_result()
    }
}

impl Interpret for Unreachable {
    fn interpret(&self, _state: &mut dyn State) -> super::EvalResults {
        panic!("unreachable executed")
    }
}
