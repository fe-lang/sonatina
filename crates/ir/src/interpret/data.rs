use super::{Action, EvalValue, Interpret, State};
use crate::inst::data::*;

impl Interpret for Mload {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let addr = state.lookup_val(*self.addr());
        state.set_action(Action::Continue);

        state.load(addr, *self.ty())
    }
}

impl Interpret for Mstore {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let value = state.lookup_val(*self.addr());
        let addr = state.lookup_val(*self.addr());

        state.set_action(Action::Continue);

        state.store(addr, value, *self.ty())
    }
}
