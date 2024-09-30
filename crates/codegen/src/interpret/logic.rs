use sonatina_ir::{inst::logic::*, Immediate};

use super::{Interpret, State};

impl Interpret for Not {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let arg = state.lookup_val(*self.arg())?;
        Some(!arg)
    }
}

impl Interpret for And {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;
        Some(lhs & rhs)
    }
}

impl Interpret for Or {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;
        Some(lhs | rhs)
    }
}

impl Interpret for Xor {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;
        Some(lhs ^ rhs)
    }
}
