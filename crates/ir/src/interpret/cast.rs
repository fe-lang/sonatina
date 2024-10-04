use super::{EvalValue, Interpret, State};
use crate::inst::cast::*;

impl Interpret for Sext {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let value = state.lookup_val(*self.from());
        let ty = self.ty();

        value.with_imm(|value| value.sext(*ty))
    }
}

impl Interpret for Zext {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let value = state.lookup_val(*self.from());
        let ty = self.ty();

        value.with_imm(|value| value.zext(*ty))
    }
}

impl Interpret for Trunc {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let value = state.lookup_val(*self.from());
        let ty = self.ty();

        value.with_imm(|value| value.trunc(*ty))
    }
}
