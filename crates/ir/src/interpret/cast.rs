use super::{Action, EvalValue, Interpret, State};
use crate::inst::cast::*;

impl Interpret for Sext {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let value = state.lookup_val(*self.from());
        let ty = self.ty();

        value.with_imm(|value| value.sext(*ty))
    }
}

impl Interpret for Zext {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let value = state.lookup_val(*self.from());
        let ty = self.ty();

        value.with_imm(|value| value.zext(*ty))
    }
}

impl Interpret for Trunc {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        let value = state.lookup_val(*self.from());
        let ty = self.ty();
        state.set_action(Action::Continue);

        value.with_imm(|value| value.trunc(*ty))
    }
}

impl Interpret for IntToPtr {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);
        let value = state.lookup_val(*self.from());
        let ty = self.ty();

        value.with_imm(|value| {
            let target_repr = state.dfg().ctx.type_layout.pointer_repl();
            if *ty > target_repr {
                value.trunc(target_repr)
            } else {
                value.zext(target_repr)
            }
        })
    }
}
