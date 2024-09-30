use sonatina_ir::{inst::cast::*, Immediate};

use super::{Interpret, State};

impl Interpret for Sext {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let value = state.lookup_val(*self.from())?;
        let ty = self.ty();
        Some(value.sext(*ty))
    }
}

impl Interpret for Zext {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let value = state.lookup_val(*self.from())?;
        let ty = self.ty();
        Some(value.zext(*ty))
    }
}

impl Interpret for Trunc {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let value = state.lookup_val(*self.from())?;
        let ty = self.ty();
        Some(value.trunc(*ty))
    }
}
