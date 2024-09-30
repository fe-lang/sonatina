use sonatina_ir::{inst::arith::*, Immediate};

use super::{Interpret, State};

impl Interpret for Neg {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        state.lookup_val(*self.arg()).map(|imm| -imm)
    }
}

impl Interpret for Add {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;
        Some(lhs + rhs)
    }
}

impl Interpret for Sub {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;
        Some(lhs - rhs)
    }
}

impl Interpret for Mul {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;
        Some(lhs * rhs)
    }
}

impl Interpret for Sdiv {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;
        Some(lhs.sdiv(rhs))
    }
}

impl Interpret for Udiv {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;
        Some(lhs.udiv(rhs))
    }
}

impl Interpret for Shl {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let bits = state.lookup_val(*self.bits())?;
        let value = state.lookup_val(*self.value())?;

        Some(value << bits)
    }
}

impl Interpret for Shr {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let bits = state.lookup_val(*self.bits())?;
        let value = state.lookup_val(*self.value())?;

        Some(value >> bits)
    }
}
