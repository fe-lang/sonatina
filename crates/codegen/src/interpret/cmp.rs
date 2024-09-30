use sonatina_ir::{inst::cmp::*, Immediate};

use super::{Interpret, State};

impl Interpret for Lt {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.lt(rhs))
    }
}

impl Interpret for Gt {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.gt(rhs))
    }
}

impl Interpret for Slt {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.slt(rhs))
    }
}

impl Interpret for Sgt {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.sgt(rhs))
    }
}

impl Interpret for Le {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.le(rhs))
    }
}

impl Interpret for Ge {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.ge(rhs))
    }
}

impl Interpret for Sle {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.sle(rhs))
    }
}

impl Interpret for Sge {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.sge(rhs))
    }
}
impl Interpret for Eq {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.imm_eq(rhs))
    }
}

impl Interpret for Ne {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;
        let rhs = state.lookup_val(*self.rhs())?;

        Some(lhs.imm_ne(rhs))
    }
}

impl Interpret for IsZero {
    fn interpret(&self, state: &mut dyn State) -> Option<Immediate> {
        let lhs = state.lookup_val(*self.lhs())?;

        Some(lhs.is_zero().into())
    }
}
