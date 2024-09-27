use super::{Env, Interpret};

use sonatina_ir::{inst::logic::*, Immediate};

impl Interpret for Not {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let arg = env.lookup_val(*self.arg())?;
        Some(!arg)
    }
}

impl Interpret for And {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        Some(lhs & rhs)
    }
}

impl Interpret for Or {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        Some(lhs | rhs)
    }
}

impl Interpret for Xor {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        Some(lhs ^ rhs)
    }
}
