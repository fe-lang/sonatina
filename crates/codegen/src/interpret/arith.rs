use super::{Env, Interpret};

use sonatina_ir::{inst::arith::*, Immediate};

impl Interpret for Neg {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        env.lookup_val(*self.arg()).map(|imm| -imm)
    }
}

impl Interpret for Add {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        Some(lhs + rhs)
    }
}

impl Interpret for Sub {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        Some(lhs - rhs)
    }
}

impl Interpret for Mul {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        Some(lhs * rhs)
    }
}

impl Interpret for Sdiv {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        Some(lhs.sdiv(rhs))
    }
}

impl Interpret for Udiv {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        Some(lhs.udiv(rhs))
    }
}

impl Interpret for Umod {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        todo!()
    }
}

impl Interpret for Smod {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let lhs = env.lookup_val(*self.lhs())?;
        let rhs = env.lookup_val(*self.rhs())?;
        todo!()
    }
}

impl Interpret for Shl {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let bits = env.lookup_val(*self.bits())?;
        let value = env.lookup_val(*self.value())?;

        Some(value << bits)
    }
}

impl Interpret for Shr {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let bits = env.lookup_val(*self.bits())?;
        let value = env.lookup_val(*self.value())?;

        Some(value >> bits)
    }
}
