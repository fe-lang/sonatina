use super::{Env, Interpret};

use sonatina_ir::{inst::cast::*, Immediate};

impl Interpret for Sext {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let value = env.lookup_val(*self.from())?;
        let ty = self.ty();
        Some(value.sext(*ty))
    }
}

impl Interpret for Zext {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let value = env.lookup_val(*self.from())?;
        let ty = self.ty();
        Some(value.zext(*ty))
    }
}

impl Interpret for Trunc {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate> {
        let value = env.lookup_val(*self.from())?;
        let ty = self.ty();
        Some(value.trunc(*ty))
    }
}

impl Interpret for Bitcast {
    fn interpret(&self, _env: &mut dyn Env) -> Option<Immediate> {
        todo!()
    }
}
