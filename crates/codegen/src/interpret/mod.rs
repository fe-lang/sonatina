use sonatina_ir::{Immediate, ValueId};

mod arith;
mod cmp;

pub trait Interpret {
    fn interpret(&self, env: &mut dyn Env) -> Option<Immediate>;
}

pub trait Env {
    fn lookup_val(&self, value: ValueId) -> Option<Immediate>;
}
