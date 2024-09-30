use sonatina_ir::{inst, Immediate, ValueId};
use sonatina_macros::inst_prop;

mod arith;
mod cast;
mod cmp;
mod logic;

#[inst_prop(Subset = "Interpretable")]
pub trait Interpret {
    fn interpret(&self, env: &mut dyn State) -> Option<Immediate>;

    type Members = (
        inst::arith::Neg,
        inst::arith::Add,
        inst::arith::Sub,
        inst::arith::Mul,
        inst::arith::Sdiv,
        inst::arith::Udiv,
        inst::arith::Shl,
        inst::arith::Shr,
        inst::logic::Not,
        inst::logic::And,
        inst::logic::Or,
        inst::logic::Xor,
        inst::cast::Sext,
        inst::cast::Zext,
        inst::cast::Trunc,
        inst::cmp::Lt,
        inst::cmp::Gt,
        inst::cmp::Slt,
        inst::cmp::Sgt,
        inst::cmp::Le,
        inst::cmp::Ge,
        inst::cmp::Sle,
        inst::cmp::Sge,
        inst::cmp::Eq,
        inst::cmp::Ne,
        inst::cmp::IsZero,
    );
}

pub trait State {
    fn lookup_val(&mut self, value: ValueId) -> Option<Immediate>;
}
