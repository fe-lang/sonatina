use sonatina_ir::{inst, BlockId, Immediate, ValueId};
use sonatina_macros::inst_prop;

mod arith;
mod cast;
mod cmp;
mod logic;

#[inst_prop(Subset = "Interpretable")]
pub trait Interpret {
    fn interpret(&self, env: &mut dyn State) -> EvalValue;

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
    fn lookup_val(&mut self, value: ValueId) -> EvalValue;

    fn set_next_action(&mut self, action: Action);
}

pub enum Action {
    Continue,
    JumpTo(BlockId),
    Return(ValueId),
}

pub enum EvalValue {
    Imm(Immediate),
    Undef,
}

impl EvalValue {
    pub fn with_imm<F, R>(self, f: F) -> Self
    where
        F: FnOnce(Immediate) -> R,
        R: Into<Self>,
    {
        match self {
            EvalValue::Imm(value) => f(value).into(),
            EvalValue::Undef => EvalValue::Undef,
        }
    }

    pub fn zip_with_imm<F, R>(lhs: Self, rhs: Self, f: F) -> Self
    where
        F: FnOnce(Immediate, Immediate) -> R,
        R: Into<Self>,
    {
        match (lhs, rhs) {
            (EvalValue::Imm(l), EvalValue::Imm(r)) => f(l, r).into(),
            _ => EvalValue::Undef,
        }
    }
}

impl From<Immediate> for EvalValue {
    fn from(imm: Immediate) -> Self {
        Self::Imm(imm)
    }
}
