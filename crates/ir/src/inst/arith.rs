use macros::Inst;

use crate::Value;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Neg {
    #[inst(value)]
    arg: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Add {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Mul {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sub {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Sdiv {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Udiv {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}
