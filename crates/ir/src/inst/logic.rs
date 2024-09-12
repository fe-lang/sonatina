use macros::Inst;

use crate::Value;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Not {
    #[inst(value)]
    arg: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct And {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Or {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Xor {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}
