use macros::Inst;

use crate::Value;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Lt {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Gt {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Slt {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sgt {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Le {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Ge {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sle {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sge {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Eq {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Ne {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}
