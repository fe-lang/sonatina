use macros::Inst;

use crate::ValueId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Lt {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Gt {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Slt {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sgt {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Le {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Ge {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sle {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sge {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Eq {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Ne {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct IsZero {
    #[inst(value)]
    lhs: ValueId,
}
