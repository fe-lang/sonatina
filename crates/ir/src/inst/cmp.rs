use macros::Inst;

use crate::ValueId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Lt {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Gt {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Slt {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sgt {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Le {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Ge {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sle {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sge {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Eq {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Ne {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct IsZero {
    lhs: ValueId,
}
