use macros::Inst;

use crate::ValueId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Neg {
    arg: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Add {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Mul {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sub {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sdiv {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Udiv {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Umod {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Smod {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shl {
    bits: ValueId,
    value: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shr {
    bits: ValueId,
    value: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sar {
    bits: ValueId,
    value: ValueId,
}
