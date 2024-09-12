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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Umod {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Smod {
    #[inst(value)]
    lhs: Value,
    #[inst(value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shl {
    #[inst(value)]
    bits: Value,
    #[inst(value)]
    value: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shr {
    #[inst(value)]
    bits: Value,
    #[inst(value)]
    value: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sar {
    #[inst(value)]
    bits: Value,
    #[inst(value)]
    value: Value,
}
