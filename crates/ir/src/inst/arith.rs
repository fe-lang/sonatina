use macros::Inst;

use crate::ValueId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Neg {
    #[inst(value)]
    arg: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Add {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Mul {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sub {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Sdiv {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Udiv {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Umod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Smod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shl {
    #[inst(value)]
    bits: ValueId,
    #[inst(value)]
    value: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shr {
    #[inst(value)]
    bits: ValueId,
    #[inst(value)]
    value: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sar {
    #[inst(value)]
    bits: ValueId,
    #[inst(value)]
    value: ValueId,
}
