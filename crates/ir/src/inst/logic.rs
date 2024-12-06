use macros::Inst;

use crate::ValueId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Not {
    arg: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct And {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Or {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Xor {
    lhs: ValueId,
    rhs: ValueId,
}
