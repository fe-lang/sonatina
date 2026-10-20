use macros::Inst;

use crate::ValueId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(unary(Not)))]
pub struct Not {
    arg: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(binary(And)))]
pub struct And {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(binary(Or)))]
pub struct Or {
    lhs: ValueId,
    rhs: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(binary(Xor)))]
pub struct Xor {
    lhs: ValueId,
    rhs: ValueId,
}

/// Reverses the order of the bytes of an integer; an `i8` is unchanged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(unary(Bswap)))]
pub struct Bswap {
    arg: ValueId,
}
