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

/// `then_value` when `cond`, an `i1`, is true, else `else_value`: a choice
/// between two values of one integral or pointer type, without a branch.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Select {
    cond: ValueId,
    then_value: ValueId,
    else_value: ValueId,
}

/// Reverses the order of the bytes of an integer; an `i8` is unchanged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(unary(Bswap)))]
pub struct Bswap {
    arg: ValueId,
}

/// The number of zero bits above the highest set bit of an integer, as an
/// integer of the same type: the width of the type for zero.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(unary(Clz)))]
pub struct Clz {
    arg: ValueId,
}

/// The number of zero bits below the lowest set bit of an integer, as an
/// integer of the same type: the width of the type for zero.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(unary(Ctz)))]
pub struct Ctz {
    arg: ValueId,
}
