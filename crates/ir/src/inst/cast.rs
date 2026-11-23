use macros::Inst;

use crate::{Type, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(cast(Sext)))]
pub struct Sext {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(cast(Zext)))]
pub struct Zext {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(cast(Trunc)))]
pub struct Trunc {
    from: ValueId,
    ty: Type,
}

/// Narrowing cast whose discarded high bits are assumed zero (undefined
/// behavior otherwise). Lowered without a mask on wide-word targets like EVM.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(cast(TruncNuw)))]
pub struct TruncNuw {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(cast(Bitcast)))]
pub struct Bitcast {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(cast(IntToPtr)))]
pub struct IntToPtr {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(kind(cast(PtrToInt)))]
pub struct PtrToInt {
    from: ValueId,
    ty: Type,
}
