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
