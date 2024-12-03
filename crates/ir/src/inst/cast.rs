use macros::Inst;

use crate::{Type, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sext {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Zext {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Trunc {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Bitcast {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct IntToPtr {
    from: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct PtrToInt {
    from: ValueId,
    ty: Type,
}
