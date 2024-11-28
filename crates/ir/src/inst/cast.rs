use macros::Inst;

use crate::{inst::impl_inst_write, Type, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sext {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(Sext, {from, ty});

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Zext {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(Zext, {from, ty});

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Trunc {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(Trunc, {from, ty});

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Bitcast {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(Bitcast, {from, ty});

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct IntToPtr {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(IntToPtr, {from, ty});

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct PtrToInt {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(PtrToInt, {from, ty});
