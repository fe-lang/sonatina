use macros::Inst;

use crate::{inst::impl_inst_write, Type, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sext {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(Sext, (from: ValueId, ty: Type));

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Zext {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(Zext, (from: ValueId, ty: Type));

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Trunc {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(Trunc, (from: ValueId, ty: Type));

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Bitcast {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(Bitcast, (from: ValueId, ty: Type));

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct IntToPtr {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_inst_write!(IntToPtr, (from: ValueId, ty: Type));
