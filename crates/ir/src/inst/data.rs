use macros::Inst;
use smallvec::SmallVec;

use crate::{inst::impl_inst_write, Type, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Read))]
pub struct Mload {
    #[inst(value)]
    addr: ValueId,
    ty: Type,
}
impl_inst_write!(Mload, (addr: ValueId, ty: Type));

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
pub struct Mstore {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    value: ValueId,
    ty: Type,
}
impl_inst_write!(Mstore, (value: ValueId, addr: ValueId, ty: Type));

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Gep {
    #[inst(value)]
    values: SmallVec<[ValueId; 8]>,
}
impl_inst_write!(Gep);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
pub struct Alloca {
    ty: Type,
}
impl_inst_write!(Alloca);
