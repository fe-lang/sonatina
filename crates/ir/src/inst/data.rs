use macros::Inst;
use smallvec::SmallVec;

use crate::{module::FuncRef, Type, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Read))]
pub struct Mload {
    #[inst(value)]
    addr: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
pub struct Mstore {
    #[inst(value)]
    addr: ValueId,
    #[inst(value)]
    value: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Gep {
    #[inst(value)]
    values: SmallVec<[ValueId; 8]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct GetFunctionPtr {
    func: FuncRef,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
pub struct Alloca {
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct InsertValue {
    #[inst(value)]
    dest: ValueId,
    #[inst(value)]
    idx: ValueId,
    #[inst(value)]
    value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct ExtractValue {
    #[inst(value)]
    dest: ValueId,
    #[inst(value)]
    idx: ValueId,
}
