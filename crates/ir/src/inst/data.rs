use macros::Inst;
use smallvec::SmallVec;

use crate::{Type, ValueId, module::FuncRef};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Read))]
pub struct Mload {
    addr: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
pub struct Mstore {
    addr: ValueId,
    value: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Gep {
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
    dest: ValueId,
    idx: ValueId,
    value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct ExtractValue {
    dest: ValueId,
    idx: ValueId,
}
