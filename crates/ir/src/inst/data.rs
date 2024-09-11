use macros::Inst;
use smallvec::SmallVec;

use crate::{module::FuncRef, Type, Value};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Mload {
    #[inst(value)]
    addr: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Mstore {
    #[inst(value)]
    value: Value,
    #[inst(value)]
    addr: Value,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Alloca {
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Gep {
    #[inst(value)]
    values: SmallVec<[Value; 8]>,
}
