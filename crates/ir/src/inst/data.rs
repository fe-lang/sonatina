use macros::Inst;
use smallvec::SmallVec;

use crate::{inst::impl_inst_write, Type, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Mload {
    #[inst(value)]
    addr: ValueId,
    ty: Type,
}
impl_inst_write!(Mload);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Mstore {
    #[inst(value)]
    value: ValueId,
    #[inst(value)]
    addr: ValueId,
    ty: Type,
}
impl_inst_write!(Mstore);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Gep {
    #[inst(value)]
    values: SmallVec<[ValueId; 8]>,
}
impl_inst_write!(Gep);
