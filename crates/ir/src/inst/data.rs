use macros::Inst;
use smallvec::SmallVec;

use crate::{impl_ir_write, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Mload {
    #[inst(value)]
    addr: ValueId,
}
impl_ir_write!(Mload);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
pub struct Mstore {
    #[inst(value)]
    value: ValueId,
    #[inst(value)]
    addr: ValueId,
}
impl_ir_write!(Mstore);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Gep {
    #[inst(value)]
    values: SmallVec<[ValueId; 8]>,
}
impl_ir_write!(Gep);
