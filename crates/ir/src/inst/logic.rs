use macros::Inst;

use crate::{impl_ir_write, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Not {
    #[inst(value)]
    arg: ValueId,
}
impl_ir_write!(Not);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct And {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_ir_write!(And);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Or {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_ir_write!(Or);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Xor {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_ir_write!(Xor);
