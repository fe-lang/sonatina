use macros::Inst;

use crate::{impl_display_with_func, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Not {
    #[inst(value)]
    arg: ValueId,
}
impl_display_with_func!(Not);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct And {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(And);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Or {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Or);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Xor {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Xor);
