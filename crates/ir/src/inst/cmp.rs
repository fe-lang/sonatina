use macros::Inst;

use crate::{impl_display_with_func, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Lt {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Lt);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Gt {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Gt);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Slt {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Slt);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sgt {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Sgt);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Le {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Le);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Ge {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Ge);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sle {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Sle);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sge {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Sge);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Eq {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Eq);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Ne {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_display_with_func!(Ne);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct IsZero {
    #[inst(value)]
    lhs: ValueId,
}
impl_display_with_func!(IsZero);
