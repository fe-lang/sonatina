use macros::Inst;

use crate::{inst::impl_inst_write, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Neg {
    #[inst(value)]
    arg: ValueId,
}
impl_inst_write!(Neg);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Add {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_inst_write!(Add);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Mul {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_inst_write!(Mul);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sub {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_inst_write!(Sub);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sdiv {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_inst_write!(Sdiv);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Udiv {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_inst_write!(Udiv);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Umod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_inst_write!(Umod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Smod {
    #[inst(value)]
    lhs: ValueId,
    #[inst(value)]
    rhs: ValueId,
}
impl_inst_write!(Smod);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shl {
    #[inst(value)]
    bits: ValueId,
    #[inst(value)]
    value: ValueId,
}
impl_inst_write!(Shl);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Shr {
    #[inst(value)]
    bits: ValueId,
    #[inst(value)]
    value: ValueId,
}
impl_inst_write!(Shr);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sar {
    #[inst(value)]
    bits: ValueId,
    #[inst(value)]
    value: ValueId,
}
impl_inst_write!(Sar);
