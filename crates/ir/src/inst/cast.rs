use macros::Inst;

use crate::{impl_ir_write, Type, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sext {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_ir_write!(Sext);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Zext {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_ir_write!(Zext);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Trunc {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_ir_write!(Trunc);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Bitcast {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_ir_write!(Bitcast);
