use macros::Inst;

use crate::{impl_display_with_func, Type, ValueId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sext {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_display_with_func!(Sext);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Zext {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_display_with_func!(Zext);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Trunc {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_display_with_func!(Trunc);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Bitcast {
    #[inst(value)]
    from: ValueId,
    ty: Type,
}
impl_display_with_func!(Bitcast);
