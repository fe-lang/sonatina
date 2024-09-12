use macros::Inst;

use crate::{Type, Value};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Sext {
    #[inst(value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Zext {
    #[inst(value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Trunc {
    #[inst(value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
pub struct Bitcast {
    #[inst(value)]
    from: Value,
    ty: Type,
}
