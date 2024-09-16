use macros::Inst;
use smallvec::SmallVec;

use crate::{module::FuncRef, Block, Type, Value};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Jump {
    dest: Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct Br {
    #[inst(value)]
    cond: Value,

    z_dest: Block,
    nz_dest: Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(terminator)]
pub struct BrTable {
    #[inst(value)]
    scrutinee: Value,
    #[inst(value)]
    table: Vec<(Value, Block)>,

    default: Option<Block>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Phi {
    #[inst(value)]
    values: Vec<(Value, Block)>,
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct Call {
    #[inst(value)]
    args: SmallVec<[Value; 8]>,
    callee: FuncRef,
    ret_ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(has_side_effect)]
#[inst(terminator)]
pub struct Return {
    #[inst(value)]
    arg: Option<Value>,
}
