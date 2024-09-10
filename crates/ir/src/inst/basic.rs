use crate::{module::FuncRef, Block, Type, Value};
use smallvec::SmallVec;

use macros::Inst;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Not {
    #[inst(visit_value)]
    arg: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Neg {
    #[inst(visit_value)]
    arg: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Add {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Mul {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sub {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Sdiv {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Udiv {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Lt {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Gt {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Slt {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sgt {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Le {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Ge {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sle {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sge {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Eq {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Ne {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct And {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Or {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Xor {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sext {
    #[inst(visit_value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Zext {
    #[inst(visit_value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Trunc {
    #[inst(visit_value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Bitcast {
    #[inst(visit_value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Mload {
    #[inst(visit_value)]
    addr: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Mstore {
    #[inst(visit_value)]
    value: Value,
    #[inst(visit_value)]
    addr: Value,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Call {
    #[inst(visit_value)]
    args: SmallVec<[Value; 8]>,
    callee: FuncRef,
    ret_ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Jump {
    dest: Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Br {
    #[inst(visit_value)]
    cond: Value,

    z_dest: Block,
    nz_dest: Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct BrTable {
    #[inst(visit_value)]
    scrutinee: Value,
    #[inst(visit_value)]
    table: Vec<(Value, Block)>,

    default: Option<Block>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Alloca {
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Return {
    #[inst(visit_value)]
    arg: Option<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Gep {
    #[inst(visit_value)]
    values: SmallVec<[Value; 8]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Phi {
    #[inst(visit_value)]
    values: Vec<(Value, Block)>,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Nop {}
