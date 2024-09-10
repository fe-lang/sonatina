use super::{basic, Inst};

use macros::define_inst_set_base;

pub(super) mod sealed {
    /// This trait has two roles,
    /// 1. works as a sealed trait.
    /// 2. ensure that an `Inst` is definitely registered to the `InstGroup`.
    pub trait Registered {}
}

// All instructions defined in the IR must be listed(otherwise, you'll get a compile error).
define_inst_set_base! {
    basic::Not,
    basic::Neg,
    basic::Add,
    basic::Mul,
    basic::Sub,
    basic::Sdiv,
    basic::Udiv,
    basic::Lt,
    basic::Gt,
    basic::Slt,
    basic::Sgt,
    basic::Le,
    basic::Ge,
    basic::Sle,
    basic::Sge,
    basic::Eq,
    basic::Ne,
    basic::And,
    basic::Or,
    basic::Xor,
    basic::Sext,
    basic::Zext,
    basic::Trunc,
    basic::Bitcast,
    basic::Mload,
    basic::Mstore,
    basic::Call,
    basic::Jump,
    basic::Br,
    basic::BrTable,
    basic::Alloca,
    basic::Return,
    basic::Gep,
    basic::Phi,
    basic::Nop,
}

pub trait StaticInstSet: InstSetBase {
    type InstKind;
    type InstKindMut;

    fn resolve_inst(inst: &dyn Inst) -> Self::InstKind;
    fn resolve_inst_mut(inst: &mut dyn Inst) -> Self::InstKindMut;
}
