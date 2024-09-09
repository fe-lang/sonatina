use super::{basic, Inst};

use sonatina_macros::define_dyn_inst_group;

pub(super) mod sealed {
    /// This trait has two roles,
    /// 1. works as a sealed trait.
    /// 2. ensure that an `Inst` is definitely registered to the `InstGroup`.
    pub trait Registered {}
}

define_dyn_inst_group! {
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

pub trait ConcreteInstGroup: DynInstGroup {
    type InstSet;
    type InstSetMut;

    fn downcast(inst: &dyn Inst) -> Self::InstSet;
    fn downcast_mut(inst: &mut dyn Inst) -> Self::InstSetMut;
}
