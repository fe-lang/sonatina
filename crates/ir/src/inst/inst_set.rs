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

pub trait InstSetExt: InstSetBase {
    type InstKind<'i>;
    type InstKindMut<'i>;

    fn resolve_inst<'i>(&self, inst: &'i dyn Inst) -> Self::InstKind<'i>;
    fn resolve_inst_mut<'i>(&self, inst: &'i mut dyn Inst) -> Self::InstKindMut<'i>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Value;
    use basic::*;
    use macros::inst_set;

    #[inst_set(InstKind = "TestInstSetKind")]
    struct TestInstSet(Add, Sub, Not, Phi, Jump);

    #[test]
    fn ctor() {
        let _ = TestInstSet::new();
    }

    #[test]
    fn test_cast_isa() {
        let inst_set = TestInstSet::new();
        assert!(inst_set.has_add().is_some());
        assert!(inst_set.has_sub().is_some());
        assert!(inst_set.has_not().is_some());
        assert!(inst_set.has_phi().is_some());
        assert!(inst_set.has_jump().is_some());

        assert!(inst_set.has_lt().is_none());
        assert!(inst_set.has_br().is_none());
    }

    #[test]
    fn inst_creation() {
        let inst_set = TestInstSet::new();
        let v = Value::from_u32(1);
        let _add = Add::new(&inst_set, v, v);
        let _sub = Sub::new(&inst_set, v, v);
    }

    #[test]
    fn inst_resolution() {
        let inst_set = TestInstSet::new();
        let mut insts: Vec<Box<dyn Inst>> = Vec::new();

        let value = Value::from_u32(1);
        let add = Add::new(&inst_set, value, value);
        insts.push(Box::new(add));
        let sub = Sub::new(&inst_set, value, value);
        insts.push(Box::new(sub));
        let not = Not::new(&inst_set, value);
        insts.push(Box::new(not));

        let resolved = inst_set.resolve_inst(insts[0].as_ref());
        assert!(matches!(resolved, TestInstSetKind::Add(_)));
        let resolved = inst_set.resolve_inst(insts[1].as_ref());
        assert!(matches!(resolved, TestInstSetKind::Sub(_)));
        let resolved = inst_set.resolve_inst(insts[2].as_ref());
        assert!(matches!(resolved, TestInstSetKind::Not(_)));

        let resolved = inst_set.resolve_inst_mut(insts[0].as_mut());
        assert!(matches!(resolved, TestInstSetKindMut::Add(_)));
        let resolved = inst_set.resolve_inst_mut(insts[1].as_mut());
        assert!(matches!(resolved, TestInstSetKindMut::Sub(_)));
        let resolved = inst_set.resolve_inst_mut(insts[2].as_mut());
        assert!(matches!(resolved, TestInstSetKindMut::Not(_)));
    }
}
