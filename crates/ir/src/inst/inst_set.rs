use macros::define_inst_set_base;

use super::{arith, cast, cmp, control_flow, data, evm, logic, Inst};

define_inst_set_base! {
    /// This trait is used to determine whether a certain instruction set includes a specific inst in runtime.
    /// If a certain instruction set `IS` implements `HasInst<I>`,
    /// the corresponding `has_i(&self) -> Option<&dyn HasInst<I>>` method always returns `Some`.
    ///
    /// Since all instruction set implements `HasInst<Inst>` if it contains `Inst`,
    /// this trait is naturally intended to be used as a trait object.
    ///
    /// NOTE: Do NOT implement this trait manually, use `sonatina-macro::inst_set` instead.
    ///
    /// Currently, all paths to the inst types should be the relative path from `inst` module,
    /// other than that, this macro won't work.
    /// We should fix this in the future of course.
    trait InstSetBase {
        arith::Neg,
        arith::Add,
        arith::Mul,
        arith::Sub,
        arith::Sdiv,
        arith::Udiv,
        arith::Umod,
        arith::Smod,
        arith::Shl,
        arith::Shr,
        arith::Sar,
        cmp::Lt,
        cmp::Gt,
        cmp::Slt,
        cmp::Sgt,
        cmp::Le,
        cmp::Ge,
        cmp::Sle,
        cmp::Sge,
        cmp::Eq,
        cmp::Ne,
        cmp::IsZero,
        logic::Not,
        logic::And,
        logic::Or,
        logic::Xor,
        cast::Sext,
        cast::Zext,
        cast::Trunc,
        cast::Bitcast,
        cast::IntToPtr,
        data::Mload,
        data::Mstore,
        data::Gep,
        control_flow::Call,
        control_flow::Jump,
        control_flow::Br,
        control_flow::BrTable,
        control_flow::Return,
        control_flow::Phi,
        // Evm specific
        evm::EvmStop,
        evm::EvmAddMod,
        evm::EvmMulMod,
        evm::EvmExp,
        evm::EvmByte,
        evm::EvmKeccak256,
        evm::EvmAddress,
        evm::EvmBalance,
        evm::EvmOrigin,
        evm::EvmCaller,
        evm::EvmCallValue,
        evm::EvmCallDataLoad,
        evm::EvmCallDataCopy,
        evm::EvmCodeSize,
        evm::EvmCodeCopy,
        evm::EvmGasPrice,
        evm::EvmExtCodeSize,
        evm::EvmExtCodeCopy,
        evm::EvmReturnDataSize,
        evm::EvmReturnDataCopy,
        evm::EvmExtCodeHash,
        evm::EvmBlockHash,
        evm::EvmCoinBase,
        evm::EvmTimestamp,
        evm::EvmNumber,
        evm::EvmPrevRandao,
        evm::EvmGasLimit,
        evm::EvmChainId,
        evm::EvmSelfBalance,
        evm::EvmBaseFee,
        evm::EvmBlobHash,
        evm::EvmBlobBaseFee,
        evm::EvmMstore8,
        evm::EvmSload,
        evm::EvmSstore,
        evm::EvmMsize,
        evm::EvmGas,
        evm::EvmTload,
        evm::EvmTstore,
        evm::EvmLog0,
        evm::EvmLog1,
        evm::EvmLog2,
        evm::EvmLog3,
        evm::EvmLog4,
        evm::EvmCreate,
        evm::EvmCall,
        evm::EvmReturn,
        evm::EvmDelegateCall,
        evm::EvmCreate2,
        evm::EvmStaticCall,
        evm::EvmRevert,
        evm::EvmSelfDestruct,
    }
}

/// This trait provides the concrete mapping from `Inst` to corresponding enum
/// variant. All instruction set that are defined by `sonatina_macros::inst_set`
/// automatically defines an enum which represents all instructions in the set.
/// e.g.
///
/// ```rust,ignore
/// use sonatina_ir::inst::{arith::*, control_flow::*};
/// #[inst_set(InstKind = "InstKind")]
/// struct InstSet(Jump, Phi, Add, Sub);
/// ```
/// defines
///
/// ```rust
/// use sonatina_ir::inst::{arith::*, control_flow::*};
/// enum InstKind<'i> {
///     Jump(&'i Jump),
///     Phi(&'i Phi),
///     Add(&'i Add),
///     Sub(&'i Sub),
/// }
/// enum InstKindMut<'i> {
///     Jump(&'i mut Jump),
///     Phi(&'i mut Phi),
///     Add(&'i mut Add),
///     Sub(&'i mut Sub),
/// }
/// ```
///
/// Assuming that the all instructions are created with this instruction set,
/// the cast(resolution) from dynamic inst object to this enum always succeed.
///
/// This macro provides the way to these safe downcast, and allow us to focus on
/// the restricted concrete instruction set, instead of "all possible"
/// instructions.
pub trait InstSetExt: InstSetBase {
    type InstKind<'i>;
    type InstKindMut<'i>;

    fn resolve_inst<'i>(&self, inst: &'i dyn Inst) -> Self::InstKind<'i>;
    fn resolve_inst_mut<'i>(&self, inst: &'i mut dyn Inst) -> Self::InstKindMut<'i>;
}

#[cfg(test)]
mod tests {
    use arith::*;
    use control_flow::*;
    use logic::*;
    use macros::inst_set;

    use super::*;
    use crate::{InstDowncast, InstDowncastMut, ValueId};

    #[inst_set(InstKind = "TestInstKind")]
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
        let v = ValueId::from_u32(1);
        let _add = Add::new(&inst_set, v, v);
        let _sub = Sub::new(&inst_set, v, v);
    }

    #[test]
    fn inst_downcast() {
        let mut insts: Vec<Box<dyn Inst>> = Vec::new();
        let inst_set = TestInstSet::new();
        let v = ValueId::from_u32(1);
        let add = Add::new(&inst_set, v, v);
        insts.push(Box::new(add));
        let sub = Sub::new(&inst_set, v, v);
        insts.push(Box::new(sub));

        assert!(
            <&Add as InstDowncast>::downcast(&inst_set, insts.first().unwrap().as_ref()).is_some()
        );
        assert!(
            <&Sub as InstDowncast>::downcast(&inst_set, insts.get(1).unwrap().as_ref()).is_some()
        );
        assert!(<&mut Add as InstDowncastMut>::downcast_mut(
            &inst_set,
            insts.get_mut(0).unwrap().as_mut()
        )
        .is_some());
        assert!(<&mut Sub as InstDowncastMut>::downcast_mut(
            &inst_set,
            insts.get_mut(1).unwrap().as_mut()
        )
        .is_some());
    }

    #[test]
    fn inst_resolution() {
        let inst_set = TestInstSet::new();
        let mut insts: Vec<Box<dyn Inst>> = Vec::new();

        let value = ValueId::from_u32(1);
        let add = Add::new(&inst_set, value, value);
        insts.push(Box::new(add));
        let sub = Sub::new(&inst_set, value, value);
        insts.push(Box::new(sub));
        let not = Not::new(&inst_set, value);
        insts.push(Box::new(not));

        let resolved = inst_set.resolve_inst(insts[0].as_ref());
        assert!(matches!(resolved, TestInstKind::Add(_)));
        let resolved = inst_set.resolve_inst(insts[1].as_ref());
        assert!(matches!(resolved, TestInstKind::Sub(_)));
        let resolved = inst_set.resolve_inst(insts[2].as_ref());
        assert!(matches!(resolved, TestInstKind::Not(_)));

        let resolved = inst_set.resolve_inst_mut(insts[0].as_mut());
        assert!(matches!(resolved, TestInstKindMut::Add(_)));
        let resolved = inst_set.resolve_inst_mut(insts[1].as_mut());
        assert!(matches!(resolved, TestInstKindMut::Sub(_)));
        let resolved = inst_set.resolve_inst_mut(insts[2].as_mut());
        assert!(matches!(resolved, TestInstKindMut::Not(_)));
    }
}

pub(super) mod sealed {
    /// This trait has two roles,
    /// 1. works as a sealed trait.
    /// 2. ensure that an `Inst` is definitely registered to the `InstSetBase`.
    pub trait Registered {}
}
