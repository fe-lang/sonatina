use sonatina_ir::{
    Function, I256, Immediate, Type, U256, ValueId,
    inst::{BinaryInstKind, CastInstKind, UnaryInstKind, cast, downcast},
};

use crate::analysis::known_bits::{
    KnownBits, has_conflicting_known_bits, supports_known_bits, type_mask,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SimplifyExprResult {
    Const(Immediate),
    Copy(ValueId),
    NoChange,
}

impl SimplifyExprResult {
    pub(crate) fn is_no_change(&self) -> bool {
        matches!(self, Self::NoChange)
    }
}

pub(crate) trait ExprFactProvider {
    fn known_imm(&self, v: ValueId) -> Option<Immediate>;
    fn known_bits(&self, func: &Function, v: ValueId) -> KnownBits;
    fn same_non_undef(&self, lhs: ValueId, rhs: ValueId) -> bool;
    fn may_be_undef(&self, v: ValueId) -> bool;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvmModOp {
    Add,
    Mul,
}

fn integral_bit_width(ty: Type) -> Option<usize> {
    match ty {
        Type::I1 => Some(1),
        Type::I8 => Some(8),
        Type::I16 => Some(16),
        Type::I32 => Some(32),
        Type::I64 => Some(64),
        Type::I128 => Some(128),
        Type::I256 => Some(256),
        Type::EnumTag(_) | Type::Compound(_) | Type::Unit => None,
    }
}

fn integral_byte_width(ty: Type) -> Option<usize> {
    match ty {
        Type::I1 | Type::I8 => Some(1),
        Type::I16 => Some(2),
        Type::I32 => Some(4),
        Type::I64 => Some(8),
        Type::I128 => Some(16),
        Type::I256 => Some(32),
        Type::EnumTag(_) | Type::Compound(_) | Type::Unit => None,
    }
}

fn imm_to_u256(imm: Immediate) -> U256 {
    imm.as_i256().to_u256() & type_mask(imm.ty())
}

fn fold_evm_addmod_raw(lhs: U256, rhs: U256, modulus: U256) -> U256 {
    if modulus.is_zero() {
        return U256::zero();
    }

    let lhs = lhs % modulus;
    let rhs = rhs % modulus;
    let modulus_minus_rhs = modulus - rhs;

    if lhs >= modulus_minus_rhs {
        lhs - modulus_minus_rhs
    } else {
        lhs + rhs
    }
}

fn fold_evm_mulmod_raw(lhs: U256, rhs: U256, modulus: U256) -> U256 {
    if modulus.is_zero() {
        return U256::zero();
    }

    let mut result = U256::zero();
    let mut addend = lhs % modulus;
    let mut multiplier = rhs % modulus;

    while multiplier > U256::zero() {
        if multiplier & U256::one() == U256::one() {
            result = fold_evm_addmod_raw(result, addend, modulus);
        }
        addend = fold_evm_addmod_raw(addend, addend, modulus);
        multiplier >>= 1;
    }

    result
}

pub(crate) fn fold_evm_modop(
    lhs: Immediate,
    rhs: Immediate,
    modulus: Immediate,
    op: EvmModOp,
) -> Option<Immediate> {
    let ty = lhs.ty();
    if ty != rhs.ty() || ty != modulus.ty() || !ty.is_integral() {
        return None;
    }

    let result = match op {
        EvmModOp::Add => {
            fold_evm_addmod_raw(imm_to_u256(lhs), imm_to_u256(rhs), imm_to_u256(modulus))
        }
        EvmModOp::Mul => {
            fold_evm_mulmod_raw(imm_to_u256(lhs), imm_to_u256(rhs), imm_to_u256(modulus))
        }
    };
    Some(Immediate::from_i256(I256::from(result), ty))
}

pub(crate) fn simplify_evm_modop_known(
    lhs: Option<Immediate>,
    rhs: Option<Immediate>,
    modulus: Option<Immediate>,
    ty: Type,
    op: EvmModOp,
) -> Option<Immediate> {
    if !ty.is_integral() {
        return None;
    }

    if modulus.is_some_and(Immediate::is_zero) {
        return Some(Immediate::zero(ty));
    }

    fold_evm_modop(lhs?, rhs?, modulus?, op)
}

pub(crate) fn fold_evm_exp(base: Immediate, exponent: Immediate) -> Option<Immediate> {
    let ty = base.ty();
    if ty != exponent.ty() || !ty.is_integral() {
        return None;
    }

    let mask = type_mask(ty);
    let mut result = U256::one() & mask;
    let mut base = imm_to_u256(base) & mask;
    let mut exponent = imm_to_u256(exponent);

    while exponent > U256::zero() {
        if exponent & U256::one() == U256::one() {
            result = result.overflowing_mul(base).0 & mask;
        }

        exponent >>= 1;
        base = base.overflowing_mul(base).0 & mask;
    }

    Some(Immediate::from_i256(I256::from(result), ty))
}

pub(crate) fn simplify_evm_exp_known(
    base: Option<Immediate>,
    exponent: Option<Immediate>,
    ty: Type,
) -> Option<Immediate> {
    if !ty.is_integral() {
        return None;
    }

    if exponent.is_some_and(Immediate::is_zero) || base.is_some_and(Immediate::is_one) {
        return Some(Immediate::one(ty));
    }

    if base.is_some_and(Immediate::is_zero) && exponent.is_some_and(|imm| !imm.is_zero()) {
        return Some(Immediate::zero(ty));
    }

    fold_evm_exp(base?, exponent?)
}

pub(crate) fn fold_evm_byte(pos: Immediate, value: Immediate) -> Option<Immediate> {
    let ty = value.ty();
    if ty != pos.ty() || !ty.is_integral() {
        return None;
    }

    let pos = imm_to_u256(pos);
    if pos >= U256::from(32u8) {
        return Some(Immediate::zero(ty));
    }

    let value_bytes = integral_byte_width(ty)?;
    let pos = pos.as_usize();
    if pos < 32 - value_bytes {
        return Some(Immediate::zero(ty));
    }

    let idx = pos - (32 - value_bytes);
    let shift_bytes = value_bytes - 1 - idx;
    let result = (imm_to_u256(value) >> (shift_bytes * 8)) & U256::from(0xffu16);
    Some(Immediate::from_i256(I256::from(result), ty))
}

pub(crate) fn simplify_evm_byte_known(
    pos: Option<Immediate>,
    value: Option<Immediate>,
    ty: Type,
) -> Option<Immediate> {
    if !ty.is_integral() {
        return None;
    }

    if value.is_some_and(Immediate::is_zero) {
        return Some(Immediate::zero(ty));
    }

    fold_evm_byte(pos?, value?)
}

pub(crate) fn fold_evm_clz(word: Immediate) -> Option<Immediate> {
    let ty = word.ty();
    let bit_width = integral_bit_width(ty)?;
    let value = imm_to_u256(word);
    let clz = (0..bit_width)
        .rev()
        .find(|&bit| ((value >> bit) & U256::one()) == U256::one())
        .map_or(bit_width, |bit| bit_width - 1 - bit);
    Some(Immediate::from_i256(I256::from(clz), ty))
}

pub(crate) fn simplify_unary_with_same_inner(
    kind: UnaryInstKind,
    arg: ValueId,
    same_inner_arg: impl Fn(ValueId, UnaryInstKind) -> Option<ValueId>,
) -> SimplifyExprResult {
    match kind {
        UnaryInstKind::Not | UnaryInstKind::Neg => same_inner_arg(arg, kind)
            .map(SimplifyExprResult::Copy)
            .unwrap_or(SimplifyExprResult::NoChange),
        UnaryInstKind::Snego | UnaryInstKind::IsZero | UnaryInstKind::EvmClz => {
            SimplifyExprResult::NoChange
        }
    }
}

pub(crate) fn simplify_binary_with_facts(
    func: &Function,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    facts: &impl ExprFactProvider,
) -> SimplifyExprResult {
    let ty = func.dfg.value_ty(lhs);
    let lhs_imm = facts.known_imm(lhs);
    let rhs_imm = facts.known_imm(rhs);

    match kind {
        BinaryInstKind::Add => {
            if lhs_imm.is_some_and(Immediate::is_zero) {
                return SimplifyExprResult::Copy(rhs);
            }
            if rhs_imm.is_some_and(Immediate::is_zero) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Sub => {
            if ty.is_integral() && facts.same_non_undef(lhs, rhs) {
                return SimplifyExprResult::Const(Immediate::zero(ty));
            }
            if rhs_imm == Some(Immediate::zero(ty)) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Mul => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                let one = Immediate::one(ty);
                if lhs_imm == Some(zero) || rhs_imm == Some(zero) {
                    return SimplifyExprResult::Const(zero);
                }
                if lhs_imm == Some(one) {
                    return SimplifyExprResult::Copy(rhs);
                }
                if rhs_imm == Some(one) {
                    return SimplifyExprResult::Copy(lhs);
                }
            }
        }
        BinaryInstKind::And => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                let all_one = Immediate::all_one(ty);
                if lhs_imm == Some(zero) || rhs_imm == Some(zero) {
                    return SimplifyExprResult::Const(zero);
                }
                if lhs_imm == Some(all_one) {
                    return SimplifyExprResult::Copy(rhs);
                }
                if rhs_imm == Some(all_one) {
                    return SimplifyExprResult::Copy(lhs);
                }

                if let Some(copy) = simplify_and_copy_with_facts(func, lhs, rhs, facts)
                    .or_else(|| simplify_and_copy_with_facts(func, rhs, lhs, facts))
                {
                    return SimplifyExprResult::Copy(copy);
                }
            }
            if facts.same_non_undef(lhs, rhs) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Or => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                let all_one = Immediate::all_one(ty);
                if lhs_imm == Some(all_one) || rhs_imm == Some(all_one) {
                    return SimplifyExprResult::Const(all_one);
                }
                if lhs_imm == Some(zero) {
                    return SimplifyExprResult::Copy(rhs);
                }
                if rhs_imm == Some(zero) {
                    return SimplifyExprResult::Copy(lhs);
                }

                if let Some(copy) = simplify_or_copy_with_facts(func, lhs, rhs, facts)
                    .or_else(|| simplify_or_copy_with_facts(func, rhs, lhs, facts))
                {
                    return SimplifyExprResult::Copy(copy);
                }
            }
            if facts.same_non_undef(lhs, rhs) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Xor => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                if lhs_imm == Some(zero) {
                    return SimplifyExprResult::Copy(rhs);
                }
                if rhs_imm == Some(zero) {
                    return SimplifyExprResult::Copy(lhs);
                }
                if facts.same_non_undef(lhs, rhs) {
                    return SimplifyExprResult::Const(zero);
                }
            }
        }
        BinaryInstKind::Udiv
        | BinaryInstKind::Sdiv
        | BinaryInstKind::EvmUdiv
        | BinaryInstKind::EvmSdiv => {
            if ty.is_integral() && rhs_imm == Some(Immediate::one(ty)) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Umod
        | BinaryInstKind::Smod
        | BinaryInstKind::EvmUmod
        | BinaryInstKind::EvmSmod => {
            if ty.is_integral() && rhs_imm == Some(Immediate::one(ty)) {
                return SimplifyExprResult::Const(Immediate::zero(ty));
            }
        }
        BinaryInstKind::Eq => {
            if facts.same_non_undef(lhs, rhs) {
                return SimplifyExprResult::Const(Immediate::one(Type::I1));
            }
            if !facts.may_be_undef(lhs)
                && !facts.may_be_undef(rhs)
                && has_conflicting_known_bits(
                    facts.known_bits(func, lhs),
                    facts.known_bits(func, rhs),
                    ty,
                )
            {
                return SimplifyExprResult::Const(Immediate::zero(Type::I1));
            }
        }
        BinaryInstKind::Ne => {
            if facts.same_non_undef(lhs, rhs) {
                return SimplifyExprResult::Const(Immediate::zero(Type::I1));
            }
            if !facts.may_be_undef(lhs)
                && !facts.may_be_undef(rhs)
                && has_conflicting_known_bits(
                    facts.known_bits(func, lhs),
                    facts.known_bits(func, rhs),
                    ty,
                )
            {
                return SimplifyExprResult::Const(Immediate::one(Type::I1));
            }
        }
        BinaryInstKind::Shl | BinaryInstKind::Shr | BinaryInstKind::Sar => {
            let value_ty = func.dfg.value_ty(rhs);
            let value_zero = Immediate::zero(value_ty);
            if rhs_imm == Some(value_zero) {
                return SimplifyExprResult::Const(value_zero);
            }
            if lhs_imm.is_some_and(Immediate::is_zero) {
                return SimplifyExprResult::Copy(rhs);
            }
        }
        BinaryInstKind::Uaddo
        | BinaryInstKind::Uaddsat
        | BinaryInstKind::Saddo
        | BinaryInstKind::Saddsat
        | BinaryInstKind::Umulo
        | BinaryInstKind::Umulsat
        | BinaryInstKind::Smulo
        | BinaryInstKind::Smulsat
        | BinaryInstKind::Usubo
        | BinaryInstKind::Usubsat
        | BinaryInstKind::Ssubo
        | BinaryInstKind::Ssubsat
        | BinaryInstKind::Lt
        | BinaryInstKind::Gt
        | BinaryInstKind::Slt
        | BinaryInstKind::Sgt
        | BinaryInstKind::Le
        | BinaryInstKind::Ge
        | BinaryInstKind::Sle
        | BinaryInstKind::Sge
        | BinaryInstKind::EvmUdivo
        | BinaryInstKind::EvmSdivo
        | BinaryInstKind::EvmUmodo
        | BinaryInstKind::EvmSmodo
        | BinaryInstKind::EvmUaddsat
        | BinaryInstKind::EvmSaddsat
        | BinaryInstKind::EvmUsubsat
        | BinaryInstKind::EvmSsubsat
        | BinaryInstKind::EvmUmulsat
        | BinaryInstKind::EvmSmulsat
        | BinaryInstKind::EvmExp
        | BinaryInstKind::EvmByte => {}
    }

    SimplifyExprResult::NoChange
}

#[allow(dead_code)]
pub(crate) fn simplify_binary_with_known_imm(
    func: &Function,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    known_imm: impl Fn(ValueId) -> Option<Immediate>,
    same_value: impl Fn(ValueId, ValueId) -> bool,
) -> SimplifyExprResult {
    struct KnownImmFacts<K, S> {
        known_imm: K,
        same_value: S,
    }

    impl<K, S> ExprFactProvider for KnownImmFacts<K, S>
    where
        K: Fn(ValueId) -> Option<Immediate>,
        S: Fn(ValueId, ValueId) -> bool,
    {
        fn known_imm(&self, v: ValueId) -> Option<Immediate> {
            (self.known_imm)(v)
        }

        fn known_bits(&self, func: &Function, v: ValueId) -> KnownBits {
            KnownBits::unknown(func.dfg.value_ty(v))
        }

        fn same_non_undef(&self, lhs: ValueId, rhs: ValueId) -> bool {
            (self.same_value)(lhs, rhs)
        }

        fn may_be_undef(&self, _v: ValueId) -> bool {
            true
        }
    }

    simplify_binary_with_facts(
        func,
        kind,
        lhs,
        rhs,
        &KnownImmFacts {
            known_imm,
            same_value,
        },
    )
}

pub(crate) fn simplify_cast(
    func: &Function,
    kind: CastInstKind,
    from: ValueId,
    ty: Type,
) -> SimplifyExprResult {
    if func.dfg.value_ty(from) == ty {
        return SimplifyExprResult::Copy(from);
    }

    if matches!(kind, CastInstKind::Trunc)
        && let Some((inst, _)) = func.dfg.value_inst_result(from)
    {
        if let Some(zext) = downcast::<&cast::Zext>(func.inst_set(), func.dfg.inst(inst)) {
            let src = *zext.from();
            if func.dfg.value_ty(src) == ty {
                return SimplifyExprResult::Copy(src);
            }
        }

        if let Some(sext) = downcast::<&cast::Sext>(func.inst_set(), func.dfg.inst(inst)) {
            let src = *sext.from();
            if func.dfg.value_ty(src) == ty {
                return SimplifyExprResult::Copy(src);
            }
        }
    }

    SimplifyExprResult::NoChange
}

fn simplify_and_copy_with_facts(
    func: &Function,
    value: ValueId,
    mask_value: ValueId,
    facts: &impl ExprFactProvider,
) -> Option<ValueId> {
    let ty = func.dfg.value_ty(value);
    let mask_imm = facts.known_imm(mask_value)?;
    let keep_mask = KnownBits::from_imm(mask_imm).known_one & type_mask(ty);
    simplify_mask_copy_with_facts(
        func,
        value,
        type_mask(ty) & !keep_mask,
        facts,
        KnownBits::all_zero_in,
    )
}

fn simplify_or_copy_with_facts(
    func: &Function,
    value: ValueId,
    mask_value: ValueId,
    facts: &impl ExprFactProvider,
) -> Option<ValueId> {
    let ty = func.dfg.value_ty(value);
    let mask_imm = facts.known_imm(mask_value)?;
    let ones_mask = KnownBits::from_imm(mask_imm).known_one & type_mask(ty);
    simplify_mask_copy_with_facts(func, value, ones_mask, facts, KnownBits::all_one_in)
}

fn simplify_mask_copy_with_facts(
    func: &Function,
    value: ValueId,
    proved_mask: sonatina_ir::U256,
    facts: &impl ExprFactProvider,
    keeps_mask: impl Fn(KnownBits, sonatina_ir::U256) -> bool,
) -> Option<ValueId> {
    let ty = func.dfg.value_ty(value);
    if !supports_known_bits(ty) || facts.may_be_undef(value) {
        return None;
    }

    keeps_mask(facts.known_bits(func, value), proved_mask).then_some(value)
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        I256, Immediate, Linkage, Signature, Type, U256, builder::test_util::test_isa, isa::Isa,
        module::ModuleCtx,
    };

    use super::*;
    use crate::analysis::known_bits::KnownBits;

    struct MockFacts {
        known_bits: std::collections::BTreeMap<ValueId, KnownBits>,
        known_imm: std::collections::BTreeMap<ValueId, Immediate>,
        may_be_undef: std::collections::BTreeMap<ValueId, bool>,
    }

    impl ExprFactProvider for MockFacts {
        fn known_imm(&self, v: ValueId) -> Option<Immediate> {
            self.known_imm.get(&v).copied()
        }

        fn known_bits(&self, func: &Function, v: ValueId) -> KnownBits {
            self.known_bits
                .get(&v)
                .copied()
                .unwrap_or_else(|| KnownBits::unknown(func.dfg.value_ty(v)))
        }

        fn same_non_undef(&self, lhs: ValueId, rhs: ValueId) -> bool {
            lhs == rhs && !self.may_be_undef(lhs)
        }

        fn may_be_undef(&self, v: ValueId) -> bool {
            self.may_be_undef.get(&v).copied().unwrap_or_default()
        }
    }

    #[test]
    fn simplify_unary_with_same_inner_folds_double_not() {
        let arg = ValueId::from_u32(42);
        let simplified = simplify_unary_with_same_inner(UnaryInstKind::Not, arg, |value, kind| {
            if value == arg && kind == UnaryInstKind::Not {
                Some(ValueId::from_u32(7))
            } else {
                None
            }
        });

        assert_eq!(simplified, SimplifyExprResult::Copy(ValueId::from_u32(7)));
    }

    #[test]
    fn simplify_binary_with_known_imm_folds_shift_identities() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new_single("f", Linkage::Private, &[], Type::I256);
        let mut func = Function::new(&ctx, &sig);
        let bits = func.dfg.make_imm_value(Immediate::zero(Type::I8));
        let value = func
            .dfg
            .make_imm_value(Immediate::from_i256(I256::from(7), Type::I256));

        let simplified = simplify_binary_with_known_imm(
            &func,
            BinaryInstKind::Shl,
            bits,
            value,
            |v| func.dfg.value_imm(v),
            |_lhs, _rhs| false,
        );
        assert_eq!(simplified, SimplifyExprResult::Copy(value));
    }

    #[test]
    fn simplify_binary_with_facts_folds_redundant_mask() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new_single("f", Linkage::Private, &[Type::I256], Type::I256);
        let mut func = Function::new(&ctx, &sig);
        let value = func.arg_values[0];
        let mask = func
            .dfg
            .make_imm_value(Immediate::from_i256(I256::from(u32::MAX), Type::I256));
        let facts = MockFacts {
            known_bits: [(
                value,
                KnownBits::normalized(Type::I256, !U256::from(u32::MAX), U256::zero()),
            )]
            .into_iter()
            .collect(),
            known_imm: [(mask, Immediate::from_i256(I256::from(u32::MAX), Type::I256))]
                .into_iter()
                .collect(),
            may_be_undef: Default::default(),
        };

        let simplified =
            simplify_binary_with_facts(&func, BinaryInstKind::And, value, mask, &facts);
        assert_eq!(simplified, SimplifyExprResult::Copy(value));
    }

    #[test]
    fn simplify_binary_with_facts_folds_redundant_or() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new_single("f", Linkage::Private, &[Type::I256], Type::I256);
        let mut func = Function::new(&ctx, &sig);
        let value = func.arg_values[0];
        let mask = func
            .dfg
            .make_imm_value(Immediate::from_i256(I256::from(0xffu8), Type::I256));
        let facts = MockFacts {
            known_bits: [(
                value,
                KnownBits::normalized(Type::I256, U256::zero(), U256::from(0xffu8)),
            )]
            .into_iter()
            .collect(),
            known_imm: [(mask, Immediate::from_i256(I256::from(0xffu8), Type::I256))]
                .into_iter()
                .collect(),
            may_be_undef: Default::default(),
        };

        let simplified = simplify_binary_with_facts(&func, BinaryInstKind::Or, value, mask, &facts);
        assert_eq!(simplified, SimplifyExprResult::Copy(value));
    }

    #[test]
    fn simplify_binary_with_facts_detects_compare_contradiction() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new_single("f", Linkage::Private, &[Type::I8, Type::I8], Type::I1);
        let func = Function::new(&ctx, &sig);
        let lhs = func.arg_values[0];
        let rhs = func.arg_values[1];
        let facts = MockFacts {
            known_bits: [
                (
                    lhs,
                    KnownBits::normalized(Type::I8, U256::from(0b10u8), U256::zero()),
                ),
                (
                    rhs,
                    KnownBits::normalized(Type::I8, U256::zero(), U256::from(0b10u8)),
                ),
            ]
            .into_iter()
            .collect(),
            known_imm: Default::default(),
            may_be_undef: Default::default(),
        };

        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::Eq, lhs, rhs, &facts),
            SimplifyExprResult::Const(Immediate::I1(false))
        );
        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::Ne, lhs, rhs, &facts),
            SimplifyExprResult::Const(Immediate::I1(true))
        );
    }

    #[test]
    fn simplify_binary_with_facts_keeps_copy_fold_blocked_for_maybe_undef() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new_single("f", Linkage::Private, &[Type::I256], Type::I256);
        let mut func = Function::new(&ctx, &sig);
        let value = func.arg_values[0];
        let mask = func
            .dfg
            .make_imm_value(Immediate::from_i256(I256::from(u32::MAX), Type::I256));
        let facts = MockFacts {
            known_bits: [(
                value,
                KnownBits::normalized(Type::I256, !U256::from(u32::MAX), U256::zero()),
            )]
            .into_iter()
            .collect(),
            known_imm: [(mask, Immediate::from_i256(I256::from(u32::MAX), Type::I256))]
                .into_iter()
                .collect(),
            may_be_undef: [(value, true)].into_iter().collect(),
        };

        let simplified =
            simplify_binary_with_facts(&func, BinaryInstKind::And, value, mask, &facts);
        assert_eq!(simplified, SimplifyExprResult::NoChange);
    }

    #[test]
    fn simplify_cast_folds_trunc_of_zext_back_to_source() {
        let mb = sonatina_ir::builder::test_util::test_module_builder();
        let (evm, mut builder) =
            sonatina_ir::builder::test_util::test_func_builder(&mb, &[Type::I8], Type::I8);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let zext = builder.insert_inst_with(|| cast::Zext::new(is, arg, Type::I16), Type::I16);
        builder.seal_all();
        builder.finish();
        let func = mb
            .func_store
            .view(mb.func_store.funcs()[0], |func| func.clone());

        assert_eq!(
            simplify_cast(&func, CastInstKind::Trunc, zext, Type::I8),
            SimplifyExprResult::Copy(arg)
        );
    }
}
