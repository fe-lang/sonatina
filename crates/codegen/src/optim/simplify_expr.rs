use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, I256, Immediate, InstId, Type, U256, Value, ValueId,
    inst::{
        BinaryInstKind, CastInstKind, InstClassKind, InstKeyExt, OwnedInstKey, UnaryInstKind, cast,
        downcast,
    },
};

use crate::{
    analysis::known_bits::{KnownBits, has_conflicting_known_bits, supports_known_bits, type_mask},
    range_analysis::RangeFact,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SimplifiedResult {
    NoChange,
    Const(Immediate),
    Copy(ValueId),
}

impl SimplifiedResult {
    pub(crate) fn is_no_change(&self) -> bool {
        matches!(self, Self::NoChange)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SimplifiedInst {
    pub(crate) results: SmallVec<[SimplifiedResult; 2]>,
}

impl SimplifiedInst {
    pub(crate) fn no_change(len: usize) -> Self {
        Self {
            results: std::iter::repeat_n(SimplifiedResult::NoChange, len).collect(),
        }
    }

    pub(crate) fn one(result: SimplifiedResult) -> Self {
        Self {
            results: smallvec![result],
        }
    }

    pub(crate) fn result(&self, idx: usize) -> SimplifiedResult {
        self.results
            .get(idx)
            .copied()
            .unwrap_or(SimplifiedResult::NoChange)
    }

    pub(crate) fn is_no_change(&self) -> bool {
        self.results.iter().all(SimplifiedResult::is_no_change)
    }
}

pub(crate) trait ExprFactProvider {
    fn known_imm(&self, v: ValueId) -> Option<Immediate>;
    fn known_bits(&self, func: &Function, v: ValueId) -> KnownBits;
    fn range(&self, _v: ValueId) -> Option<RangeFact> {
        None
    }
    fn same_non_undef(&self, lhs: ValueId, rhs: ValueId) -> bool;
    fn may_be_undef(&self, v: ValueId) -> bool;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvmModOp {
    Add,
    Mul,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ZextI1CompareRewrite {
    Copy(ValueId),
    IsZero(ValueId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct KnownValueFact {
    pub(crate) imm: Option<Immediate>,
    pub(crate) may_be_undef: bool,
}

pub(crate) fn integral_bit_width(ty: Type) -> Option<usize> {
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

pub(crate) fn shift_amount_for_pow2_mul(imm: Immediate) -> Option<usize> {
    let bit_width = integral_bit_width(imm.ty())?;
    let mut value = imm_to_u256(imm);
    if value == U256::zero() || value & (value - U256::one()) != U256::zero() {
        return None;
    }

    let mut shift = 0;
    while value > U256::one() {
        value >>= 1;
        shift += 1;
    }

    (shift != 0 && shift < bit_width).then_some(shift)
}

pub(crate) fn simplify_zext_i1_compare(
    func: &Function,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    known_imm: impl Fn(ValueId) -> Option<Immediate>,
) -> Option<ZextI1CompareRewrite> {
    simplify_zext_i1_compare_one_side(func, kind, lhs, rhs, &known_imm)
        .or_else(|| simplify_zext_i1_compare_one_side(func, kind, rhs, lhs, &known_imm))
}

fn simplify_zext_i1_compare_one_side(
    func: &Function,
    kind: BinaryInstKind,
    widened: ValueId,
    other: ValueId,
    known_imm: &impl Fn(ValueId) -> Option<Immediate>,
) -> Option<ZextI1CompareRewrite> {
    let from = zext_i1_source(func, widened)?;
    let ty = func.dfg.value_ty(widened);
    let imm = known_imm(other)?;

    match kind {
        BinaryInstKind::Eq if imm == Immediate::one(ty) => Some(ZextI1CompareRewrite::Copy(from)),
        BinaryInstKind::Ne if imm == Immediate::zero(ty) => Some(ZextI1CompareRewrite::Copy(from)),
        BinaryInstKind::Eq if imm == Immediate::zero(ty) => {
            Some(ZextI1CompareRewrite::IsZero(from))
        }
        BinaryInstKind::Ne if imm == Immediate::one(ty) => Some(ZextI1CompareRewrite::IsZero(from)),
        _ => None,
    }
}

fn zext_i1_source(func: &Function, value: ValueId) -> Option<ValueId> {
    let Value::Inst { inst, .. } = func.dfg.value(value) else {
        return None;
    };
    if func.dfg.inst(*inst).kind() != InstClassKind::Cast(CastInstKind::Zext) {
        return None;
    }

    let values = func.dfg.inst(*inst).collect_values();
    let [from] = values.as_slice() else {
        return None;
    };
    (func.dfg.value_ty(*from) == Type::I1).then_some(*from)
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
    lhs: KnownValueFact,
    rhs: KnownValueFact,
    modulus: KnownValueFact,
    ty: Type,
    op: EvmModOp,
) -> Option<Immediate> {
    if !ty.is_integral() {
        return None;
    }
    if lhs.may_be_undef || rhs.may_be_undef || modulus.may_be_undef {
        return None;
    }

    if modulus.imm.is_some_and(Immediate::is_zero) {
        return Some(Immediate::zero(ty));
    }

    fold_evm_modop(lhs.imm?, rhs.imm?, modulus.imm?, op)
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
    base: KnownValueFact,
    exponent: KnownValueFact,
    ty: Type,
) -> Option<Immediate> {
    if !ty.is_integral() {
        return None;
    }
    if base.may_be_undef || exponent.may_be_undef {
        return None;
    }

    if exponent.imm.is_some_and(Immediate::is_zero) || base.imm.is_some_and(Immediate::is_one) {
        return Some(Immediate::one(ty));
    }

    if base.imm.is_some_and(Immediate::is_zero) && exponent.imm.is_some_and(|imm| !imm.is_zero()) {
        return Some(Immediate::zero(ty));
    }

    fold_evm_exp(base.imm?, exponent.imm?)
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
    pos: KnownValueFact,
    value: KnownValueFact,
    ty: Type,
) -> Option<Immediate> {
    if !ty.is_integral() {
        return None;
    }
    if pos.may_be_undef || value.may_be_undef {
        return None;
    }

    if value.imm.is_some_and(Immediate::is_zero) {
        return Some(Immediate::zero(ty));
    }

    fold_evm_byte(pos.imm?, value.imm?)
}

fn fold_evm_signextend_raw(byte: U256, value: U256, ty: Type) -> U256 {
    let mask = type_mask(ty);
    if byte >= U256::from(32u8) {
        return value & mask;
    }

    let sign_bit = (byte.as_usize() + 1) * 8 - 1;
    let result = if value.bit(sign_bit) {
        value | (!U256::zero() << (sign_bit + 1))
    } else {
        value & ((U256::one() << (sign_bit + 1)) - U256::one())
    };
    result & mask
}

pub(crate) fn fold_evm_signextend(byte: Immediate, value: Immediate) -> Option<Immediate> {
    let ty = value.ty();
    if ty != byte.ty() || !ty.is_integral() {
        return None;
    }

    let result = fold_evm_signextend_raw(imm_to_u256(byte), imm_to_u256(value), ty);
    Some(Immediate::from_i256(I256::from(result), ty))
}

pub(crate) fn simplify_evm_signextend_known(
    byte: KnownValueFact,
    value: KnownValueFact,
    ty: Type,
) -> Option<Immediate> {
    if !ty.is_integral() || byte.may_be_undef || value.may_be_undef {
        return None;
    }

    if value.imm.is_some_and(Immediate::is_zero) {
        return Some(Immediate::zero(ty));
    }

    fold_evm_signextend(byte.imm?, value.imm?)
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

pub(crate) fn simplify_inst_with_facts(
    func: &Function,
    inst_id: InstId,
    facts: &impl ExprFactProvider,
) -> SimplifiedInst {
    let inst = func.dfg.inst(inst_id);
    let result_tys: SmallVec<[_; 2]> = func
        .dfg
        .inst_results(inst_id)
        .iter()
        .map(|result| func.dfg.value_ty(*result))
        .collect();
    simplify_key_with_facts(func, &inst.owned_key(&result_tys), facts)
}

pub(crate) fn simplify_key_with_facts(
    func: &Function,
    key: &OwnedInstKey,
    facts: &impl ExprFactProvider,
) -> SimplifiedInst {
    fold_key_with_facts(func, key, facts)
        .or_else(|| simplify_key_identities(func, key, facts))
        .map(|simplified| normalize_inst_results(key.result_tys(), simplified))
        .unwrap_or_else(|| SimplifiedInst::no_change(key.result_tys().len()))
}

fn simplify_key_identities(
    func: &Function,
    key: &OwnedInstKey,
    facts: &impl ExprFactProvider,
) -> Option<SimplifiedInst> {
    match key.kind() {
        InstClassKind::Unary(kind) => {
            let arg = key.unary_arg()?;
            if matches!(kind, UnaryInstKind::Snego) {
                return simplify_snego_zero(func, arg, facts);
            }

            let simplified = simplify_unary_with_same_inner(kind, arg, |arg, expected| {
                let Value::Inst { inst, .. } = func.dfg.value(arg) else {
                    return None;
                };
                let inner = func.dfg.inst(*inst);
                if inner.kind() != InstClassKind::Unary(expected) {
                    return None;
                }
                let values = inner.collect_values();
                let [arg] = values.as_slice() else {
                    return None;
                };
                Some(*arg)
            });
            (!simplified.is_no_change()).then(|| SimplifiedInst::one(simplified))
        }
        InstClassKind::Binary(kind) => {
            let (lhs, rhs) = key.binary_args()?;
            if let Some(simplified) =
                simplify_checked_binary_with_facts(func, kind, lhs, rhs, facts)
            {
                return Some(simplified);
            }

            let simplified = simplify_binary_with_facts(func, kind, lhs, rhs, facts);
            (!simplified.is_no_change()).then(|| SimplifiedInst::one(simplified))
        }
        InstClassKind::Cast(kind) => {
            let (arg, ty) = key.cast_arg_ty()?;
            let simplified = simplify_cast(func, kind, arg, ty);
            (!simplified.is_no_change()).then(|| SimplifiedInst::one(simplified))
        }
        InstClassKind::Phi | InstClassKind::Opaque => None,
    }
}

fn fold_key_with_facts(
    func: &Function,
    key: &OwnedInstKey,
    facts: &impl ExprFactProvider,
) -> Option<SimplifiedInst> {
    match key.kind() {
        InstClassKind::Unary(kind) => fold_unary_with_facts(key, kind, facts),
        InstClassKind::Binary(kind) => fold_binary_with_facts(func, key, kind, facts),
        InstClassKind::Cast(kind) => fold_cast_with_facts(key, kind, facts),
        InstClassKind::Opaque => fold_opaque_with_facts(key, facts),
        InstClassKind::Phi => None,
    }
}

fn fold_unary_with_facts(
    key: &OwnedInstKey,
    kind: UnaryInstKind,
    facts: &impl ExprFactProvider,
) -> Option<SimplifiedInst> {
    let arg = defined_imm(facts, key.unary_arg()?)?;
    let result_ty = *key.result_tys().first()?;
    let result = match kind {
        UnaryInstKind::Neg => SimplifiedInst::one(SimplifiedResult::Const(-arg)),
        UnaryInstKind::Snego => {
            let (value, overflow) = arg.overflowing_sneg();
            SimplifiedInst {
                results: smallvec![
                    SimplifiedResult::Const(value),
                    SimplifiedResult::Const(Immediate::from(overflow)),
                ],
            }
        }
        UnaryInstKind::Not => SimplifiedInst::one(SimplifiedResult::Const(!arg)),
        UnaryInstKind::IsZero => SimplifiedInst::one(SimplifiedResult::Const(fold_result_imm(
            arg.is_zero().into(),
            result_ty,
        )?)),
        UnaryInstKind::EvmClz => SimplifiedInst::one(SimplifiedResult::Const(fold_evm_clz(arg)?)),
    };
    Some(result)
}

fn fold_binary_with_facts(
    func: &Function,
    key: &OwnedInstKey,
    kind: BinaryInstKind,
    facts: &impl ExprFactProvider,
) -> Option<SimplifiedInst> {
    let (lhs, rhs) = key.binary_args()?;
    let result_ty = *key.result_tys().first()?;
    let result = match kind {
        BinaryInstKind::Add => {
            let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
            fold_result_imm(lhs + rhs, result_ty)?
        }
        BinaryInstKind::Uaddo => {
            return fold_checked_binary(facts, lhs, rhs, Immediate::overflowing_uadd);
        }
        BinaryInstKind::Uaddsat => {
            defined_imm(facts, lhs)?.saturating_uadd(defined_imm(facts, rhs)?)
        }
        BinaryInstKind::Saddo => {
            return fold_checked_binary(facts, lhs, rhs, Immediate::overflowing_sadd);
        }
        BinaryInstKind::Saddsat => {
            defined_imm(facts, lhs)?.saturating_sadd(defined_imm(facts, rhs)?)
        }
        BinaryInstKind::Mul => {
            let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
            fold_result_imm(lhs * rhs, result_ty)?
        }
        BinaryInstKind::Umulo => {
            return fold_checked_binary(facts, lhs, rhs, Immediate::overflowing_umul);
        }
        BinaryInstKind::Umulsat => {
            defined_imm(facts, lhs)?.saturating_umul(defined_imm(facts, rhs)?)
        }
        BinaryInstKind::Smulo => {
            return fold_checked_binary(facts, lhs, rhs, Immediate::overflowing_smul);
        }
        BinaryInstKind::Smulsat => {
            defined_imm(facts, lhs)?.saturating_smul(defined_imm(facts, rhs)?)
        }
        BinaryInstKind::Sub => {
            let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
            fold_result_imm(lhs - rhs, result_ty)?
        }
        BinaryInstKind::Usubo => {
            return fold_checked_binary(facts, lhs, rhs, Immediate::overflowing_usub);
        }
        BinaryInstKind::Usubsat => {
            defined_imm(facts, lhs)?.saturating_usub(defined_imm(facts, rhs)?)
        }
        BinaryInstKind::Ssubo => {
            return fold_checked_binary(facts, lhs, rhs, Immediate::overflowing_ssub);
        }
        BinaryInstKind::Ssubsat => {
            defined_imm(facts, lhs)?.saturating_ssub(defined_imm(facts, rhs)?)
        }
        BinaryInstKind::Sdiv => {
            fold_nonzero_word_binary(func, facts, lhs, rhs, result_ty, Immediate::sdiv)?
        }
        BinaryInstKind::Udiv => {
            fold_nonzero_word_binary(func, facts, lhs, rhs, result_ty, Immediate::udiv)?
        }
        BinaryInstKind::Umod => {
            fold_nonzero_word_binary(func, facts, lhs, rhs, result_ty, Immediate::urem)?
        }
        BinaryInstKind::Smod => {
            fold_nonzero_word_binary(func, facts, lhs, rhs, result_ty, Immediate::srem)?
        }
        BinaryInstKind::Lt => fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::lt)?,
        BinaryInstKind::Gt => fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::gt)?,
        BinaryInstKind::Slt => fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::slt)?,
        BinaryInstKind::Sgt => fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::sgt)?,
        BinaryInstKind::Le => fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::le)?,
        BinaryInstKind::Ge => fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::ge)?,
        BinaryInstKind::Sle => fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::sle)?,
        BinaryInstKind::Sge => fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::sge)?,
        BinaryInstKind::Eq => {
            fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::imm_eq)?
        }
        BinaryInstKind::Ne => {
            fold_word_binary(func, facts, lhs, rhs, result_ty, Immediate::imm_ne)?
        }
        BinaryInstKind::And => {
            let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
            fold_result_imm(lhs & rhs, result_ty)?
        }
        BinaryInstKind::Or => {
            let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
            fold_result_imm(lhs | rhs, result_ty)?
        }
        BinaryInstKind::Xor => {
            let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
            fold_result_imm(lhs ^ rhs, result_ty)?
        }
        BinaryInstKind::Shl => {
            fold_word_binary(func, facts, lhs, rhs, result_ty, |bits, value| {
                value << bits
            })?
        }
        BinaryInstKind::Shr => {
            fold_word_binary(func, facts, lhs, rhs, result_ty, |bits, value| {
                value >> bits
            })?
        }
        BinaryInstKind::Sar => {
            fold_word_binary(func, facts, lhs, rhs, result_ty, |bits, value| {
                value.ashr(bits)
            })?
        }
        BinaryInstKind::EvmUdiv => {
            fold_evm_div_rem(func, facts, lhs, rhs, result_ty, Immediate::udiv)?
        }
        BinaryInstKind::EvmSdiv => {
            fold_evm_div_rem(func, facts, lhs, rhs, result_ty, Immediate::sdiv)?
        }
        BinaryInstKind::EvmUdivo => {
            return fold_evm_overflow_div_rem(
                func,
                facts,
                lhs,
                rhs,
                result_ty,
                Immediate::udiv,
                |_| false,
            );
        }
        BinaryInstKind::EvmSdivo => {
            return fold_evm_overflow_div_rem(
                func,
                facts,
                lhs,
                rhs,
                result_ty,
                Immediate::sdiv,
                |lhs| lhs.overflowing_sneg().1,
            );
        }
        BinaryInstKind::EvmUmod => {
            fold_evm_div_rem(func, facts, lhs, rhs, result_ty, Immediate::urem)?
        }
        BinaryInstKind::EvmSmod => {
            fold_evm_div_rem(func, facts, lhs, rhs, result_ty, Immediate::srem)?
        }
        BinaryInstKind::EvmUmodo => {
            return fold_evm_overflow_div_rem(
                func,
                facts,
                lhs,
                rhs,
                result_ty,
                Immediate::urem,
                |_| false,
            );
        }
        BinaryInstKind::EvmSmodo => {
            return fold_evm_overflow_div_rem(
                func,
                facts,
                lhs,
                rhs,
                result_ty,
                Immediate::srem,
                |_| false,
            );
        }
        BinaryInstKind::EvmUaddsat
        | BinaryInstKind::EvmSaddsat
        | BinaryInstKind::EvmUsubsat
        | BinaryInstKind::EvmSsubsat
        | BinaryInstKind::EvmUmulsat
        | BinaryInstKind::EvmSmulsat => fold_evm_saturating(
            kind,
            defined_imm(facts, lhs)?,
            defined_imm(facts, rhs)?,
            key.extra_ty()?,
            result_ty,
        )?,
        BinaryInstKind::EvmExp => {
            simplify_evm_exp_known(known_value(facts, lhs), known_value(facts, rhs), result_ty)?
        }
        BinaryInstKind::EvmSignExtend => simplify_evm_signextend_known(
            known_value(facts, lhs),
            known_value(facts, rhs),
            result_ty,
        )?,
        BinaryInstKind::EvmByte => {
            simplify_evm_byte_known(known_value(facts, lhs), known_value(facts, rhs), result_ty)?
        }
    };
    Some(SimplifiedInst::one(SimplifiedResult::Const(result)))
}

fn fold_cast_with_facts(
    key: &OwnedInstKey,
    kind: CastInstKind,
    facts: &impl ExprFactProvider,
) -> Option<SimplifiedInst> {
    let (arg, ty) = key.cast_arg_ty()?;
    if !ty.is_integral() {
        return None;
    }

    let value = defined_imm(facts, arg)?;
    let result = match kind {
        CastInstKind::Sext => value.sext(ty),
        CastInstKind::Zext => value.zext(ty),
        CastInstKind::Trunc => value.trunc(ty),
        CastInstKind::Bitcast => value.bitcast(ty),
        CastInstKind::IntToPtr | CastInstKind::PtrToInt => {
            Immediate::from_i256(value.as_i256(), ty)
        }
    };
    Some(SimplifiedInst::one(SimplifiedResult::Const(result)))
}

fn fold_opaque_with_facts(
    key: &OwnedInstKey,
    facts: &impl ExprFactProvider,
) -> Option<SimplifiedInst> {
    let [lhs, rhs, modulus] = key.values() else {
        return None;
    };
    let op = match key.opcode_text() {
        "evm_add_mod" => EvmModOp::Add,
        "evm_mul_mod" => EvmModOp::Mul,
        _ => return None,
    };
    let result = simplify_evm_modop_known(
        known_value(facts, *lhs),
        known_value(facts, *rhs),
        known_value(facts, *modulus),
        *key.result_tys().first()?,
        op,
    )?;
    Some(SimplifiedInst::one(SimplifiedResult::Const(result)))
}

fn fold_checked_binary(
    facts: &impl ExprFactProvider,
    lhs: ValueId,
    rhs: ValueId,
    fold: fn(Immediate, Immediate) -> (Immediate, bool),
) -> Option<SimplifiedInst> {
    let (value, overflow) = fold(defined_imm(facts, lhs)?, defined_imm(facts, rhs)?);
    Some(SimplifiedInst {
        results: smallvec![
            SimplifiedResult::Const(value),
            SimplifiedResult::Const(Immediate::from(overflow)),
        ],
    })
}

fn fold_word_binary(
    func: &Function,
    facts: &impl ExprFactProvider,
    lhs: ValueId,
    rhs: ValueId,
    result_ty: Type,
    fold: impl FnOnce(Immediate, Immediate) -> Immediate,
) -> Option<Immediate> {
    let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
    fold_result_imm(fold(lhs, rhs), result_ty)
}

fn fold_nonzero_word_binary(
    func: &Function,
    facts: &impl ExprFactProvider,
    lhs: ValueId,
    rhs: ValueId,
    result_ty: Type,
    fold: impl FnOnce(Immediate, Immediate) -> Immediate,
) -> Option<Immediate> {
    let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
    (!rhs.is_zero()).then(|| fold_result_imm(fold(lhs, rhs), result_ty))?
}

fn fold_evm_div_rem(
    func: &Function,
    facts: &impl ExprFactProvider,
    lhs: ValueId,
    rhs: ValueId,
    result_ty: Type,
    fold: impl FnOnce(Immediate, Immediate) -> Immediate,
) -> Option<Immediate> {
    let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
    fold_result_imm(if rhs.is_zero() { rhs } else { fold(lhs, rhs) }, result_ty)
}

fn fold_evm_overflow_div_rem(
    func: &Function,
    facts: &impl ExprFactProvider,
    lhs: ValueId,
    rhs: ValueId,
    result_ty: Type,
    fold: impl FnOnce(Immediate, Immediate) -> Immediate,
    signed_overflow: impl FnOnce(Immediate) -> bool,
) -> Option<SimplifiedInst> {
    let (lhs, rhs) = word_binary_imms(func, facts, lhs, rhs, result_ty)?;
    let value = if rhs.is_zero() { rhs } else { fold(lhs, rhs) };
    let overflow = rhs.is_zero() || (rhs.is_all_one() && signed_overflow(lhs));
    Some(SimplifiedInst {
        results: smallvec![
            SimplifiedResult::Const(value),
            SimplifiedResult::Const(Immediate::from(overflow)),
        ],
    })
}

fn word_binary_imms(
    func: &Function,
    facts: &impl ExprFactProvider,
    lhs: ValueId,
    rhs: ValueId,
    result_ty: Type,
) -> Option<(Immediate, Immediate)> {
    let lhs = defined_imm(facts, lhs)?;
    let rhs = defined_imm(facts, rhs)?;
    if lhs.ty() == rhs.ty() {
        if lhs.ty() == Type::I1 && result_ty == Type::I256 {
            return Some((lhs.zext(Type::I256), rhs.zext(Type::I256)));
        }
        return Some((lhs, rhs));
    }
    if matches!(
        (lhs.ty(), rhs.ty()),
        (Type::I1, Type::I256) | (Type::I256, Type::I1)
    ) && func.dfg.ctx.size_of(result_ty).is_ok()
    {
        return Some((lhs.zext(Type::I256), rhs.zext(Type::I256)));
    }
    None
}

fn fold_result_imm(imm: Immediate, result_ty: Type) -> Option<Immediate> {
    if imm.ty() == result_ty {
        Some(imm)
    } else if imm.ty() == Type::I1 && result_ty == Type::I256 {
        Some(imm.zext(result_ty))
    } else {
        None
    }
}

fn fold_evm_saturating(
    kind: BinaryInstKind,
    lhs: Immediate,
    rhs: Immediate,
    sat_ty: Type,
    result_ty: Type,
) -> Option<Immediate> {
    let lhs = lhs.trunc(sat_ty);
    let rhs = rhs.trunc(sat_ty);

    match kind {
        BinaryInstKind::EvmUaddsat => Some(lhs.saturating_uadd(rhs).zext(result_ty)),
        BinaryInstKind::EvmSaddsat => Some(lhs.saturating_sadd(rhs).sext(result_ty)),
        BinaryInstKind::EvmUsubsat => Some(lhs.saturating_usub(rhs).zext(result_ty)),
        BinaryInstKind::EvmSsubsat => Some(lhs.saturating_ssub(rhs).sext(result_ty)),
        BinaryInstKind::EvmUmulsat => Some(lhs.saturating_umul(rhs).zext(result_ty)),
        BinaryInstKind::EvmSmulsat => Some(lhs.saturating_smul(rhs).sext(result_ty)),
        _ => None,
    }
}

fn simplify_snego_zero(
    func: &Function,
    arg: ValueId,
    facts: &impl ExprFactProvider,
) -> Option<SimplifiedInst> {
    let arg_ty = func.dfg.value_ty(arg);
    if !arg_ty.is_integral() {
        // `Immediate::zero` is only defined for integral types, and snego
        // itself is verified to take an integral operand.
        return None;
    }
    (defined_imm(facts, arg) == Some(Immediate::zero(arg_ty)))
        .then(|| checked_value_no_overflow(SimplifiedResult::Const(Immediate::zero(arg_ty))))
}

fn simplify_checked_binary_with_facts(
    func: &Function,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    facts: &impl ExprFactProvider,
) -> Option<SimplifiedInst> {
    if facts.may_be_undef(lhs) || facts.may_be_undef(rhs) {
        return None;
    }

    let ty = func.dfg.value_ty(lhs);
    if !ty.is_integral() {
        return None;
    }
    let zero = Immediate::zero(ty);
    let one = Immediate::one(ty);
    let lhs_imm = facts.known_imm(lhs);
    let rhs_imm = facts.known_imm(rhs);

    match kind {
        BinaryInstKind::Uaddo | BinaryInstKind::Saddo => {
            if rhs_imm == Some(zero) {
                Some(checked_value_no_overflow(SimplifiedResult::Copy(lhs)))
            } else if lhs_imm == Some(zero) {
                Some(checked_value_no_overflow(SimplifiedResult::Copy(rhs)))
            } else {
                None
            }
        }
        BinaryInstKind::Usubo | BinaryInstKind::Ssubo if rhs_imm == Some(zero) => {
            Some(checked_value_no_overflow(SimplifiedResult::Copy(lhs)))
        }
        BinaryInstKind::Umulo | BinaryInstKind::Smulo => {
            if lhs_imm == Some(zero) || rhs_imm == Some(zero) {
                Some(checked_value_no_overflow(SimplifiedResult::Const(zero)))
            } else if lhs_imm == Some(one) {
                Some(checked_value_no_overflow(SimplifiedResult::Copy(rhs)))
            } else if rhs_imm == Some(one) {
                Some(checked_value_no_overflow(SimplifiedResult::Copy(lhs)))
            } else {
                None
            }
        }
        BinaryInstKind::EvmUdivo | BinaryInstKind::EvmSdivo if rhs_imm == Some(one) => {
            Some(checked_value_no_overflow(SimplifiedResult::Copy(lhs)))
        }
        BinaryInstKind::EvmUmodo | BinaryInstKind::EvmSmodo if rhs_imm == Some(one) => {
            Some(checked_value_no_overflow(SimplifiedResult::Const(zero)))
        }
        BinaryInstKind::Uaddsat | BinaryInstKind::Saddsat => {
            simplify_saturating_add(lhs, rhs, lhs_imm, rhs_imm, zero)
        }
        BinaryInstKind::Usubsat | BinaryInstKind::Ssubsat => {
            simplify_saturating_sub(kind, lhs, lhs_imm, rhs_imm, zero)
        }
        BinaryInstKind::Umulsat | BinaryInstKind::Smulsat => {
            simplify_saturating_mul(lhs, rhs, lhs_imm, rhs_imm, zero, one)
        }
        _ => None,
    }
}

fn simplify_saturating_add(
    lhs: ValueId,
    rhs: ValueId,
    lhs_imm: Option<Immediate>,
    rhs_imm: Option<Immediate>,
    zero: Immediate,
) -> Option<SimplifiedInst> {
    if rhs_imm == Some(zero) {
        Some(SimplifiedInst::one(SimplifiedResult::Copy(lhs)))
    } else if lhs_imm == Some(zero) {
        Some(SimplifiedInst::one(SimplifiedResult::Copy(rhs)))
    } else {
        None
    }
}

fn simplify_saturating_sub(
    kind: BinaryInstKind,
    lhs: ValueId,
    lhs_imm: Option<Immediate>,
    rhs_imm: Option<Immediate>,
    zero: Immediate,
) -> Option<SimplifiedInst> {
    if rhs_imm == Some(zero) {
        Some(SimplifiedInst::one(SimplifiedResult::Copy(lhs)))
    } else if kind == BinaryInstKind::Usubsat && lhs_imm == Some(zero) {
        Some(SimplifiedInst::one(SimplifiedResult::Const(zero)))
    } else {
        None
    }
}

fn simplify_saturating_mul(
    lhs: ValueId,
    rhs: ValueId,
    lhs_imm: Option<Immediate>,
    rhs_imm: Option<Immediate>,
    zero: Immediate,
    one: Immediate,
) -> Option<SimplifiedInst> {
    if lhs_imm == Some(zero) || rhs_imm == Some(zero) {
        Some(SimplifiedInst::one(SimplifiedResult::Const(zero)))
    } else if lhs_imm == Some(one) {
        Some(SimplifiedInst::one(SimplifiedResult::Copy(rhs)))
    } else if rhs_imm == Some(one) {
        Some(SimplifiedInst::one(SimplifiedResult::Copy(lhs)))
    } else {
        None
    }
}

fn checked_value_no_overflow(value: SimplifiedResult) -> SimplifiedInst {
    SimplifiedInst {
        results: smallvec![value, SimplifiedResult::Const(Immediate::I1(false)),],
    }
}

fn normalize_inst_results(result_tys: &[Type], simplified: SimplifiedInst) -> SimplifiedInst {
    SimplifiedInst {
        results: result_tys
            .iter()
            .enumerate()
            .map(|(idx, &ty)| normalize_result(simplified.result(idx), ty))
            .collect(),
    }
}

fn normalize_result(result: SimplifiedResult, ty: Type) -> SimplifiedResult {
    match result {
        SimplifiedResult::Const(imm) => normalize_imm_for_type(imm, ty)
            .map(SimplifiedResult::Const)
            .unwrap_or(SimplifiedResult::NoChange),
        SimplifiedResult::Copy(value) => SimplifiedResult::Copy(value),
        SimplifiedResult::NoChange => SimplifiedResult::NoChange,
    }
}

fn normalize_imm_for_type(imm: Immediate, ty: Type) -> Option<Immediate> {
    if !ty.is_integral() {
        None
    } else if imm.ty() == ty {
        Some(imm)
    } else if imm.ty() == Type::I1 {
        Some(imm.zext(ty))
    } else {
        Some(Immediate::from_i256(imm.as_i256(), ty))
    }
}

fn known_value(facts: &impl ExprFactProvider, value: ValueId) -> KnownValueFact {
    KnownValueFact {
        imm: facts.known_imm(value),
        may_be_undef: facts.may_be_undef(value),
    }
}

fn defined_imm(facts: &impl ExprFactProvider, value: ValueId) -> Option<Immediate> {
    (!facts.may_be_undef(value))
        .then(|| facts.known_imm(value))
        .flatten()
}

pub(crate) fn simplify_unary_with_same_inner(
    kind: UnaryInstKind,
    arg: ValueId,
    same_inner_arg: impl Fn(ValueId, UnaryInstKind) -> Option<ValueId>,
) -> SimplifiedResult {
    match kind {
        UnaryInstKind::Not | UnaryInstKind::Neg => same_inner_arg(arg, kind)
            .map(SimplifiedResult::Copy)
            .unwrap_or(SimplifiedResult::NoChange),
        UnaryInstKind::Snego | UnaryInstKind::IsZero | UnaryInstKind::EvmClz => {
            SimplifiedResult::NoChange
        }
    }
}

pub(crate) fn simplify_binary_with_facts(
    func: &Function,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    facts: &impl ExprFactProvider,
) -> SimplifiedResult {
    let ty = func.dfg.value_ty(lhs);
    let lhs_imm = facts.known_imm(lhs);
    let rhs_imm = facts.known_imm(rhs);
    let lhs_defined = !facts.may_be_undef(lhs);
    let rhs_defined = !facts.may_be_undef(rhs);

    match kind {
        BinaryInstKind::Add => {
            if lhs_defined && lhs_imm.is_some_and(Immediate::is_zero) {
                return SimplifiedResult::Copy(rhs);
            }
            if rhs_defined && rhs_imm.is_some_and(Immediate::is_zero) {
                return SimplifiedResult::Copy(lhs);
            }
        }
        BinaryInstKind::Sub => {
            if ty.is_integral() && facts.same_non_undef(lhs, rhs) {
                return SimplifiedResult::Const(Immediate::zero(ty));
            }
            if rhs_defined && rhs_imm == Some(Immediate::zero(ty)) {
                return SimplifiedResult::Copy(lhs);
            }
        }
        BinaryInstKind::Mul => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                let one = Immediate::one(ty);
                if lhs_defined && rhs_defined && (lhs_imm == Some(zero) || rhs_imm == Some(zero)) {
                    return SimplifiedResult::Const(zero);
                }
                if lhs_defined && lhs_imm == Some(one) {
                    return SimplifiedResult::Copy(rhs);
                }
                if rhs_defined && rhs_imm == Some(one) {
                    return SimplifiedResult::Copy(lhs);
                }
            }
        }
        BinaryInstKind::And => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                let all_one = Immediate::all_one(ty);
                if lhs_defined && rhs_defined && (lhs_imm == Some(zero) || rhs_imm == Some(zero)) {
                    return SimplifiedResult::Const(zero);
                }
                if lhs_defined && lhs_imm == Some(all_one) {
                    return SimplifiedResult::Copy(rhs);
                }
                if rhs_defined && rhs_imm == Some(all_one) {
                    return SimplifiedResult::Copy(lhs);
                }

                if let Some(copy) = simplify_and_copy_with_facts(func, lhs, rhs, facts)
                    .or_else(|| simplify_and_copy_with_facts(func, rhs, lhs, facts))
                {
                    return SimplifiedResult::Copy(copy);
                }
            }
            if facts.same_non_undef(lhs, rhs) {
                return SimplifiedResult::Copy(lhs);
            }
        }
        BinaryInstKind::Or => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                let all_one = Immediate::all_one(ty);
                if lhs_defined
                    && rhs_defined
                    && (lhs_imm == Some(all_one) || rhs_imm == Some(all_one))
                {
                    return SimplifiedResult::Const(all_one);
                }
                if lhs_defined && lhs_imm == Some(zero) {
                    return SimplifiedResult::Copy(rhs);
                }
                if rhs_defined && rhs_imm == Some(zero) {
                    return SimplifiedResult::Copy(lhs);
                }

                if let Some(copy) = simplify_or_copy_with_facts(func, lhs, rhs, facts)
                    .or_else(|| simplify_or_copy_with_facts(func, rhs, lhs, facts))
                {
                    return SimplifiedResult::Copy(copy);
                }
            }
            if facts.same_non_undef(lhs, rhs) {
                return SimplifiedResult::Copy(lhs);
            }
        }
        BinaryInstKind::Xor => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                if lhs_defined && lhs_imm == Some(zero) {
                    return SimplifiedResult::Copy(rhs);
                }
                if rhs_defined && rhs_imm == Some(zero) {
                    return SimplifiedResult::Copy(lhs);
                }
                if facts.same_non_undef(lhs, rhs) {
                    return SimplifiedResult::Const(zero);
                }
            }
        }
        BinaryInstKind::Udiv
        | BinaryInstKind::Sdiv
        | BinaryInstKind::EvmUdiv
        | BinaryInstKind::EvmSdiv => {
            if ty.is_integral() && rhs_defined && rhs_imm == Some(Immediate::one(ty)) {
                return SimplifiedResult::Copy(lhs);
            }
        }
        BinaryInstKind::Umod
        | BinaryInstKind::Smod
        | BinaryInstKind::EvmUmod
        | BinaryInstKind::EvmSmod => {
            if ty.is_integral() && lhs_defined && rhs_defined && rhs_imm == Some(Immediate::one(ty))
            {
                return SimplifiedResult::Const(Immediate::zero(ty));
            }
        }
        BinaryInstKind::Eq => {
            if let Some(ZextI1CompareRewrite::Copy(value)) =
                simplify_zext_i1_compare(func, kind, lhs, rhs, |v| defined_imm(facts, v))
            {
                return SimplifiedResult::Copy(value);
            }
            if facts.same_non_undef(lhs, rhs) {
                return SimplifiedResult::Const(Immediate::one(Type::I1));
            }
            if !facts.may_be_undef(lhs)
                && !facts.may_be_undef(rhs)
                && has_conflicting_known_bits(
                    facts.known_bits(func, lhs),
                    facts.known_bits(func, rhs),
                    ty,
                )
            {
                return SimplifiedResult::Const(Immediate::zero(Type::I1));
            }
        }
        BinaryInstKind::Ne => {
            if let Some(ZextI1CompareRewrite::Copy(value)) =
                simplify_zext_i1_compare(func, kind, lhs, rhs, |v| defined_imm(facts, v))
            {
                return SimplifiedResult::Copy(value);
            }
            if facts.same_non_undef(lhs, rhs) {
                return SimplifiedResult::Const(Immediate::zero(Type::I1));
            }
            if !facts.may_be_undef(lhs)
                && !facts.may_be_undef(rhs)
                && has_conflicting_known_bits(
                    facts.known_bits(func, lhs),
                    facts.known_bits(func, rhs),
                    ty,
                )
            {
                return SimplifiedResult::Const(Immediate::one(Type::I1));
            }
        }
        BinaryInstKind::Gt | BinaryInstKind::Lt | BinaryInstKind::Ge | BinaryInstKind::Le => {
            if !ty.is_integral() {
                return SimplifiedResult::NoChange;
            }
            if facts.same_non_undef(lhs, rhs) {
                return SimplifiedResult::Const(Immediate::I1(matches!(
                    kind,
                    BinaryInstKind::Ge | BinaryInstKind::Le
                )));
            }

            let zero = Immediate::zero(ty);
            match kind {
                _ if !lhs_defined || !rhs_defined => {}
                BinaryInstKind::Gt if lhs_imm == Some(zero) => {
                    return SimplifiedResult::Const(Immediate::zero(Type::I1));
                }
                BinaryInstKind::Lt if rhs_imm == Some(zero) => {
                    return SimplifiedResult::Const(Immediate::zero(Type::I1));
                }
                BinaryInstKind::Ge if rhs_imm == Some(zero) => {
                    return SimplifiedResult::Const(Immediate::one(Type::I1));
                }
                BinaryInstKind::Le if lhs_imm == Some(zero) => {
                    return SimplifiedResult::Const(Immediate::one(Type::I1));
                }
                _ => {}
            }
        }
        BinaryInstKind::Shl | BinaryInstKind::Shr | BinaryInstKind::Sar => {
            let value_ty = func.dfg.value_ty(rhs);
            let value_zero = Immediate::zero(value_ty);
            if lhs_defined && rhs_defined && rhs_imm == Some(value_zero) {
                return SimplifiedResult::Const(value_zero);
            }
            if lhs_defined && lhs_imm.is_some_and(Immediate::is_zero) {
                return SimplifiedResult::Copy(rhs);
            }
        }
        BinaryInstKind::EvmSignExtend => {
            if let Some(result) = simplify_evm_signextend_known(
                KnownValueFact {
                    imm: lhs_imm,
                    may_be_undef: facts.may_be_undef(lhs),
                },
                KnownValueFact {
                    imm: rhs_imm,
                    may_be_undef: facts.may_be_undef(rhs),
                },
                ty,
            ) {
                return SimplifiedResult::Const(result);
            }
            if let Some(value) = simplify_evm_signextend_copy_with_facts(func, lhs, rhs, facts) {
                return SimplifiedResult::Copy(value);
            }
        }
        BinaryInstKind::Slt | BinaryInstKind::Sgt => {
            if facts.same_non_undef(lhs, rhs) {
                return SimplifiedResult::Const(Immediate::I1(false));
            }
        }
        BinaryInstKind::Sle | BinaryInstKind::Sge => {
            if facts.same_non_undef(lhs, rhs) {
                return SimplifiedResult::Const(Immediate::I1(true));
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
        | BinaryInstKind::EvmUdivo
        | BinaryInstKind::EvmSdivo
        | BinaryInstKind::EvmUmodo
        | BinaryInstKind::EvmSmodo
        | BinaryInstKind::EvmUaddsat
        | BinaryInstKind::EvmSaddsat
        | BinaryInstKind::EvmUsubsat
        | BinaryInstKind::EvmSsubsat
        | BinaryInstKind::EvmUmulsat
        | BinaryInstKind::EvmSmulsat => {}
        BinaryInstKind::EvmExp => {
            if let Some(result) =
                simplify_evm_exp_known(known_value(facts, lhs), known_value(facts, rhs), ty)
            {
                return SimplifiedResult::Const(result);
            }
        }
        BinaryInstKind::EvmByte => {
            if let Some(result) =
                simplify_evm_byte_known(known_value(facts, lhs), known_value(facts, rhs), ty)
            {
                return SimplifiedResult::Const(result);
            }
        }
    }

    SimplifiedResult::NoChange
}

#[allow(dead_code)]
pub(crate) fn simplify_binary_with_known_imm(
    func: &Function,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    known_imm: impl Fn(ValueId) -> Option<Immediate>,
    same_value: impl Fn(ValueId, ValueId) -> bool,
) -> SimplifiedResult {
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

        fn may_be_undef(&self, v: ValueId) -> bool {
            (self.known_imm)(v).is_none()
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
) -> SimplifiedResult {
    if func.dfg.value_ty(from) == ty {
        return SimplifiedResult::Copy(from);
    }

    if matches!(kind, CastInstKind::Trunc)
        && let Some((inst, _)) = func.dfg.value_inst_result(from)
    {
        if let Some(zext) = downcast::<&cast::Zext>(func.inst_set(), func.dfg.inst(inst)) {
            let src = *zext.from();
            if func.dfg.value_ty(src) == ty {
                return SimplifiedResult::Copy(src);
            }
        }

        if let Some(sext) = downcast::<&cast::Sext>(func.inst_set(), func.dfg.inst(inst)) {
            let src = *sext.from();
            if func.dfg.value_ty(src) == ty {
                return SimplifiedResult::Copy(src);
            }
        }
    }

    SimplifiedResult::NoChange
}

pub(crate) fn canonicalize_cast_chain(
    func: &Function,
    kind: CastInstKind,
    from: ValueId,
    ty: Type,
) -> Option<(CastInstKind, ValueId, Type)> {
    let (inst, _) = func.dfg.value_inst_result(from)?;
    let InstClassKind::Cast(inner_kind) = func.dfg.inst(inst).kind() else {
        return None;
    };
    let values = func.dfg.inst(inst).collect_values();
    let [inner_arg] = values.as_slice() else {
        return None;
    };
    let inner_ty = func.dfg.value_ty(from);
    let src_ty = func.dfg.value_ty(*inner_arg);
    let src_bits = integral_bit_width(src_ty)?;
    let inner_bits = integral_bit_width(inner_ty)?;
    let dst_bits = integral_bit_width(ty)?;

    match (kind, inner_kind) {
        (CastInstKind::Zext, CastInstKind::Zext) | (CastInstKind::Sext, CastInstKind::Sext)
            if src_bits < dst_bits && inner_bits < dst_bits =>
        {
            Some((kind, *inner_arg, ty))
        }
        (CastInstKind::Trunc, CastInstKind::Trunc)
            if src_bits > dst_bits && inner_bits > dst_bits =>
        {
            Some((kind, *inner_arg, ty))
        }
        (CastInstKind::Trunc, CastInstKind::Zext | CastInstKind::Sext)
            if src_bits < dst_bits && dst_bits < inner_bits =>
        {
            Some((inner_kind, *inner_arg, ty))
        }
        _ => None,
    }
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
    .or_else(|| simplify_low_mask_copy_with_range(func, value, keep_mask, facts))
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

fn simplify_evm_signextend_copy_with_facts(
    func: &Function,
    byte: ValueId,
    value: ValueId,
    facts: &impl ExprFactProvider,
) -> Option<ValueId> {
    let ty = func.dfg.value_ty(value);
    let byte_imm = imm_to_u256(facts.known_imm(byte)?);
    if !ty.is_integral() || facts.may_be_undef(byte) {
        return None;
    }
    if byte_imm >= U256::from(32u8) {
        return Some(value);
    }

    let width = integral_bit_width(ty)?;
    let sign_width = (byte_imm.as_usize() + 1) * 8;
    if sign_width >= width {
        return Some(value);
    }
    if facts.may_be_undef(value) {
        return None;
    }

    let low_mask = (U256::one() << sign_width) - U256::one();
    let sign_mask = U256::one() << (sign_width - 1);
    let high_mask = type_mask(ty) & !low_mask;
    let known = facts.known_bits(func, value);
    let already_sign_extended = known.all_zero_in(sign_mask) && known.all_zero_in(high_mask)
        || known.all_one_in(sign_mask) && known.all_one_in(high_mask);
    already_sign_extended.then_some(value)
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

fn simplify_low_mask_copy_with_range(
    func: &Function,
    value: ValueId,
    keep_mask: U256,
    facts: &impl ExprFactProvider,
) -> Option<ValueId> {
    let ty = func.dfg.value_ty(value);
    if !ty.is_integral() || !is_low_ones_mask(keep_mask, ty) {
        return None;
    }

    let range = facts.range(value)?;
    (range.unsigned.hi <= keep_mask).then_some(value)
}

fn is_low_ones_mask(mask: U256, ty: Type) -> bool {
    let type_mask = type_mask(ty);
    mask == type_mask || mask & (mask + U256::one()) == U256::zero()
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        I256, Immediate, Linkage, Signature, Type, U256, builder::test_util::test_isa, isa::Isa,
        module::ModuleCtx,
    };
    use sonatina_parser::parse_module;

    use super::*;
    use crate::analysis::known_bits::{KnownBits, low_mask};

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

        assert_eq!(simplified, SimplifiedResult::Copy(ValueId::from_u32(7)));
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
        assert_eq!(simplified, SimplifiedResult::Copy(value));
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
        assert_eq!(simplified, SimplifiedResult::Copy(value));
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
        assert_eq!(simplified, SimplifiedResult::Copy(value));
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
            SimplifiedResult::Const(Immediate::I1(false))
        );
        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::Ne, lhs, rhs, &facts),
            SimplifiedResult::Const(Immediate::I1(true))
        );
    }

    #[test]
    fn simplify_binary_with_facts_folds_unsigned_zero_bound_compares() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new_single("f", Linkage::Private, &[Type::I256], Type::I1);
        let mut func = Function::new(&ctx, &sig);
        let value = func.arg_values[0];
        let zero = func.dfg.make_imm_value(Immediate::zero(Type::I256));
        let facts = MockFacts {
            known_bits: Default::default(),
            known_imm: [(zero, Immediate::zero(Type::I256))].into_iter().collect(),
            may_be_undef: Default::default(),
        };

        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::Gt, zero, value, &facts),
            SimplifiedResult::Const(Immediate::I1(false))
        );
        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::Lt, value, zero, &facts),
            SimplifiedResult::Const(Immediate::I1(false))
        );
        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::Ge, value, zero, &facts),
            SimplifiedResult::Const(Immediate::I1(true))
        );
        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::Le, zero, value, &facts),
            SimplifiedResult::Const(Immediate::I1(true))
        );
        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::Sgt, zero, value, &facts),
            SimplifiedResult::NoChange
        );
    }

    #[test]
    fn simplify_binary_with_facts_preserves_undef_in_unsigned_zero_bound_compares() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new_single("f", Linkage::Private, &[Type::I256], Type::I1);
        let mut func = Function::new(&ctx, &sig);
        let value = func.arg_values[0];
        let zero = func.dfg.make_imm_value(Immediate::zero(Type::I256));
        let facts = MockFacts {
            known_bits: Default::default(),
            known_imm: [(zero, Immediate::zero(Type::I256))].into_iter().collect(),
            may_be_undef: [(value, true)].into_iter().collect(),
        };

        for (kind, lhs, rhs) in [
            (BinaryInstKind::Gt, zero, value),
            (BinaryInstKind::Lt, value, zero),
            (BinaryInstKind::Ge, value, zero),
            (BinaryInstKind::Le, zero, value),
        ] {
            assert_eq!(
                simplify_binary_with_facts(&func, kind, lhs, rhs, &facts),
                SimplifiedResult::NoChange
            );
        }
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
        assert_eq!(simplified, SimplifiedResult::NoChange);
    }

    #[test]
    fn simplify_binary_with_facts_preserves_undef_through_absorbing_identities() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new_single("f", Linkage::Private, &[Type::I256], Type::I256);
        let mut func = Function::new(&ctx, &sig);
        let value = func.arg_values[0];
        let zero = func.dfg.make_imm_value(Immediate::zero(Type::I256));
        let one = func.dfg.make_imm_value(Immediate::one(Type::I256));
        let all_one = func.dfg.make_imm_value(Immediate::all_one(Type::I256));
        let facts = MockFacts {
            known_bits: Default::default(),
            known_imm: [
                (zero, Immediate::zero(Type::I256)),
                (one, Immediate::one(Type::I256)),
                (all_one, Immediate::all_one(Type::I256)),
            ]
            .into_iter()
            .collect(),
            may_be_undef: [(value, true)].into_iter().collect(),
        };

        for (kind, lhs, rhs) in [
            (BinaryInstKind::Mul, value, zero),
            (BinaryInstKind::And, value, zero),
            (BinaryInstKind::Or, value, all_one),
            (BinaryInstKind::Umod, value, one),
        ] {
            assert_eq!(
                simplify_binary_with_facts(&func, kind, lhs, rhs, &facts),
                SimplifiedResult::NoChange
            );
        }
    }

    #[test]
    fn simplify_inst_with_facts_handles_checked_add_results() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i256) {
    block0:
        (v1.i256, v2.i1) = uaddo v0 0.i256;
        return;
}
"#;
        let module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let inst = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find(|&inst| {
                    matches!(
                        func.dfg.inst(inst).kind(),
                        InstClassKind::Binary(BinaryInstKind::Uaddo)
                    )
                })
                .expect("test function should contain a uaddo instruction");
            let values = func.dfg.inst(inst).collect_values();
            let [arg, zero] = values.as_slice() else {
                panic!("uaddo should have two operands");
            };
            let facts = MockFacts {
                known_bits: Default::default(),
                known_imm: [(*zero, Immediate::zero(Type::I256))].into_iter().collect(),
                may_be_undef: Default::default(),
            };
            assert_eq!(
                simplify_inst_with_facts(func, inst, &facts)
                    .results
                    .as_slice(),
                &[
                    SimplifiedResult::Copy(*arg),
                    SimplifiedResult::Const(Immediate::I1(false)),
                ]
            );

            let facts = MockFacts {
                known_bits: Default::default(),
                known_imm: [(*zero, Immediate::zero(Type::I256))].into_iter().collect(),
                may_be_undef: [(*arg, true)].into_iter().collect(),
            };
            assert_eq!(
                simplify_inst_with_facts(func, inst, &facts)
                    .results
                    .as_slice(),
                &[SimplifiedResult::NoChange, SimplifiedResult::NoChange]
            );
        });
    }

    #[test]
    fn fold_evm_signextend_matches_evm_sign_extension() {
        let ty = Type::I256;
        assert_eq!(
            fold_evm_signextend(
                Immediate::zero(ty),
                Immediate::from_i256(I256::from(0x80u16), ty),
            ),
            Some(Immediate::from_i256(I256::from(-128i16), ty))
        );
        assert_eq!(
            fold_evm_signextend(
                Immediate::from_i256(I256::from(32u8), ty),
                Immediate::from_i256(I256::from(0x80u16), ty),
            ),
            Some(Immediate::from_i256(I256::from(0x80u16), ty))
        );
    }

    #[test]
    fn simplify_binary_with_facts_folds_evm_signextend_identities() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new_single("f", Linkage::Private, &[Type::I256], Type::I256);
        let mut func = Function::new(&ctx, &sig);
        let value = func.arg_values[0];
        let byte32 = func
            .dfg
            .make_imm_value(Immediate::from_i256(I256::from(32u8), Type::I256));
        let facts = MockFacts {
            known_bits: Default::default(),
            known_imm: [(byte32, Immediate::from_i256(I256::from(32u8), Type::I256))]
                .into_iter()
                .collect(),
            may_be_undef: Default::default(),
        };

        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::EvmSignExtend, byte32, value, &facts),
            SimplifiedResult::Copy(value)
        );

        let byte0 = func.dfg.make_imm_value(Immediate::zero(Type::I256));
        let facts = MockFacts {
            known_bits: [(
                value,
                KnownBits::normalized(
                    Type::I256,
                    type_mask(Type::I256) & !low_mask(7),
                    U256::zero(),
                ),
            )]
            .into_iter()
            .collect(),
            known_imm: [(byte0, Immediate::zero(Type::I256))].into_iter().collect(),
            may_be_undef: Default::default(),
        };

        assert_eq!(
            simplify_binary_with_facts(&func, BinaryInstKind::EvmSignExtend, byte0, value, &facts),
            SimplifiedResult::Copy(value)
        );
    }

    #[test]
    fn simplify_evm_signextend_known_blocks_maybe_undef_zero_fold() {
        let ty = Type::I256;
        assert_eq!(
            simplify_evm_signextend_known(
                KnownValueFact {
                    imm: None,
                    may_be_undef: true,
                },
                KnownValueFact {
                    imm: Some(Immediate::zero(ty)),
                    may_be_undef: false,
                },
                ty,
            ),
            None
        );
        assert_eq!(
            simplify_evm_signextend_known(
                KnownValueFact {
                    imm: None,
                    may_be_undef: false,
                },
                KnownValueFact {
                    imm: Some(Immediate::zero(ty)),
                    may_be_undef: false,
                },
                ty,
            ),
            Some(Immediate::zero(ty))
        );
    }

    #[test]
    fn simplify_evm_exp_known_blocks_maybe_undef_one_sided_folds() {
        let ty = Type::I256;

        assert_eq!(
            simplify_evm_exp_known(
                KnownValueFact {
                    imm: None,
                    may_be_undef: true,
                },
                KnownValueFact {
                    imm: Some(Immediate::zero(ty)),
                    may_be_undef: false,
                },
                ty,
            ),
            None
        );
        assert_eq!(
            simplify_evm_exp_known(
                KnownValueFact {
                    imm: Some(Immediate::one(ty)),
                    may_be_undef: false,
                },
                KnownValueFact {
                    imm: None,
                    may_be_undef: true,
                },
                ty,
            ),
            None
        );
        assert_eq!(
            simplify_evm_exp_known(
                KnownValueFact {
                    imm: Some(Immediate::one(ty)),
                    may_be_undef: false,
                },
                KnownValueFact {
                    imm: None,
                    may_be_undef: false,
                },
                ty,
            ),
            Some(Immediate::one(ty))
        );
    }

    #[test]
    fn simplify_evm_one_sided_helpers_block_maybe_undef_ignored_operands() {
        let ty = Type::I256;

        assert_eq!(
            simplify_evm_modop_known(
                KnownValueFact {
                    imm: None,
                    may_be_undef: true,
                },
                KnownValueFact {
                    imm: Some(Immediate::from_i256(I256::from(7), ty)),
                    may_be_undef: false,
                },
                KnownValueFact {
                    imm: Some(Immediate::zero(ty)),
                    may_be_undef: false,
                },
                ty,
                EvmModOp::Add,
            ),
            None
        );
        assert_eq!(
            simplify_evm_byte_known(
                KnownValueFact {
                    imm: None,
                    may_be_undef: true,
                },
                KnownValueFact {
                    imm: Some(Immediate::zero(ty)),
                    may_be_undef: false,
                },
                ty,
            ),
            None
        );
        assert_eq!(
            simplify_evm_byte_known(
                KnownValueFact {
                    imm: None,
                    may_be_undef: false,
                },
                KnownValueFact {
                    imm: Some(Immediate::zero(ty)),
                    may_be_undef: false,
                },
                ty,
            ),
            Some(Immediate::zero(ty))
        );
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
            SimplifiedResult::Copy(arg)
        );
    }
}
