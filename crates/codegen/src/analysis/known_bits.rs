use std::collections::VecDeque;
#[cfg(test)]
use std::{
    cell::Cell,
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
};

use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    Function, Immediate, Type, U256, Value, ValueId,
    inst::{BinaryInstKind, CastInstKind, InstClassKind, UnaryInstKind},
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct KnownBits {
    pub known_zero: U256,
    pub known_one: U256,
}

impl KnownBits {
    pub fn unknown(ty: Type) -> Self {
        if !supports_known_bits(ty) {
            return Self::default();
        }

        Self::normalized(ty, U256::zero(), U256::zero())
    }

    pub fn from_imm(imm: Immediate) -> Self {
        let ty = imm.ty();
        let ones = imm.as_i256().to_u256() & type_mask(ty);
        Self::normalized(ty, !ones, ones)
    }

    pub fn exact_imm(self, ty: Type) -> Option<Immediate> {
        if !supports_known_bits(ty) {
            return None;
        }

        let mask = type_mask(ty);
        (((self.known_zero | self.known_one) & mask) == mask)
            .then(|| Immediate::from_i256((self.known_one & mask).into(), ty))
    }

    pub fn all_zero_in(self, mask: U256) -> bool {
        (self.known_zero & mask) == mask
    }

    pub fn all_one_in(self, mask: U256) -> bool {
        (self.known_one & mask) == mask
    }

    pub fn fits_in_low_bits(self, bits: u16, ty: Type) -> bool {
        self.all_zero_in(type_mask(ty) & !low_mask(bits))
    }

    pub(crate) fn normalized(ty: Type, known_zero: U256, known_one: U256) -> Self {
        let mask = type_mask(ty);
        let known_one = known_one & mask;
        let known_zero = (known_zero & mask) | !mask;
        debug_assert_eq!(known_zero & known_one, U256::zero());
        Self {
            known_zero,
            known_one,
        }
    }

    fn exact_bool(value: bool) -> Self {
        if value {
            Self {
                known_zero: !U256::one(),
                known_one: U256::one(),
            }
        } else {
            Self {
                known_zero: !U256::zero(),
                known_one: U256::zero(),
            }
        }
    }

    fn meet(self, other: Self, ty: Type) -> Self {
        if !supports_known_bits(ty) {
            return Self::unknown(ty);
        }

        Self::normalized(
            ty,
            self.known_zero & other.known_zero,
            self.known_one & other.known_one,
        )
    }
}

pub struct KnownBitsQuery {
    known: SecondaryMap<ValueId, KnownBits>,
    value_tys: SecondaryMap<ValueId, Option<Type>>,
    immediates: SecondaryMap<ValueId, Option<Immediate>>,
}

#[cfg(test)]
thread_local! {
    static TEST_NEW_COUNTER: Cell<Option<usize>> = const { Cell::new(None) };
}

impl KnownBitsQuery {
    pub fn new(func: &Function) -> Self {
        #[cfg(test)]
        TEST_NEW_COUNTER.with(|counter| {
            if let Some(count) = counter.get() {
                counter.set(Some(count + 1));
            }
        });

        let mut query = Self {
            known: SecondaryMap::default(),
            value_tys: SecondaryMap::default(),
            immediates: SecondaryMap::default(),
        };
        query.capture_value_metadata(func);
        query.solve(func);
        query
    }

    pub fn for_value(&self, func: &Function, value: ValueId) -> KnownBits {
        self.known_of(func, value)
    }

    pub fn is_known_zero(&self, func: &Function, value: ValueId) -> bool {
        let ty = self.value_ty(func, value);
        supports_known_bits(ty) && self.for_value(func, value).all_zero_in(type_mask(ty))
    }

    pub fn is_known_nonzero(&self, func: &Function, value: ValueId) -> bool {
        let ty = self.value_ty(func, value);
        supports_known_bits(ty)
            && (self.for_value(func, value).known_one & type_mask(ty)) != U256::zero()
    }

    pub fn fits_in_low_bits(&self, func: &Function, value: ValueId, bits: u16) -> bool {
        let ty = self.value_ty(func, value);
        supports_known_bits(ty) && self.for_value(func, value).fits_in_low_bits(bits, ty)
    }

    pub fn has_conflicting_known_bits(&self, func: &Function, lhs: ValueId, rhs: ValueId) -> bool {
        let ty = self.value_ty(func, lhs);
        debug_assert_eq!(ty, self.value_ty(func, rhs));
        has_conflicting_known_bits(self.for_value(func, lhs), self.for_value(func, rhs), ty)
    }

    fn capture_value_metadata(&mut self, func: &Function) {
        for value in func.dfg.value_ids() {
            self.value_tys[value] = Some(func.dfg.value_ty(value));
            self.immediates[value] = func.dfg.value_imm(value);
        }
    }

    fn solve(&mut self, func: &Function) {
        let values: Vec<_> = func.dfg.value_ids().collect();
        let mut dependents = SecondaryMap::<ValueId, Vec<ValueId>>::default();
        let mut queued = SecondaryMap::<ValueId, bool>::default();
        let mut worklist = VecDeque::new();

        for value in values {
            if let Value::Inst { inst, .. } = func.dfg.value(value) {
                for used in func.dfg.inst(*inst).collect_values() {
                    dependents[used].push(value);
                }
            }

            self.known[value] = self.seed_known_bits(func, value);
            queued[value] = true;
            worklist.push_back(value);
        }

        while let Some(value) = worklist.pop_front() {
            queued[value] = false;
            let known = self.value_known_bits(func, value);
            if known == self.known[value] {
                continue;
            }

            self.known[value] = known;
            for &dependent in &dependents[value] {
                if queued[dependent] {
                    continue;
                }

                queued[dependent] = true;
                worklist.push_back(dependent);
            }
        }
    }

    fn value_ty(&self, func: &Function, value: ValueId) -> Type {
        self.value_tys
            .get(value)
            .copied()
            .flatten()
            .unwrap_or_else(|| func.dfg.value_ty(value))
    }

    fn value_imm(&self, func: &Function, value: ValueId) -> Option<Immediate> {
        self.immediates
            .get(value)
            .copied()
            .flatten()
            .or_else(|| func.dfg.value_imm(value))
    }

    fn seed_known_bits(&self, func: &Function, value: ValueId) -> KnownBits {
        self.value_imm(func, value)
            .map(KnownBits::from_imm)
            .unwrap_or_else(|| KnownBits::unknown(self.value_ty(func, value)))
    }

    fn known_of(&self, func: &Function, value: ValueId) -> KnownBits {
        self.value_imm(func, value)
            .map(KnownBits::from_imm)
            .unwrap_or_else(|| {
                self.known
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| KnownBits::unknown(self.value_ty(func, value)))
            })
    }

    fn value_known_bits(&self, func: &Function, value: ValueId) -> KnownBits {
        if let Some(imm) = self.value_imm(func, value) {
            return KnownBits::from_imm(imm);
        }

        if self.known.get(value).is_none() {
            return KnownBits::unknown(self.value_ty(func, value));
        }

        let ty = self.value_ty(func, value);
        match func.dfg.value(value) {
            Value::Arg { .. } | Value::Global { .. } | Value::Undef { .. } => {
                KnownBits::unknown(ty)
            }
            Value::Immediate { .. } => unreachable!("immediates handled above"),
            Value::Inst {
                inst, result_idx, ..
            } => self.inst_result_known_bits(func, *inst, usize::from(*result_idx), ty),
        }
    }

    fn inst_result_known_bits(
        &self,
        func: &Function,
        inst: sonatina_ir::InstId,
        result_idx: usize,
        ty: Type,
    ) -> KnownBits {
        if !supports_known_bits(ty) || result_idx != 0 {
            return KnownBits::unknown(ty);
        }

        if let Some(phi) = func.dfg.cast_phi(inst) {
            let mut args = phi
                .args()
                .iter()
                .map(|(value, _)| self.known_of(func, *value));
            return args
                .next()
                .map(|first| args.fold(first, |acc, incoming| acc.meet(incoming, ty)))
                .unwrap_or_else(|| KnownBits::unknown(ty));
        }

        let inst_data = func.dfg.inst(inst);
        let args = inst_data.collect_values();
        match inst_data.kind() {
            InstClassKind::Binary(kind) => self.binary_known_bits(func, kind, ty, &args),
            InstClassKind::Cast(kind) => self.cast_known_bits(func, kind, ty, &args),
            InstClassKind::Unary(kind) => self.unary_known_bits(func, kind, ty, &args),
            InstClassKind::Phi | InstClassKind::Opaque => KnownBits::unknown(ty),
        }
    }

    fn unary_known_bits(
        &self,
        func: &Function,
        kind: UnaryInstKind,
        ty: Type,
        args: &[ValueId],
    ) -> KnownBits {
        let [arg] = args else {
            return KnownBits::unknown(ty);
        };
        let arg_known = self.known_of(func, *arg);
        match kind {
            UnaryInstKind::IsZero => {
                let arg_ty = self.value_ty(func, *arg);
                if !supports_known_bits(arg_ty) {
                    return bool_shape();
                }

                let mask = type_mask(arg_ty);
                if arg_known.all_zero_in(mask) {
                    KnownBits::exact_bool(true)
                } else if (arg_known.known_one & mask) != U256::zero() {
                    KnownBits::exact_bool(false)
                } else {
                    bool_shape()
                }
            }
            UnaryInstKind::Not => {
                if !supports_known_bits(ty) {
                    return KnownBits::unknown(ty);
                }

                KnownBits::normalized(ty, arg_known.known_one, arg_known.known_zero)
            }
            UnaryInstKind::Neg | UnaryInstKind::Snego | UnaryInstKind::EvmClz => {
                KnownBits::unknown(ty)
            }
        }
    }

    fn cast_known_bits(
        &self,
        func: &Function,
        kind: CastInstKind,
        ty: Type,
        args: &[ValueId],
    ) -> KnownBits {
        let [arg] = args else {
            return KnownBits::unknown(ty);
        };
        let src_ty = self.value_ty(func, *arg);
        let src = self.known_of(func, *arg);
        match kind {
            CastInstKind::Zext => {
                let src_mask = type_mask(src_ty);
                let dst_mask = type_mask(ty);
                KnownBits::normalized(
                    ty,
                    (src.known_zero & src_mask) | (dst_mask & !src_mask),
                    src.known_one & src_mask,
                )
            }
            CastInstKind::Trunc => KnownBits::normalized(ty, src.known_zero, src.known_one),
            CastInstKind::Sext => {
                let src_mask = type_mask(src_ty);
                let dst_mask = type_mask(ty);
                let sign_mask = U256::one() << usize::from(type_bits(src_ty) - 1);
                let fill_mask = dst_mask & !src_mask;
                let mut known_zero = src.known_zero & src_mask;
                let mut known_one = src.known_one & src_mask;
                if src.all_zero_in(sign_mask) {
                    known_zero |= fill_mask;
                } else if src.all_one_in(sign_mask) {
                    known_one |= fill_mask;
                }
                KnownBits::normalized(ty, known_zero, known_one)
            }
            CastInstKind::Bitcast | CastInstKind::IntToPtr | CastInstKind::PtrToInt => {
                KnownBits::unknown(ty)
            }
        }
    }

    fn binary_known_bits(
        &self,
        func: &Function,
        kind: BinaryInstKind,
        ty: Type,
        args: &[ValueId],
    ) -> KnownBits {
        let [lhs, rhs] = args else {
            return KnownBits::unknown(ty);
        };
        let lhs_known = self.known_of(func, *lhs);
        let rhs_known = self.known_of(func, *rhs);

        match kind {
            BinaryInstKind::And => KnownBits::normalized(
                ty,
                lhs_known.known_zero | rhs_known.known_zero,
                lhs_known.known_one & rhs_known.known_one,
            ),
            BinaryInstKind::Or => KnownBits::normalized(
                ty,
                lhs_known.known_zero & rhs_known.known_zero,
                lhs_known.known_one | rhs_known.known_one,
            ),
            BinaryInstKind::Xor => KnownBits::normalized(
                ty,
                (lhs_known.known_zero & rhs_known.known_zero)
                    | (lhs_known.known_one & rhs_known.known_one),
                (lhs_known.known_zero & rhs_known.known_one)
                    | (lhs_known.known_one & rhs_known.known_zero),
            ),
            BinaryInstKind::Shl => self.shl_known_bits(func, ty, *lhs, rhs_known),
            BinaryInstKind::Shr => self.shr_known_bits(func, ty, *lhs, rhs_known),
            BinaryInstKind::Sar => self.sar_known_bits(func, ty, *lhs, rhs_known),
            BinaryInstKind::Eq
            | BinaryInstKind::Ne
            | BinaryInstKind::Lt
            | BinaryInstKind::Gt
            | BinaryInstKind::Slt
            | BinaryInstKind::Sgt
            | BinaryInstKind::Le
            | BinaryInstKind::Ge
            | BinaryInstKind::Sle
            | BinaryInstKind::Sge => self.compare_known_bits(func, kind, *lhs, *rhs),
            _ => KnownBits::unknown(ty),
        }
    }

    fn shl_known_bits(
        &self,
        func: &Function,
        ty: Type,
        bits: ValueId,
        value: KnownBits,
    ) -> KnownBits {
        let Some(shift) = constant_shift(self.value_imm(func, bits)) else {
            return KnownBits::unknown(ty);
        };
        let width = U256::from(type_bits(ty));
        if shift >= width {
            return KnownBits::from_imm(Immediate::zero(ty));
        }

        let shift = shift.as_usize();
        KnownBits::normalized(
            ty,
            (value.known_zero << shift) | low_mask(shift as u16),
            value.known_one << shift,
        )
    }

    fn shr_known_bits(
        &self,
        func: &Function,
        ty: Type,
        bits: ValueId,
        value: KnownBits,
    ) -> KnownBits {
        let Some(shift) = constant_shift(self.value_imm(func, bits)) else {
            return KnownBits::unknown(ty);
        };
        let width_bits = type_bits(ty);
        if shift >= U256::from(width_bits) {
            return KnownBits::from_imm(Immediate::zero(ty));
        }

        let shift = shift.as_usize();
        let fill_mask = type_mask(ty) & !low_mask((usize::from(width_bits) - shift) as u16);
        KnownBits::normalized(
            ty,
            (value.known_zero >> shift) | fill_mask,
            value.known_one >> shift,
        )
    }

    fn sar_known_bits(
        &self,
        func: &Function,
        ty: Type,
        bits: ValueId,
        value: KnownBits,
    ) -> KnownBits {
        let Some(shift) = constant_shift(self.value_imm(func, bits)) else {
            return KnownBits::unknown(ty);
        };
        let width_bits = type_bits(ty);
        let sign_mask = U256::one() << usize::from(width_bits - 1);
        if shift >= U256::from(width_bits) {
            return if value.all_zero_in(sign_mask) {
                KnownBits::from_imm(Immediate::zero(ty))
            } else if value.all_one_in(sign_mask) {
                KnownBits::from_imm(Immediate::all_one(ty))
            } else {
                KnownBits::unknown(ty)
            };
        }

        let shift = shift.as_usize();
        let fill_mask = type_mask(ty) & !low_mask((usize::from(width_bits) - shift) as u16);
        let mut known_zero = value.known_zero >> shift;
        let mut known_one = value.known_one >> shift;
        if value.all_zero_in(sign_mask) {
            known_zero |= fill_mask;
        } else if value.all_one_in(sign_mask) {
            known_one |= fill_mask;
        }
        KnownBits::normalized(ty, known_zero, known_one)
    }

    fn compare_known_bits(
        &self,
        func: &Function,
        kind: BinaryInstKind,
        lhs: ValueId,
        rhs: ValueId,
    ) -> KnownBits {
        let ty = self.value_ty(func, lhs);
        if !supports_known_bits(ty) {
            return bool_shape();
        }

        let lhs_known = self.known_of(func, lhs);
        let rhs_known = self.known_of(func, rhs);
        let lhs_exact = lhs_known.exact_imm(ty);
        let rhs_exact = rhs_known.exact_imm(ty);

        if let (Some(lhs_imm), Some(rhs_imm)) = (lhs_exact, rhs_exact) {
            let value = match kind {
                BinaryInstKind::Eq => lhs_imm == rhs_imm,
                BinaryInstKind::Ne => lhs_imm != rhs_imm,
                BinaryInstKind::Lt => lhs_imm.lt(rhs_imm).as_i256().trunc_to_i1(),
                BinaryInstKind::Gt => lhs_imm.gt(rhs_imm).as_i256().trunc_to_i1(),
                BinaryInstKind::Slt => lhs_imm.slt(rhs_imm).as_i256().trunc_to_i1(),
                BinaryInstKind::Sgt => lhs_imm.sgt(rhs_imm).as_i256().trunc_to_i1(),
                BinaryInstKind::Le => lhs_imm.le(rhs_imm).as_i256().trunc_to_i1(),
                BinaryInstKind::Ge => lhs_imm.ge(rhs_imm).as_i256().trunc_to_i1(),
                BinaryInstKind::Sle => lhs_imm.sle(rhs_imm).as_i256().trunc_to_i1(),
                BinaryInstKind::Sge => lhs_imm.sge(rhs_imm).as_i256().trunc_to_i1(),
                _ => unreachable!("compare kind expected"),
            };
            return KnownBits::exact_bool(value);
        }

        if matches!(kind, BinaryInstKind::Eq | BinaryInstKind::Ne)
            && has_conflicting_known_bits(lhs_known, rhs_known, ty)
        {
            return KnownBits::exact_bool(matches!(kind, BinaryInstKind::Ne));
        }

        bool_shape()
    }
}

#[cfg(test)]
pub(crate) fn count_query_news_for_test<T>(f: impl FnOnce() -> T) -> (T, usize) {
    TEST_NEW_COUNTER.with(|counter| {
        assert!(
            counter.replace(Some(0)).is_none(),
            "known bits query counter is already active"
        );

        let result = catch_unwind(AssertUnwindSafe(f));
        let count = counter
            .replace(None)
            .expect("known bits query counter should stay active");

        match result {
            Ok(result) => (result, count),
            Err(payload) => resume_unwind(payload),
        }
    })
}

pub(crate) fn has_conflicting_known_bits(lhs: KnownBits, rhs: KnownBits, ty: Type) -> bool {
    supports_known_bits(ty)
        && ((lhs.known_zero & rhs.known_one) | (lhs.known_one & rhs.known_zero)) & type_mask(ty)
            != U256::zero()
}

pub(crate) fn supports_known_bits(ty: Type) -> bool {
    matches!(
        ty,
        Type::I1
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::I256
            | Type::EnumTag(_)
    )
}

fn constant_shift(bits: Option<Immediate>) -> Option<U256> {
    Some(bits?.as_i256().to_u256())
}

pub(crate) fn type_bits(ty: Type) -> u16 {
    match ty {
        Type::I1 => 1,
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        Type::I128 => 128,
        Type::I256 | Type::EnumTag(_) => 256,
        _ => panic!("non-integral type {ty:?} has no known-bit width"),
    }
}

pub(crate) fn type_mask(ty: Type) -> U256 {
    low_mask(type_bits(ty))
}

pub(crate) fn low_mask(bits: u16) -> U256 {
    match bits {
        0 => U256::zero(),
        256 => !U256::zero(),
        bits => (U256::one() << usize::from(bits)) - U256::one(),
    }
}

fn bool_shape() -> KnownBits {
    KnownBits::unknown(Type::I1)
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        Function, I256, Immediate, Type, U256,
        builder::test_util::*,
        inst::{
            InstClassKind,
            arith::{Sar, Shr},
            cast::{Sext, Trunc, Zext},
            control_flow::{Br, Jump, Phi, Return},
            logic::{And, Not, Or, Xor},
        },
        isa::Isa,
    };
    use sonatina_parser::parse_module;

    use super::*;

    #[derive(Clone, Copy)]
    struct XorShift64(u64);

    impl XorShift64 {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
    }

    #[test]
    fn constant_bits_round_trip_to_exact_immediate() {
        let bits = KnownBits::from_imm(Immediate::from_i256(I256::from(-1i8), Type::I8));
        assert!(bits.all_one_in(U256::from(0xffu16)));
        assert_eq!(
            bits.exact_imm(Type::I8),
            Some(Immediate::from_i256(I256::from(-1i8), Type::I8))
        );
    }

    #[test]
    fn logical_shr_marks_high_bits_zero() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256], Type::I256);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let shift = builder.make_imm_value(Immediate::from_i256(I256::from(224u16), Type::I256));
        let shifted = builder.insert_inst_with(|| Shr::new(is, shift, arg), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, shifted));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = KnownBitsQuery::new(&func);
        let known = query.for_value(&func, shifted);
        assert!(query.fits_in_low_bits(&func, shifted, 32));
        assert!(known.all_zero_in(!low_mask(32)));
    }

    #[test]
    fn arithmetic_sar_only_sets_fill_bits_when_sign_known() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256], Type::I256);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let shift = builder.make_imm_value(Immediate::from_i256(I256::from(224u16), Type::I256));
        let shifted = builder.insert_inst_with(|| Sar::new(is, shift, arg), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, shifted));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = KnownBitsQuery::new(&func);
        assert!(!query.for_value(&func, shifted).all_zero_in(!low_mask(32)));

        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I256);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let value = builder.make_imm_value(Immediate::from_i256(I256::from(7u8), Type::I256));
        let shift = builder.make_imm_value(Immediate::from_i256(I256::from(224u16), Type::I256));
        let shifted = builder.insert_inst_with(|| Sar::new(is, shift, value), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, shifted));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = KnownBitsQuery::new(&func);
        assert!(query.for_value(&func, shifted).all_zero_in(!low_mask(32)));
    }

    #[test]
    fn phi_meet_intersects_incoming_known_bits() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::I8);
        let is = evm.inst_set();
        let entry = builder.append_block();
        let left = builder.append_block();
        let right = builder.append_block();
        let join = builder.append_block();

        builder.switch_to_block(entry);
        let cond = builder.args()[0];
        builder.insert_inst_no_result_with(|| Br::new(is, cond, left, right));

        builder.switch_to_block(left);
        let lhs = builder.make_imm_value(Immediate::from_i256(I256::from(0x10u8), Type::I8));
        builder.insert_inst_no_result_with(|| Jump::new(is, join));

        builder.switch_to_block(right);
        let rhs = builder.make_imm_value(Immediate::from_i256(I256::from(0x30u8), Type::I8));
        builder.insert_inst_no_result_with(|| Jump::new(is, join));

        builder.switch_to_block(join);
        let phi =
            builder.insert_inst_with(|| Phi::new(is, vec![(lhs, left), (rhs, right)]), Type::I8);
        builder.insert_inst_no_result_with(|| Return::new_single(is, phi));

        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = KnownBitsQuery::new(&func);
        let known = query.for_value(&func, phi);
        assert_eq!(known.known_one & U256::from(0xffu16), U256::from(0x10u8));
        assert_eq!(known.known_zero & U256::from(0xffu16), U256::from(0xcfu8));
    }

    #[test]
    fn loop_phi_reaches_fixpoint() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-london"

func public %f(v0.i1) -> i8 {
block0:
    jump block1;

block1:
    v1.i8 = phi (254.i8 block0) (v2 block2);
    br v0 block2 block3;

block2:
    v2.i8 = and v1 254.i8;
    jump block1;

block3:
    return v1;
}
"#,
        )
        .expect("module parses");
        let func = parsed
            .module
            .func_store
            .view(parsed.module.funcs()[0], |func| func.clone());
        let phi = find_inst_result_by_kind(&func, InstClassKind::Phi);
        let query = KnownBitsQuery::new(&func);
        assert!(query.for_value(&func, phi).all_zero_in(U256::one()));
    }

    #[test]
    fn cast_rules_handle_zext_trunc_and_sext() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::I16);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let neg_one_i8 = builder.make_imm_value(Immediate::from_i256(I256::from(-1i8), Type::I8));
        let wide = builder.insert_inst_with(|| Zext::new(is, neg_one_i8, Type::I16), Type::I16);
        let narrowed = builder.insert_inst_with(|| Trunc::new(is, wide, Type::I8), Type::I8);
        let signed = builder.insert_inst_with(|| Sext::new(is, narrowed, Type::I16), Type::I16);
        builder.insert_inst_no_result_with(|| Return::new_single(is, signed));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = KnownBitsQuery::new(&func);
        assert_eq!(
            query.for_value(&func, wide).exact_imm(Type::I16),
            Some(Immediate::from_i256(I256::from(0x00ffu16), Type::I16))
        );
        assert_eq!(
            query.for_value(&func, narrowed).exact_imm(Type::I8),
            Some(Immediate::from_i256(I256::from(-1i8), Type::I8))
        );
        assert_eq!(
            query.for_value(&func, signed).exact_imm(Type::I16),
            Some(Immediate::from_i256(I256::from(-1i16), Type::I16))
        );
    }

    #[test]
    fn helper_queries_report_zero_nonzero_and_conflicts() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I1);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let mask = builder.make_imm_value(Immediate::from_i256(I256::from(0x7fu8), Type::I8));
        let forced_mask =
            builder.make_imm_value(Immediate::from_i256(I256::from(0x80u8), Type::I8));
        let masked = builder.insert_inst_with(|| And::new(is, arg, mask), Type::I8);
        let forced = builder.insert_inst_with(|| Or::new(is, masked, forced_mask), Type::I8);
        let zero = builder.make_imm_value(Immediate::zero(Type::I8));
        let cmp = builder.insert_inst_with(|| Not::new(is, zero), Type::I8);
        builder.insert_inst_no_result_with(|| Return::new_single(is, cmp));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = KnownBitsQuery::new(&func);
        assert!(!query.is_known_zero(&func, masked));
        assert!(query.is_known_nonzero(&func, forced));
        assert!(query.has_conflicting_known_bits(&func, masked, forced));
        assert!(query.fits_in_low_bits(&func, masked, 7));
    }

    #[test]
    fn unsupported_phi_result_stays_unknown() {
        let mb = test_module_builder();
        let ptr_ty = mb.ptr_type(Type::I8);
        let (evm, mut builder) = test_func_builder(&mb, &[ptr_ty, Type::I1], Type::Unit);
        let is = evm.inst_set();
        let entry = builder.append_block();
        let left = builder.append_block();
        let right = builder.append_block();
        let join = builder.append_block();

        builder.switch_to_block(entry);
        let ptr = builder.args()[0];
        let cond = builder.args()[1];
        builder.insert_inst_no_result_with(|| Br::new(is, cond, left, right));

        builder.switch_to_block(left);
        builder.insert_inst_no_result_with(|| Jump::new(is, join));

        builder.switch_to_block(right);
        let undef = builder.make_undef_value(ptr_ty);
        builder.insert_inst_no_result_with(|| Jump::new(is, join));

        builder.switch_to_block(join);
        let phi =
            builder.insert_inst_with(|| Phi::new(is, vec![(ptr, left), (undef, right)]), ptr_ty);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        assert_eq!(
            KnownBitsQuery::new(&func).for_value(&func, phi),
            KnownBits::default()
        );
    }

    #[test]
    fn randomized_soundness_for_bitwise_and_shift_rules() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I256], Type::I256);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let shift = builder.make_imm_value(Immediate::from_i256(I256::from(224u16), Type::I256));
        let shr = builder.insert_inst_with(|| Shr::new(is, shift, arg), Type::I256);
        let mask = builder.make_imm_value(Immediate::from_i256(I256::from(0x55u8), Type::I256));
        let forced_mask =
            builder.make_imm_value(Immediate::from_i256(I256::from(0x80u8), Type::I256));
        let xor_mask = builder.make_imm_value(Immediate::from_i256(I256::from(0xffu8), Type::I256));
        let and = builder.insert_inst_with(|| And::new(is, arg, mask), Type::I256);
        let or = builder.insert_inst_with(|| Or::new(is, and, forced_mask), Type::I256);
        let xor = builder.insert_inst_with(|| Xor::new(is, and, xor_mask), Type::I256);
        builder.insert_inst_no_result_with(|| Return::new_single(is, xor));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = KnownBitsQuery::new(&func);
        let shr_known = query.for_value(&func, shr);
        let and_known = query.for_value(&func, and);
        let or_known = query.for_value(&func, or);
        let xor_known = query.for_value(&func, xor);
        let mut rng = XorShift64(1);
        for _ in 0..256 {
            let arg_imm = imm_i256(next_u256(&mut rng));
            assert_sound(
                shr_known,
                Type::I256,
                arg_imm >> imm_i256(U256::from(224u16)),
            );
            assert_sound(
                and_known,
                Type::I256,
                arg_imm & imm_i256(U256::from(0x55u8)),
            );
            let masked = arg_imm & imm_i256(U256::from(0x55u8));
            assert_sound(or_known, Type::I256, masked | imm_i256(U256::from(0x80u8)));
            assert_sound(xor_known, Type::I256, masked ^ imm_i256(U256::from(0xffu8)));
        }
    }

    #[test]
    fn randomized_soundness_for_cast_and_iszero_rules() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I1);
        let is = evm.inst_set();
        let block = builder.append_block();
        builder.switch_to_block(block);
        let arg = builder.args()[0];
        let zext = builder.insert_inst_with(|| Zext::new(is, arg, Type::I16), Type::I16);
        let trunc = builder.insert_inst_with(|| Trunc::new(is, zext, Type::I8), Type::I8);
        let sext = builder.insert_inst_with(|| Sext::new(is, trunc, Type::I16), Type::I16);
        let one = builder.make_imm_value(Immediate::from_i256(I256::from(1u8), Type::I8));
        let forced_nonzero = builder.insert_inst_with(|| Or::new(is, trunc, one), Type::I8);
        let iszero = builder.insert_inst_with(
            || sonatina_ir::inst::cmp::IsZero::new(is, forced_nonzero),
            Type::I1,
        );
        builder.insert_inst_no_result_with(|| Return::new_single(is, iszero));
        builder.seal_all();
        builder.finish();

        let func = only_func(&mb);
        let query = KnownBitsQuery::new(&func);
        let zext_known = query.for_value(&func, zext);
        let trunc_known = query.for_value(&func, trunc);
        let sext_known = query.for_value(&func, sext);
        let iszero_known = query.for_value(&func, iszero);
        let mut rng = XorShift64(9);
        for _ in 0..256 {
            let arg_imm = Immediate::from_i256(I256::from(next_u256(&mut rng)), Type::I8);
            let zext_imm = arg_imm.zext(Type::I16);
            let trunc_imm = zext_imm.trunc(Type::I8);
            let sext_imm = trunc_imm.sext(Type::I16);
            assert_sound(zext_known, Type::I16, zext_imm);
            assert_sound(trunc_known, Type::I8, trunc_imm);
            assert_sound(sext_known, Type::I16, sext_imm);
            assert_sound(iszero_known, Type::I1, Immediate::I1(false));
        }
    }

    fn only_func(mb: &sonatina_ir::builder::ModuleBuilder) -> Function {
        let func_ref = mb.func_store.funcs()[0];
        mb.func_store.view(func_ref, |func| func.clone())
    }

    fn find_inst_result_by_kind(func: &Function, kind: InstClassKind) -> ValueId {
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if func.dfg.inst(inst).kind() == kind {
                    return func.dfg.inst_result(inst).expect("result");
                }
            }
        }
        panic!("missing instruction kind {kind:?}");
    }

    fn next_u256(rng: &mut XorShift64) -> U256 {
        let mut value = U256::zero();
        for shift in [0usize, 64, 128, 192] {
            value |= U256::from(rng.next()) << shift;
        }
        value
    }

    fn imm_i256(value: U256) -> Immediate {
        Immediate::from_i256(I256::from(value), Type::I256)
    }

    fn assert_sound(known: KnownBits, ty: Type, concrete: Immediate) {
        let mask = type_mask(ty);
        let value = concrete.as_i256().to_u256() & mask;
        assert_eq!(value & known.known_one, known.known_one & mask);
        assert_eq!((!value) & known.known_zero & mask, known.known_zero & mask);
    }
}
