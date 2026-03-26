use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    Function, Immediate, Type, U256, Value, ValueId,
    inst::{BinaryInstKind, InstClassKind, UnaryInstKind},
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

    fn normalized(ty: Type, known_zero: U256, known_one: U256) -> Self {
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
        Self::normalized(
            ty,
            self.known_zero & other.known_zero,
            self.known_one & other.known_one,
        )
    }
}

pub struct KnownBitsQuery<'a> {
    func: &'a Function,
    memo: SecondaryMap<ValueId, KnownBits>,
    state: SecondaryMap<ValueId, VisitState>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum VisitState {
    #[default]
    Unvisited,
    Visiting,
    Done,
}

impl<'a> KnownBitsQuery<'a> {
    pub fn new(func: &'a Function) -> Self {
        Self {
            func,
            memo: SecondaryMap::default(),
            state: SecondaryMap::default(),
        }
    }

    pub fn for_value(&mut self, value: ValueId) -> KnownBits {
        match self.state[value] {
            VisitState::Done => self.memo[value],
            VisitState::Visiting => KnownBits::unknown(self.func.dfg.value_ty(value)),
            VisitState::Unvisited => self.compute_value(value),
        }
    }

    fn compute_value(&mut self, value: ValueId) -> KnownBits {
        self.state[value] = VisitState::Visiting;
        let known = self.value_known_bits(value);
        self.memo[value] = known;
        self.state[value] = VisitState::Done;
        known
    }

    fn value_known_bits(&mut self, value: ValueId) -> KnownBits {
        if let Some(imm) = self.func.dfg.value_imm(value) {
            return KnownBits::from_imm(imm);
        }

        let ty = self.func.dfg.value_ty(value);
        match self.func.dfg.value(value) {
            Value::Arg { .. } | Value::Global { .. } | Value::Undef { .. } => {
                KnownBits::unknown(ty)
            }
            Value::Immediate { .. } => unreachable!("immediates handled above"),
            Value::Inst {
                inst, result_idx, ..
            } => self.inst_result_known_bits(*inst, usize::from(*result_idx), ty),
        }
    }

    fn inst_result_known_bits(
        &mut self,
        inst: sonatina_ir::InstId,
        result_idx: usize,
        ty: Type,
    ) -> KnownBits {
        if result_idx != 0 {
            return KnownBits::unknown(ty);
        }

        if let Some(phi) = self.func.dfg.cast_phi(inst) {
            let mut args = phi.args().iter().map(|(value, _)| self.for_value(*value));
            return args
                .next()
                .map(|first| args.fold(first, |acc, incoming| acc.meet(incoming, ty)))
                .unwrap_or_else(|| KnownBits::unknown(ty));
        }

        let inst_data = self.func.dfg.inst(inst);
        let args = inst_data.collect_values();
        match inst_data.kind() {
            InstClassKind::Binary(kind) => self.binary_known_bits(kind, ty, &args),
            InstClassKind::Cast(kind) => self.cast_known_bits(kind, ty, &args),
            InstClassKind::Unary(kind) => self.unary_known_bits(kind, ty, &args),
            InstClassKind::Phi | InstClassKind::Opaque => KnownBits::unknown(ty),
        }
    }

    fn unary_known_bits(&mut self, kind: UnaryInstKind, ty: Type, args: &[ValueId]) -> KnownBits {
        let [arg] = args else {
            return KnownBits::unknown(ty);
        };
        let arg_known = self.for_value(*arg);
        match kind {
            UnaryInstKind::IsZero => {
                let arg_ty = self.func.dfg.value_ty(*arg);
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
        &mut self,
        kind: sonatina_ir::inst::CastInstKind,
        ty: Type,
        args: &[ValueId],
    ) -> KnownBits {
        let [arg] = args else {
            return KnownBits::unknown(ty);
        };
        let src_ty = self.func.dfg.value_ty(*arg);
        let src = self.for_value(*arg);
        match kind {
            sonatina_ir::inst::CastInstKind::Zext => {
                let src_mask = type_mask(src_ty);
                let dst_mask = type_mask(ty);
                KnownBits::normalized(
                    ty,
                    (src.known_zero & src_mask) | (dst_mask & !src_mask),
                    src.known_one & src_mask,
                )
            }
            sonatina_ir::inst::CastInstKind::Trunc => {
                KnownBits::normalized(ty, src.known_zero, src.known_one)
            }
            sonatina_ir::inst::CastInstKind::Sext => {
                let src_mask = type_mask(src_ty);
                let dst_mask = type_mask(ty);
                let src_bits = type_bits(src_ty);
                let sign_mask = U256::one() << usize::from(src_bits - 1);
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
            sonatina_ir::inst::CastInstKind::Bitcast
            | sonatina_ir::inst::CastInstKind::IntToPtr
            | sonatina_ir::inst::CastInstKind::PtrToInt => KnownBits::unknown(ty),
        }
    }

    fn binary_known_bits(&mut self, kind: BinaryInstKind, ty: Type, args: &[ValueId]) -> KnownBits {
        let [lhs, rhs] = args else {
            return KnownBits::unknown(ty);
        };
        let lhs_known = self.for_value(*lhs);
        let rhs_known = self.for_value(*rhs);

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
            BinaryInstKind::Shl => self.shl_known_bits(ty, *lhs, rhs_known),
            BinaryInstKind::Shr => self.shr_known_bits(ty, *lhs, rhs_known),
            BinaryInstKind::Sar => self.sar_known_bits(ty, *lhs, *rhs, rhs_known),
            BinaryInstKind::Eq
            | BinaryInstKind::Ne
            | BinaryInstKind::Lt
            | BinaryInstKind::Gt
            | BinaryInstKind::Slt
            | BinaryInstKind::Sgt
            | BinaryInstKind::Le
            | BinaryInstKind::Ge
            | BinaryInstKind::Sle
            | BinaryInstKind::Sge => self.compare_known_bits(kind, *lhs, *rhs),
            _ => KnownBits::unknown(ty),
        }
    }

    fn shl_known_bits(&mut self, ty: Type, bits: ValueId, value: KnownBits) -> KnownBits {
        let Some(shift) = constant_shift(self.func, bits) else {
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

    fn shr_known_bits(&mut self, ty: Type, bits: ValueId, value: KnownBits) -> KnownBits {
        let Some(shift) = constant_shift(self.func, bits) else {
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
        &mut self,
        ty: Type,
        bits: ValueId,
        value_id: ValueId,
        value: KnownBits,
    ) -> KnownBits {
        let Some(shift) = constant_shift(self.func, bits) else {
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
                KnownBits::unknown(self.func.dfg.value_ty(value_id))
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
        &mut self,
        kind: BinaryInstKind,
        lhs: ValueId,
        rhs: ValueId,
    ) -> KnownBits {
        let lhs_ty = self.func.dfg.value_ty(lhs);
        let lhs_known = self.for_value(lhs);
        let rhs_known = self.for_value(rhs);
        if !supports_known_bits(lhs_ty) {
            return bool_shape();
        }

        let lhs_exact = lhs_known.exact_imm(lhs_ty);
        let rhs_exact = rhs_known.exact_imm(lhs_ty);

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
                _ => unreachable!("non-compare kind"),
            };
            return KnownBits::exact_bool(value);
        }

        if matches!(kind, BinaryInstKind::Eq | BinaryInstKind::Ne)
            && ((lhs_known.known_zero & rhs_known.known_one)
                | (lhs_known.known_one & rhs_known.known_zero))
                & type_mask(lhs_ty)
                != U256::zero()
        {
            return KnownBits::exact_bool(matches!(kind, BinaryInstKind::Ne));
        }

        bool_shape()
    }
}

fn supports_known_bits(ty: Type) -> bool {
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

fn constant_shift(func: &Function, bits: ValueId) -> Option<U256> {
    Some(func.dfg.value_imm(bits)?.as_i256().to_u256())
}

fn type_bits(ty: Type) -> u16 {
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

fn type_mask(ty: Type) -> U256 {
    low_mask(type_bits(ty))
}

fn low_mask(bits: u16) -> U256 {
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
        Function, I256, Type,
        builder::test_util::*,
        inst::{
            arith::{Sar, Shr},
            cast::{Sext, Trunc, Zext},
            control_flow::{Br, Jump, Phi, Return},
        },
        isa::Isa,
    };

    use super::*;

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
        let mut query = KnownBitsQuery::new(&func);
        let known = query.for_value(shifted);
        assert!(known.fits_in_low_bits(32, Type::I256));
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
        let mut query = KnownBitsQuery::new(&func);
        let known = query.for_value(shifted);
        assert!(!known.all_zero_in(!low_mask(32)));

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
        let mut query = KnownBitsQuery::new(&func);
        let known = query.for_value(shifted);
        assert!(known.all_zero_in(!low_mask(32)));
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
        let mut query = KnownBitsQuery::new(&func);
        let known = query.for_value(phi);
        assert_eq!(known.known_one & U256::from(0xffu16), U256::from(0x10u8));
        assert_eq!(known.known_zero & U256::from(0xffu16), U256::from(0xcfu8));
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
        let mut query = KnownBitsQuery::new(&func);
        assert_eq!(
            query.for_value(wide).exact_imm(Type::I16),
            Some(Immediate::from_i256(I256::from(0x00ffu16), Type::I16))
        );
        assert_eq!(
            query.for_value(narrowed).exact_imm(Type::I8),
            Some(Immediate::from_i256(I256::from(-1i8), Type::I8))
        );
        assert_eq!(
            query.for_value(signed).exact_imm(Type::I16),
            Some(Immediate::from_i256(I256::from(-1i16), Type::I16))
        );
    }

    fn only_func(mb: &sonatina_ir::builder::ModuleBuilder) -> Function {
        let func_ref = mb.func_store.funcs()[0];
        mb.func_store.view(func_ref, |func| func.clone())
    }
}
