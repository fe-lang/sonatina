use smallvec::smallvec;

use super::{Action, EvalValue, Interpret, State, single_result};
use crate::{I256, Immediate, Type, U256, inst::evm::*};

fn bits_for_ty(ty: Type) -> u32 {
    match ty {
        Type::I1 => 1,
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        Type::I128 => 128,
        Type::I256 => 256,
        Type::EnumTag(_) => unreachable!(),
        Type::Compound(_) | Type::Unit => unreachable!(),
    }
}

fn mask_for_ty(ty: Type) -> U256 {
    let bits = bits_for_ty(ty);
    if bits == 256 {
        !U256::zero()
    } else {
        (U256::one() << bits) - U256::one()
    }
}

fn imm_to_u256(imm: Immediate) -> U256 {
    imm.as_i256().to_u256() & mask_for_ty(imm.ty())
}

fn u256_to_imm(value: U256, ty: Type) -> Immediate {
    Immediate::from_i256(I256::from(value), ty)
}

fn narrow_sat_args(lhs: EvalValue, rhs: EvalValue, ty: Type) -> Option<(Immediate, Immediate)> {
    let (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) = (lhs, rhs) else {
        return None;
    };
    Some((lhs.trunc(ty), rhs.trunc(ty)))
}

fn zero_extend_i256(value: Immediate) -> EvalValue {
    EvalValue::Imm(value.zext(Type::I256))
}

fn sign_extend_i256(value: Immediate) -> EvalValue {
    EvalValue::Imm(value.sext(Type::I256))
}

fn evm_addmod(lhs: U256, rhs: U256, modulus: U256) -> U256 {
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

fn evm_mulmod(lhs: U256, rhs: U256, modulus: U256) -> U256 {
    if modulus.is_zero() {
        return U256::zero();
    }

    let mut result = U256::zero();
    let mut addend = lhs % modulus;
    let mut multiplier = rhs % modulus;

    while multiplier > U256::zero() {
        if multiplier & U256::one() == U256::one() {
            result = evm_addmod(result, addend, modulus);
        }
        addend = evm_addmod(addend, addend, modulus);
        multiplier >>= 1;
    }

    result
}

fn evm_exp(base: U256, exponent: U256, mask: U256) -> U256 {
    let mut result = U256::one() & mask;
    let mut base = base & mask;
    let mut exponent = exponent;

    while exponent > U256::zero() {
        if exponent & U256::one() == U256::one() {
            result = result.overflowing_mul(base).0 & mask;
        }

        exponent >>= 1;
        base = base.overflowing_mul(base).0 & mask;
    }

    result
}

fn evm_byte(pos: U256, value: U256, value_bytes: usize) -> U256 {
    if pos >= U256::from(32u8) {
        return U256::zero();
    }

    let pos = pos.as_usize();
    if pos < 32 - value_bytes {
        return U256::zero();
    }

    let idx = pos - (32 - value_bytes);
    let shift_bytes = value_bytes - 1 - idx;
    (value >> (shift_bytes * 8)) & U256::from(0xffu16)
}

fn evm_signextend(byte: U256, value: U256) -> U256 {
    if byte >= U256::from(32u8) {
        return value;
    }

    let sign_bit = (byte.as_usize() + 1) * 8 - 1;
    if value.bit(sign_bit) {
        value | (!U256::zero() << (sign_bit + 1))
    } else {
        value & ((U256::one() << (sign_bit + 1)) - U256::one())
    }
}

fn overflow_results(result: EvalValue, overflow: EvalValue) -> super::EvalResults {
    smallvec![result, overflow]
}

impl Interpret for EvmUdiv {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() { rhs } else { lhs.udiv(rhs) }
        }))
    }
}

impl Interpret for EvmUdivo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        match (lhs, rhs) {
            (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) => overflow_results(
                EvalValue::Imm(if rhs.is_zero() { rhs } else { lhs.udiv(rhs) }),
                EvalValue::Imm(Immediate::from(rhs.is_zero())),
            ),
            _ => overflow_results(EvalValue::Undef, EvalValue::Undef),
        }
    }
}

impl Interpret for EvmSdiv {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() { rhs } else { lhs.sdiv(rhs) }
        }))
    }
}

impl Interpret for EvmSdivo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        match (lhs, rhs) {
            (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) => {
                let ty = lhs.ty();
                let min =
                    Immediate::from_i256(I256::from(U256::one() << (bits_for_ty(ty) - 1)), ty);
                let neg_one = Immediate::from_i256(I256::from(mask_for_ty(ty)), ty);
                overflow_results(
                    EvalValue::Imm(if rhs.is_zero() { rhs } else { lhs.sdiv(rhs) }),
                    EvalValue::Imm(Immediate::from(
                        rhs.is_zero() || (lhs == min && rhs == neg_one),
                    )),
                )
            }
            _ => overflow_results(EvalValue::Undef, EvalValue::Undef),
        }
    }
}

impl Interpret for EvmUmod {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() { rhs } else { lhs.urem(rhs) }
        }))
    }
}

impl Interpret for EvmUmodo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        match (lhs, rhs) {
            (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) => overflow_results(
                EvalValue::Imm(if rhs.is_zero() { rhs } else { lhs.urem(rhs) }),
                EvalValue::Imm(Immediate::from(rhs.is_zero())),
            ),
            _ => overflow_results(EvalValue::Undef, EvalValue::Undef),
        }
    }
}

impl Interpret for EvmSmod {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        single_result(EvalValue::zip_with_imm(lhs, rhs, |lhs, rhs| {
            if rhs.is_zero() { rhs } else { lhs.srem(rhs) }
        }))
    }
}

impl Interpret for EvmSmodo {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        match (lhs, rhs) {
            (EvalValue::Imm(lhs), EvalValue::Imm(rhs)) => overflow_results(
                EvalValue::Imm(if rhs.is_zero() { rhs } else { lhs.srem(rhs) }),
                EvalValue::Imm(Immediate::from(rhs.is_zero())),
            ),
            _ => overflow_results(EvalValue::Undef, EvalValue::Undef),
        }
    }
}

impl Interpret for EvmUaddsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let Some((lhs, rhs)) = narrow_sat_args(lhs, rhs, *self.ty()) else {
            return single_result(EvalValue::Undef);
        };

        single_result(zero_extend_i256(lhs.saturating_uadd(rhs)))
    }
}

impl Interpret for EvmSaddsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let Some((lhs, rhs)) = narrow_sat_args(lhs, rhs, *self.ty()) else {
            return single_result(EvalValue::Undef);
        };

        single_result(sign_extend_i256(lhs.saturating_sadd(rhs)))
    }
}

impl Interpret for EvmUsubsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let Some((lhs, rhs)) = narrow_sat_args(lhs, rhs, *self.ty()) else {
            return single_result(EvalValue::Undef);
        };

        single_result(zero_extend_i256(lhs.saturating_usub(rhs)))
    }
}

impl Interpret for EvmSsubsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let Some((lhs, rhs)) = narrow_sat_args(lhs, rhs, *self.ty()) else {
            return single_result(EvalValue::Undef);
        };

        single_result(sign_extend_i256(lhs.saturating_ssub(rhs)))
    }
}

impl Interpret for EvmUmulsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let Some((lhs, rhs)) = narrow_sat_args(lhs, rhs, *self.ty()) else {
            return single_result(EvalValue::Undef);
        };

        single_result(zero_extend_i256(lhs.saturating_umul(rhs)))
    }
}

impl Interpret for EvmSmulsat {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let Some((lhs, rhs)) = narrow_sat_args(lhs, rhs, *self.ty()) else {
            return single_result(EvalValue::Undef);
        };

        single_result(sign_extend_i256(lhs.saturating_smul(rhs)))
    }
}

impl Interpret for EvmAddMod {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let modulus = state.lookup_val(*self.modulus());

        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs), EvalValue::Imm(modulus)) =
            (lhs, rhs, modulus)
        else {
            return single_result(EvalValue::Undef);
        };

        debug_assert_eq!(lhs.ty(), rhs.ty());
        debug_assert_eq!(lhs.ty(), modulus.ty());

        let ty = lhs.ty();
        let result = evm_addmod(imm_to_u256(lhs), imm_to_u256(rhs), imm_to_u256(modulus));
        single_result(EvalValue::Imm(u256_to_imm(result, ty)))
    }
}

impl Interpret for EvmMulMod {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let modulus = state.lookup_val(*self.modulus());

        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs), EvalValue::Imm(modulus)) =
            (lhs, rhs, modulus)
        else {
            return single_result(EvalValue::Undef);
        };

        debug_assert_eq!(lhs.ty(), rhs.ty());
        debug_assert_eq!(lhs.ty(), modulus.ty());

        let ty = lhs.ty();
        let result = evm_mulmod(imm_to_u256(lhs), imm_to_u256(rhs), imm_to_u256(modulus));
        single_result(EvalValue::Imm(u256_to_imm(result, ty)))
    }
}

impl Interpret for EvmExp {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let base = state.lookup_val(*self.base());
        let exponent = state.lookup_val(*self.exponent());

        let (EvalValue::Imm(base), EvalValue::Imm(exponent)) = (base, exponent) else {
            return single_result(EvalValue::Undef);
        };

        debug_assert_eq!(base.ty(), exponent.ty());

        let ty = base.ty();
        let mask = mask_for_ty(ty);
        let result = evm_exp(imm_to_u256(base), imm_to_u256(exponent), mask);
        single_result(EvalValue::Imm(u256_to_imm(result, ty)))
    }
}

impl Interpret for EvmSignExtend {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let byte = state.lookup_val(*self.byte());
        let value = state.lookup_val(*self.value());

        let (EvalValue::Imm(byte), EvalValue::Imm(value)) = (byte, value) else {
            return single_result(EvalValue::Undef);
        };

        debug_assert_eq!(byte.ty(), value.ty());

        let ty = value.ty();
        let result = evm_signextend(imm_to_u256(byte), imm_to_u256(value)) & mask_for_ty(ty);
        single_result(EvalValue::Imm(u256_to_imm(result, ty)))
    }
}

impl Interpret for EvmByte {
    fn interpret(&self, state: &mut dyn State) -> super::EvalResults {
        state.set_action(Action::Continue);

        let pos = state.lookup_val(*self.pos());
        let value = state.lookup_val(*self.value());

        let (EvalValue::Imm(pos), EvalValue::Imm(value)) = (pos, value) else {
            return single_result(EvalValue::Undef);
        };

        debug_assert_eq!(pos.ty(), value.ty());

        let ty = value.ty();
        let value_bytes = bits_for_ty(ty).div_ceil(8) as usize;

        let result = evm_byte(imm_to_u256(pos), imm_to_u256(value), value_bytes);
        single_result(EvalValue::Imm(u256_to_imm(result, ty)))
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{
        DataFlowGraph, HasInst, Immediate, Type,
        builder::test_util::test_isa,
        interpret::EvalResults,
        module::{FuncRef, ModuleCtx},
    };

    use super::*;

    struct TestHasInst;
    impl<I: crate::Inst> HasInst<I> for TestHasInst {}

    struct TestState {
        dfg: DataFlowGraph,
        values: HashMap<crate::ValueId, EvalValue>,
    }

    impl TestState {
        fn new(values: impl IntoIterator<Item = (crate::ValueId, EvalValue)>) -> Self {
            let isa = test_isa();
            let dfg = DataFlowGraph::new(ModuleCtx::new(&isa));
            Self {
                dfg,
                values: values.into_iter().collect(),
            }
        }
    }

    impl State for TestState {
        fn lookup_val(&mut self, value: crate::ValueId) -> EvalValue {
            self.values.get(&value).cloned().unwrap_or_default()
        }

        fn call_func(&mut self, _func: FuncRef, _args: Vec<EvalValue>) -> EvalResults {
            unreachable!()
        }

        fn set_action(&mut self, action: Action) {
            assert_eq!(action, Action::Continue);
        }

        fn prev_block(&mut self) -> crate::BlockId {
            unreachable!()
        }

        fn load(&mut self, _addr: EvalValue, _ty: Type) -> EvalValue {
            unreachable!()
        }

        fn store(&mut self, _addr: EvalValue, _value: EvalValue, _ty: Type) -> EvalValue {
            unreachable!()
        }

        fn alloca(&mut self, _ty: Type) -> EvalValue {
            unreachable!()
        }

        fn dfg(&self) -> &DataFlowGraph {
            &self.dfg
        }
    }

    #[test]
    fn narrow_unsigned_saturating_ops_zero_extend_results() {
        let hi = TestHasInst;
        let lhs = crate::ValueId::from_u32(0);
        let rhs = crate::ValueId::from_u32(1);
        let mut state = TestState::new([
            (
                lhs,
                EvalValue::Imm(Immediate::from_i256(I256::from(255u16), Type::I256)),
            ),
            (
                rhs,
                EvalValue::Imm(Immediate::from_i256(I256::from(1u8), Type::I256)),
            ),
        ]);

        assert_eq!(
            EvmUaddsat::new(&hi, lhs, rhs, Type::I8).interpret(&mut state),
            single_result(EvalValue::Imm(Immediate::from_i256(
                I256::from(255u16),
                Type::I256,
            )))
        );
        assert_eq!(
            EvmUsubsat::new(&hi, rhs, lhs, Type::I8).interpret(&mut state),
            single_result(EvalValue::Imm(Immediate::from_i256(
                I256::from(0u8),
                Type::I256,
            )))
        );

        state.values.insert(
            lhs,
            EvalValue::Imm(Immediate::from_i256(I256::from(200u16), Type::I256)),
        );
        state.values.insert(
            rhs,
            EvalValue::Imm(Immediate::from_i256(I256::from(2u8), Type::I256)),
        );
        assert_eq!(
            EvmUmulsat::new(&hi, lhs, rhs, Type::I8).interpret(&mut state),
            single_result(EvalValue::Imm(Immediate::from_i256(
                I256::from(255u16),
                Type::I256,
            )))
        );
    }

    #[test]
    fn narrow_signed_saturating_ops_sign_extend_results() {
        let hi = TestHasInst;
        let lhs = crate::ValueId::from_u32(0);
        let rhs = crate::ValueId::from_u32(1);
        let mut state = TestState::new([
            (
                lhs,
                EvalValue::Imm(Immediate::from_i256(I256::from(127u8), Type::I256)),
            ),
            (
                rhs,
                EvalValue::Imm(Immediate::from_i256(I256::from(1u8), Type::I256)),
            ),
        ]);

        assert_eq!(
            EvmSaddsat::new(&hi, lhs, rhs, Type::I8).interpret(&mut state),
            single_result(EvalValue::Imm(Immediate::from_i256(
                I256::from(127u8),
                Type::I256,
            )))
        );

        state.values.insert(
            lhs,
            EvalValue::Imm(Immediate::from_i256(I256::from(-128i16), Type::I256)),
        );
        assert_eq!(
            EvmSsubsat::new(&hi, lhs, rhs, Type::I8).interpret(&mut state),
            single_result(EvalValue::Imm(Immediate::from_i256(
                I256::from(-128i16),
                Type::I256,
            )))
        );

        state.values.insert(
            lhs,
            EvalValue::Imm(Immediate::from_i256(I256::from(100u8), Type::I256)),
        );
        state.values.insert(
            rhs,
            EvalValue::Imm(Immediate::from_i256(I256::from(2u8), Type::I256)),
        );
        assert_eq!(
            EvmSmulsat::new(&hi, lhs, rhs, Type::I8).interpret(&mut state),
            single_result(EvalValue::Imm(Immediate::from_i256(
                I256::from(127u8),
                Type::I256,
            )))
        );
    }
}
