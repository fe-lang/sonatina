use super::{Action, EvalValue, Interpret, State};
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

impl Interpret for EvmUdiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(
            lhs,
            rhs,
            |lhs, rhs| {
                if rhs.is_zero() { rhs } else { lhs.udiv(rhs) }
            },
        )
    }
}

impl Interpret for EvmSdiv {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(
            lhs,
            rhs,
            |lhs, rhs| {
                if rhs.is_zero() { rhs } else { lhs.sdiv(rhs) }
            },
        )
    }
}

impl Interpret for EvmUmod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(
            lhs,
            rhs,
            |lhs, rhs| {
                if rhs.is_zero() { rhs } else { lhs.urem(rhs) }
            },
        )
    }
}

impl Interpret for EvmSmod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());

        EvalValue::zip_with_imm(
            lhs,
            rhs,
            |lhs, rhs| {
                if rhs.is_zero() { rhs } else { lhs.srem(rhs) }
            },
        )
    }
}

impl Interpret for EvmAddMod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let modulus = state.lookup_val(*self.modulus());

        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs), EvalValue::Imm(modulus)) =
            (lhs, rhs, modulus)
        else {
            return EvalValue::Undef;
        };

        debug_assert_eq!(lhs.ty(), rhs.ty());
        debug_assert_eq!(lhs.ty(), modulus.ty());

        let ty = lhs.ty();
        let result = evm_addmod(imm_to_u256(lhs), imm_to_u256(rhs), imm_to_u256(modulus));
        EvalValue::Imm(u256_to_imm(result, ty))
    }
}

impl Interpret for EvmMulMod {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let lhs = state.lookup_val(*self.lhs());
        let rhs = state.lookup_val(*self.rhs());
        let modulus = state.lookup_val(*self.modulus());

        let (EvalValue::Imm(lhs), EvalValue::Imm(rhs), EvalValue::Imm(modulus)) =
            (lhs, rhs, modulus)
        else {
            return EvalValue::Undef;
        };

        debug_assert_eq!(lhs.ty(), rhs.ty());
        debug_assert_eq!(lhs.ty(), modulus.ty());

        let ty = lhs.ty();
        let result = evm_mulmod(imm_to_u256(lhs), imm_to_u256(rhs), imm_to_u256(modulus));
        EvalValue::Imm(u256_to_imm(result, ty))
    }
}

impl Interpret for EvmExp {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let base = state.lookup_val(*self.base());
        let exponent = state.lookup_val(*self.exponent());

        let (EvalValue::Imm(base), EvalValue::Imm(exponent)) = (base, exponent) else {
            return EvalValue::Undef;
        };

        debug_assert_eq!(base.ty(), exponent.ty());

        let ty = base.ty();
        let mask = mask_for_ty(ty);
        let result = evm_exp(imm_to_u256(base), imm_to_u256(exponent), mask);
        EvalValue::Imm(u256_to_imm(result, ty))
    }
}

impl Interpret for EvmByte {
    fn interpret(&self, state: &mut dyn State) -> EvalValue {
        state.set_action(Action::Continue);

        let pos = state.lookup_val(*self.pos());
        let value = state.lookup_val(*self.value());

        let (EvalValue::Imm(pos), EvalValue::Imm(value)) = (pos, value) else {
            return EvalValue::Undef;
        };

        debug_assert_eq!(pos.ty(), value.ty());

        let ty = value.ty();
        let value_bytes = bits_for_ty(ty).div_ceil(8) as usize;

        let result = evm_byte(imm_to_u256(pos), imm_to_u256(value), value_bytes);
        EvalValue::Imm(u256_to_imm(result, ty))
    }
}
