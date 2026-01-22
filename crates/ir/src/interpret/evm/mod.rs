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
