use std::ops;

use crate::ir::{Immediate, Type, I256};

impl Immediate {
    pub(super) fn udiv(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| (lhs.to_u256() / rhs.to_u256()).into())
    }

    pub(super) fn sdiv(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| lhs.overflowing_div(rhs).0)
    }

    pub(super) fn and(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::BitAnd::bitand)
    }

    pub(super) fn or(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::BitOr::bitor)
    }

    pub(super) fn lt(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| (lhs.to_u256() < rhs.to_u256()).into())
    }

    pub(super) fn gt(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| (lhs.to_u256() > rhs.to_u256()).into())
    }

    pub(super) fn slt(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| (lhs < rhs).into())
    }

    pub(super) fn sgt(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| (lhs > rhs).into())
    }

    pub(super) fn sext(self, ty: &Type) -> Self {
        debug_assert!(&self.ty() < ty);
        Self::from_i256(self.as_i256(), ty)
    }

    pub(super) fn zext(self, ty: &Type) -> Self {
        debug_assert!(&self.ty() < ty);
        let i256: I256 = match self {
            Self::I8(val) => (val as u8).into(),
            Self::I16(val) => (val as u16).into(),
            Self::I32(val) => (val as u32).into(),
            Self::I64(val) => (val as u64).into(),
            Self::I128(val) => (val as u128).into(),
            Self::I256(_) => unreachable!(),
        };

        Self::from_i256(i256, ty)
    }

    pub(super) fn trunc(self, ty: &Type) -> Self {
        debug_assert!(&self.ty() > ty);

        Self::from_i256(self.as_i256(), ty)
    }

    pub(super) fn const_eq(self, rhs: Self) -> Self {
        debug_assert_eq!(self.ty(), rhs.ty());

        let val = (self == rhs).into();
        Self::from_i256(val, &self.ty())
    }

    pub(super) fn zero(self) -> Self {
        self.apply_unop(|_| I256::zero())
    }

    pub(super) fn one(self) -> Self {
        self.apply_unop(|_| I256::one())
    }

    pub(super) fn is_zero(self) -> bool {
        self.apply_unop_raw(|val| val.is_zero())
    }

    fn as_i256(self) -> I256 {
        match self {
            Self::I8(val) => val.into(),
            Self::I16(val) => val.into(),
            Self::I32(val) => val.into(),
            Self::I64(val) => val.into(),
            Self::I128(val) => val.into(),
            Self::I256(val) => val,
        }
    }

    fn from_i256(val: I256, ty: &Type) -> Self {
        match ty {
            Type::I8 => Self::I8(val.trunc_to_i8()),
            Type::I16 => Self::I16(val.trunc_to_i16()),
            Type::I32 => Self::I32(val.trunc_to_i32()),
            Type::I64 => Self::I64(val.trunc_to_i64()),
            Type::I128 => Self::I128(val.trunc_to_i128()),
            Type::I256 => Self::I256(val),
            Type::Array { .. } => unreachable!(),
        }
    }

    fn apply_binop<F>(self, rhs: Self, f: F) -> Self
    where
        F: FnOnce(I256, I256) -> I256,
    {
        debug_assert_eq!(self.ty(), rhs.ty());

        let res = self.apply_binop_raw(rhs, f);
        Self::from_i256(res, &self.ty())
    }

    fn apply_binop_raw<F, R>(self, rhs: Self, f: F) -> R
    where
        F: FnOnce(I256, I256) -> R,
    {
        debug_assert_eq!(self.ty(), rhs.ty());

        let lhs = self.as_i256();
        let rhs = rhs.as_i256();
        f(lhs, rhs)
    }

    fn apply_unop<F>(self, f: F) -> Self
    where
        F: FnOnce(I256) -> I256,
    {
        let res = self.apply_unop_raw(f);
        Self::from_i256(res, &self.ty())
    }

    fn apply_unop_raw<F, R>(self, f: F) -> R
    where
        F: FnOnce(I256) -> R,
    {
        let lhs = self.as_i256();
        f(lhs)
    }
}

impl ops::Add for Immediate {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| lhs.overflowing_add(rhs).0)
    }
}

impl ops::Sub for Immediate {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| lhs.overflowing_sub(rhs).0)
    }
}

impl ops::Mul for Immediate {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| lhs.overflowing_mul(rhs).0)
    }
}

impl ops::BitAnd for Immediate {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::BitAnd::bitand)
    }
}

impl ops::BitOr for Immediate {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::BitOr::bitor)
    }
}

impl ops::Not for Immediate {
    type Output = Self;

    fn not(self) -> Self {
        self.apply_unop(ops::Not::not)
    }
}

impl ops::Neg for Immediate {
    type Output = Self;

    fn neg(self) -> Self {
        self.apply_unop(ops::Neg::neg)
    }
}
