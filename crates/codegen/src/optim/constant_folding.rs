use std::ops;

use crate::ir::{
    insn::{BinaryOp, CastOp, UnaryOp},
    DataFlowGraph, Immediate, InsnData, Type, I256,
};

pub(super) fn fold_constant(dfg: &DataFlowGraph, insn_data: &InsnData) -> Option<Immediate> {
    match insn_data {
        InsnData::Unary { code, args } => {
            let arg = dfg.value_imm(args[0])?;
            Some(match *code {
                UnaryOp::Not => !arg,
                UnaryOp::Neg => -arg,
            })
        }

        InsnData::Binary { code, args } => {
            let lhs = dfg.value_imm(args[0])?;
            let rhs = dfg.value_imm(args[1])?;
            Some(match *code {
                BinaryOp::Add => lhs + rhs,
                BinaryOp::Sub => lhs - rhs,
                BinaryOp::Mul => lhs * rhs,
                BinaryOp::Udiv => lhs.udiv(rhs),
                BinaryOp::Sdiv => lhs.sdiv(rhs),
                BinaryOp::Lt => lhs.lt(rhs),
                BinaryOp::Gt => lhs.gt(rhs),
                BinaryOp::Slt => lhs.slt(rhs),
                BinaryOp::Sgt => lhs.sgt(rhs),
                BinaryOp::Le => lhs.le(rhs),
                BinaryOp::Ge => lhs.ge(rhs),
                BinaryOp::Sle => lhs.sle(rhs),
                BinaryOp::Sge => lhs.sge(rhs),
                BinaryOp::Eq => lhs.imm_eq(rhs),
                BinaryOp::Ne => lhs.imm_ne(rhs),
                BinaryOp::And => lhs & rhs,
                BinaryOp::Or => lhs | rhs,
                BinaryOp::Xor => lhs ^ rhs,
            })
        }

        InsnData::Cast { code, args, ty } => {
            let arg = dfg.value_imm(args[0])?;
            Some(match code {
                CastOp::Sext => arg.sext(ty),
                CastOp::Zext => arg.zext(ty),
                CastOp::Trunc => arg.trunc(ty),
            })
        }

        InsnData::Load { .. }
        | InsnData::Jump { .. }
        | InsnData::Branch { .. }
        | InsnData::BrTable { .. }
        | InsnData::Store { .. }
        | InsnData::Alloca { .. }
        | InsnData::Return { .. }
        | InsnData::Phi { .. } => None,
    }
}

impl Immediate {
    pub(super) fn udiv(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| (lhs.to_u256() / rhs.to_u256()).into())
    }

    pub(super) fn sdiv(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| lhs.overflowing_div(rhs).0)
    }

    pub(super) fn lt(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs.to_u256() < rhs.to_u256()).into())
    }

    pub(super) fn gt(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs.to_u256() > rhs.to_u256()).into())
    }

    pub(super) fn slt(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs < rhs).into())
    }

    pub(super) fn sgt(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs > rhs).into())
    }

    pub(super) fn le(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs.to_u256() <= rhs.to_u256()).into())
    }

    pub(super) fn ge(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs.to_u256() >= rhs.to_u256()).into())
    }

    pub(super) fn sle(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs <= rhs).into())
    }

    pub(super) fn sge(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs >= rhs).into())
    }

    pub(super) fn sext(self, ty: &Type) -> Self {
        debug_assert!(&self.ty() < ty);
        Self::from_i256(self.as_i256(), ty)
    }

    pub(super) fn zext(self, ty: &Type) -> Self {
        debug_assert!(&self.ty() < ty);
        let i256: I256 = match self {
            Self::I1(val) => (val as u8).into(),
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

    pub(super) fn imm_eq(self, rhs: Self) -> Self {
        debug_assert_eq!(self.ty(), rhs.ty());

        (self == rhs).into()
    }

    pub(super) fn imm_ne(self, rhs: Self) -> Self {
        debug_assert_eq!(self.ty(), rhs.ty());

        (self != rhs).into()
    }

    pub(super) fn zero(ty: &Type) -> Self {
        let val = I256::zero();
        Self::from_i256(val, ty)
    }

    pub(super) fn one(ty: &Type) -> Self {
        let val = I256::one();
        Self::from_i256(val, ty)
    }

    pub(super) fn all_one(ty: &Type) -> Self {
        Self::from_i256(I256::all_one(), ty)
    }

    pub(super) fn is_zero(self) -> bool {
        self.apply_unop_raw(|val| val.is_zero())
    }

    pub(super) fn is_one(self) -> bool {
        self.apply_unop_raw(|val| val == I256::one())
    }

    pub(super) fn is_all_one(self) -> bool {
        self == Self::all_one(&self.ty())
    }

    pub(super) fn is_two(self) -> bool {
        self.apply_unop_raw(|val| val == I256::one().overflowing_add(I256::one()).0)
    }

    pub(super) fn is_power_of_two(self) -> bool {
        (self & (self - Immediate::one(&self.ty()))).is_zero()
    }

    fn as_i256(self) -> I256 {
        match self {
            Self::I1(val) => val.into(),
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
            Type::I1 => Self::I1(val.trunc_to_i1()),
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

impl ops::BitXor for Immediate {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::BitXor::bitxor)
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
