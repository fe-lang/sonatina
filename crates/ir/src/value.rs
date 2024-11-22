//! This module contains Sonatine IR value definition.
use core::fmt;
use std::ops;

use super::Type;
use crate::{
    inst::InstId,
    ir_writer::{WriteWithFunc, WriteWithModule},
    GlobalVariable, I256,
};

/// An opaque reference to [`Value`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct ValueId(pub u32);
cranelift_entity::entity_impl!(ValueId);

/// An value data definition.
#[derive(Debug, Clone)]
pub enum Value {
    /// The value is defined by an instruction.
    Inst {
        inst: InstId,
        ty: Type,
    },

    /// The value is a function argument.
    Arg {
        ty: Type,
        idx: usize,
    },

    /// The value is immediate value.
    Immediate {
        imm: Immediate,
        ty: Type,
    },

    /// The value is global value.
    Global {
        gv: GlobalVariable,
        ty: Type,
    },

    Undef {
        ty: Type,
    },
}

impl WriteWithFunc for ValueId {
    fn write(
        &self,
        ctx: &crate::ir_writer::FuncWriteCtx,
        w: &mut impl std::io::Write,
    ) -> std::io::Result<()> {
        if let Some(name) = ctx.dbg.value_name(ctx.func, ctx.func_ref, *self) {
            write!(w, "{name}")
        } else {
            match ctx.func.dfg.value(*self) {
                Value::Immediate { imm, ty } => {
                    write!(w, "{}.", imm)?;
                    ty.write(ctx.func.ctx(), w)
                }
                Value::Global { gv, .. } => ctx
                    .func
                    .dfg
                    .ctx
                    .with_gv_store(|s| write!(w, "%{}", s.gv_data(*gv).symbol)),
                Value::Undef { ty } => {
                    write!(w, "undef.")?;
                    ty.write(ctx.func.ctx(), w)
                }
                _ => {
                    write!(w, "v{}", self.0)
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Immediate {
    I1(bool),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    I256(I256),
}

impl Immediate {
    pub fn ty(&self) -> Type {
        match self {
            Self::I1(..) => Type::I1,
            Self::I8(..) => Type::I8,
            Self::I16(..) => Type::I16,
            Self::I32(..) => Type::I32,
            Self::I64(..) => Type::I64,
            Self::I128(..) => Type::I128,
            Self::I256(..) => Type::I256,
        }
    }

    pub fn udiv(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| (lhs.to_u256() / rhs.to_u256()).into())
    }

    pub fn sdiv(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| lhs.overflowing_div(rhs).0)
    }

    pub fn urem(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| (lhs.to_u256() % rhs.to_u256()).into())
    }

    pub fn srem(self, rhs: Self) -> Self {
        self.apply_binop(rhs, |lhs, rhs| lhs.overflowing_rem(rhs).0)
    }

    pub fn lt(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs.to_u256() < rhs.to_u256()).into())
    }

    pub fn gt(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs.to_u256() > rhs.to_u256()).into())
    }

    pub fn slt(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs < rhs).into())
    }

    pub fn sgt(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs > rhs).into())
    }

    pub fn le(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs.to_u256() <= rhs.to_u256()).into())
    }

    pub fn ge(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs.to_u256() >= rhs.to_u256()).into())
    }

    pub fn sle(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs <= rhs).into())
    }

    pub fn sge(self, rhs: Self) -> Self {
        self.apply_binop_raw(rhs, |lhs, rhs| (lhs >= rhs).into())
    }

    pub fn sext(self, ty: Type) -> Self {
        debug_assert!(self.ty() <= ty);
        Self::from_i256(self.as_i256(), ty)
    }

    pub fn zext(self, ty: Type) -> Self {
        debug_assert!(self.ty() <= ty);
        let i256: I256 = match self {
            Self::I1(val) => (val as u8).into(),
            Self::I8(val) => (val as u8).into(),
            Self::I16(val) => (val as u16).into(),
            Self::I32(val) => (val as u32).into(),
            Self::I64(val) => (val as u64).into(),
            Self::I128(val) => (val as u128).into(),
            Self::I256(val) => val,
        };

        Self::from_i256(i256, ty)
    }

    pub fn trunc(self, ty: Type) -> Self {
        debug_assert!(self.ty() >= ty);

        Self::from_i256(self.as_i256(), ty)
    }

    pub fn imm_eq(self, rhs: Self) -> Self {
        debug_assert_eq!(self.ty(), rhs.ty());

        (self == rhs).into()
    }

    pub fn imm_ne(self, rhs: Self) -> Self {
        debug_assert_eq!(self.ty(), rhs.ty());

        (self != rhs).into()
    }

    pub fn zero(ty: Type) -> Self {
        let val = I256::zero();
        Self::from_i256(val, ty)
    }

    pub fn one(ty: Type) -> Self {
        let val = I256::one();
        Self::from_i256(val, ty)
    }

    pub fn all_one(ty: Type) -> Self {
        Self::from_i256(I256::all_one(), ty)
    }

    pub fn is_zero(self) -> bool {
        self.apply_unop_raw(|val| val.is_zero())
    }

    pub fn is_one(self) -> bool {
        self.apply_unop_raw(|val| val == I256::one())
    }

    pub fn is_positive(self) -> bool {
        self.apply_unop_raw(|val| val.is_positive())
    }

    pub fn is_negative(&self) -> bool {
        self.apply_unop_raw(|val| val.is_negative())
    }

    pub fn is_all_one(self) -> bool {
        self == Self::all_one(self.ty())
    }

    pub fn is_two(self) -> bool {
        self.apply_unop_raw(|val| val == I256::one().overflowing_add(I256::one()).0)
    }

    pub fn is_power_of_two(self) -> bool {
        (self & (self - Immediate::one(self.ty()))).is_zero()
    }

    pub fn as_i256(self) -> I256 {
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

    pub fn as_usize(self) -> usize {
        let val = if self.is_negative() { -self } else { self };
        val.as_i256().to_u256().as_usize()
    }

    pub fn from_i256(val: I256, ty: Type) -> Self {
        match ty {
            Type::I1 => Self::I1(val.trunc_to_i1()),
            Type::I8 => Self::I8(val.trunc_to_i8()),
            Type::I16 => Self::I16(val.trunc_to_i16()),
            Type::I32 => Self::I32(val.trunc_to_i32()),
            Type::I64 => Self::I64(val.trunc_to_i64()),
            Type::I128 => Self::I128(val.trunc_to_i128()),
            Type::I256 => Self::I256(val),
            _ => unreachable!(),
        }
    }

    fn apply_binop<F>(self, rhs: Self, f: F) -> Self
    where
        F: FnOnce(I256, I256) -> I256,
    {
        debug_assert_eq!(self.ty(), rhs.ty());

        let res = self.apply_binop_raw(rhs, f);
        Self::from_i256(res, self.ty())
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
        Self::from_i256(res, self.ty())
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

impl ops::Shl for Immediate {
    type Output = Self;

    fn shl(self, rhs: Self) -> Self::Output {
        self.apply_binop(rhs, ops::Shl::shl)
    }
}

impl ops::Shr for Immediate {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        self.apply_binop(rhs, ops::Shl::shl)
    }
}

impl fmt::Display for Immediate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::I1(v) => {
                if *v {
                    write!(f, "1")
                } else {
                    write!(f, "0")
                }
            }
            Self::I8(v) => write!(f, "{}", v),
            Self::I16(v) => write!(f, "{}", v),
            Self::I32(v) => write!(f, "{}", v),
            Self::I64(v) => write!(f, "{}", v),
            Self::I128(v) => write!(f, "{}", v),
            Self::I256(v) => write!(f, "{}", v),
        }
    }
}

macro_rules! imm_from_primary {
    ($prim_ty:ty, $inner_ty:ty, $immediate_variant:expr) => {
        impl From<$prim_ty> for Immediate {
            fn from(imm: $prim_ty) -> Self {
                $immediate_variant(imm as $inner_ty)
            }
        }
    };
}

imm_from_primary!(bool, bool, Immediate::I1);
imm_from_primary!(i8, i8, Immediate::I8);
imm_from_primary!(u8, i8, Immediate::I8);
imm_from_primary!(i16, i16, Immediate::I16);
imm_from_primary!(u16, i16, Immediate::I16);
imm_from_primary!(i32, i32, Immediate::I32);
imm_from_primary!(u32, i32, Immediate::I32);
imm_from_primary!(i64, i64, Immediate::I64);
imm_from_primary!(u64, i64, Immediate::I64);
imm_from_primary!(i128, i128, Immediate::I128);
imm_from_primary!(u128, i128, Immediate::I128);
imm_from_primary!(I256, I256, Immediate::I256);
