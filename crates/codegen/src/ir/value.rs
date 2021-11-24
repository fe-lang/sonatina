//! This module contains Sonatine IR value definition.

use std::fmt;

use super::{types::U256, Insn, Type};

/// An opaque reference to [`ValueData`].
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub struct Value(pub u32);
cranelift_entity::entity_impl!(Value);

/// An value data definition.
#[derive(Debug, Clone)]
pub enum ValueData {
    /// The value is defined by an instruction.
    Insn { insn: Insn, ty: Type },

    /// The value is a function argument.
    Arg { ty: Type, idx: usize },

    /// The value is alias to another value.
    Alias { alias: Value },

    /// The value is immediate value.
    Immediate { imm: Immediate, ty: Type },
}

#[derive(Debug, Clone, Copy)]
pub enum Immediate {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    U256(U256),
}

impl fmt::Display for Immediate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::I8(v) => write!(f, "{}", v),
            Self::I16(v) => write!(f, "{}", v),
            Self::I32(v) => write!(f, "{}", v),
            Self::I64(v) => write!(f, "{}", v),
            Self::I128(v) => write!(f, "{}", v),
            Self::U256(v) => write!(f, "{}", v),
        }
    }
}

macro_rules! impl_value_from_imm {
    ($arg_ty:ty, $imm_ty:ty, $immediate_variant:expr, $value_ty:expr) => {
        impl From<$arg_ty> for ValueData {
            fn from(imm: $arg_ty) -> Self {
                Self::Immediate {
                    imm: $immediate_variant(imm as $imm_ty),
                    ty: $value_ty,
                }
            }
        }
    };
}

impl_value_from_imm!(i8, i8, Immediate::I8, Type::I8);
impl_value_from_imm!(u8, i8, Immediate::I8, Type::I8);
impl_value_from_imm!(i16, i16, Immediate::I16, Type::I16);
impl_value_from_imm!(u16, i16, Immediate::I16, Type::I16);
impl_value_from_imm!(i32, i32, Immediate::I32, Type::I32);
impl_value_from_imm!(u32, i32, Immediate::I32, Type::I32);
impl_value_from_imm!(i64, i64, Immediate::I64, Type::I64);
impl_value_from_imm!(u64, i64, Immediate::I64, Type::I64);
impl_value_from_imm!(i128, i128, Immediate::I128, Type::I128);
impl_value_from_imm!(u128, i128, Immediate::I128, Type::I128);
impl_value_from_imm!(U256, U256, Immediate::U256, Type::I256);
