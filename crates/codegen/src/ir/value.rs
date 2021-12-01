//! This module contains Sonatine IR value definition.

use std::fmt;

use super::{Insn, Type, I256, U256};

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
}

impl fmt::Display for Immediate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::I1(v) => {
                if *v {
                    write!(f, "-1")
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

impl From<U256> for Immediate {
    fn from(imm: U256) -> Self {
        Self::I256(imm.into())
    }
}
