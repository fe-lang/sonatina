//! This module contains Sonatina IR types definitions.

use std::fmt;

/// Sonatina IR types definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    I8,
    I16,
    I32,
    I64,
    I128,
    I256,
    Bool,
    Array { elem_ty: Box<Type>, len: usize },
}

pub type U256 = primitive_types::U256;

impl Type {
    pub fn make_array(elem_ty: Type, len: usize) -> Self {
        Self::Array {
            elem_ty: elem_ty.into(),
            len,
        }
    }

    pub fn is_integral(&self) -> bool {
        !matches!(self, Self::Array { .. })
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::I8 => f.write_str("i8"),
            Self::I16 => f.write_str("i16"),
            Self::I32 => f.write_str("i32"),
            Self::I64 => f.write_str("i64"),
            Self::I128 => f.write_str("i128"),
            Self::I256 => f.write_str("i256"),
            Self::Bool => f.write_str("bool"),
            Self::Array { elem_ty, len } => f.write_fmt(format_args!("[{};{}]", elem_ty, len)),
        }
    }
}
