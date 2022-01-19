//! This module contains Sonatina IR types definitions.

use std::{cmp, fmt};

/// Sonatina IR types definition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    I1,
    I8,
    I16,
    I32,
    I64,
    I128,
    I256,
    Array { elem_ty: Box<Type>, len: usize },
    Ptr { base: Box<Type> },
}

impl Type {
    pub fn make_array(elem_ty: Type, len: usize) -> Self {
        Self::Array {
            elem_ty: elem_ty.into(),
            len,
        }
    }

    pub fn make_ptr(base: Type) -> Self {
        Type::Ptr { base: base.into() }
    }

    pub fn is_integral(&self) -> bool {
        matches!(
            self,
            Self::I1 | Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::I128 | Self::I256
        )
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::I1 => write!(f, "i1"),
            Self::I8 => write!(f, "i8"),
            Self::I16 => write!(f, "i16"),
            Self::I32 => write!(f, "i32"),
            Self::I64 => write!(f, "i64"),
            Self::I128 => write!(f, "i128"),
            Self::I256 => write!(f, "i256"),
            Self::Array { elem_ty, len } => write!(f, "[{}; {}]", elem_ty, len),
            Self::Ptr { base } => write!(f, "*{}", base),
        }
    }
}

impl cmp::PartialOrd for Type {
    fn partial_cmp(&self, rhs: &Self) -> Option<cmp::Ordering> {
        use Type::*;

        if self == rhs {
            return Some(cmp::Ordering::Equal);
        }

        if !self.is_integral() || !rhs.is_integral() {
            return None;
        }

        match (self, rhs) {
            (I1, _) => Some(cmp::Ordering::Less),
            (I8, I1) => Some(cmp::Ordering::Greater),
            (I8, _) => Some(cmp::Ordering::Less),
            (I16, I1 | I8) => Some(cmp::Ordering::Greater),
            (I16, _) => Some(cmp::Ordering::Less),
            (I32, I1 | I8 | I16) => Some(cmp::Ordering::Greater),
            (I32, _) => Some(cmp::Ordering::Less),
            (I64, I128 | I256) => Some(cmp::Ordering::Less),
            (I64, _) => Some(cmp::Ordering::Greater),
            (I128, I256) => Some(cmp::Ordering::Less),
            (I128, _) => Some(cmp::Ordering::Greater),
            (I256, _) => Some(cmp::Ordering::Greater),
            (_, _) => unreachable!(),
        }
    }
}
