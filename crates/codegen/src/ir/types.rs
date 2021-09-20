//! This module contains Sonatina IR types definitions.

/// Sonatina IR types definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    I8,
    I16,
    I32,
    I64,
    I128,
    I256,
    Array { elem_ty: Box<Type>, len: usize },
}

impl Type {
    pub fn make_array(elem_ty: Type, len: usize) -> Self {
        Self::Array {
            elem_ty: elem_ty.into(),
            len,
        }
    }
}
