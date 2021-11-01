//! This module contains Sonatine IR value definition.

use super::{Insn, Type};

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
}
