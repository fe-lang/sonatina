//! This module contains Sonatine IR value definition.
use id_arena::Id;

use super::{Insn, Type};

/// An opaque reference to [`ValueData`].
pub type Value = Id<ValueData>;

/// An value data definition.
#[derive(Debug, Clone)]
pub enum ValueData {
    /// The value is defined by an instruction.
    Insn { insn: Insn, ty: Type },

    /// The value is a block parameter.
    Arg { ty: Type, idx: usize },

    /// The Alias to an other value.
    Alias { value: Value },
}
