//! This module contains Sonatine IR value definition.

use id_arena::Id;

use super::{Block, Insn, Type};

/// An opaque reference to [`ValueData`].
pub type Value = Id<ValueData>;

/// An value data definition.
pub enum ValueData {
    /// The value is defined by instruction.
    Insn { insn: Insn, ty: Type },

    /// The value is a block parameter.
    Param { block: Block, ty: Type },
}
