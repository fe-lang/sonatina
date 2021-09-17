//! This module contains Sonatine IR instructions definitions.

use std::collections::HashSet;

use id_arena::Id;

use super::Value;

/// An opaque reference to [`BlockData`]
pub type Block = Id<BlockData>;

/// A block data definition.
/// A Block data doesn't hold any information for layout of a program. It is managed by
/// [`super::layout::Layout`].
pub struct BlockData {
    params: HashSet<Value>,
}
