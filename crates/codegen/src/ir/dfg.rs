//! This module contains Sonatine IR instructions definitions.

use std::collections::HashSet;

use id_arena::{Arena, Id};

use super::Value;

pub struct DataFlowGraph {
    blocks: Arena<BlockData>,
}

impl DataFlowGraph {
    pub fn new() -> Self {
        let mut blocks = Arena::new();
        blocks.alloc(BlockData {
            params: HashSet::new(),
        });

        Self { blocks }
    }

    fn foo(&self) {
        for (id, block) in &self.blocks {
            assert_eq!(self.blocks.get(id).unwrap(), block);
        }
    }
}

/// An opaque reference to [`BlockData`]
pub type Block = Id<BlockData>;

/// A block data definition.
/// A Block data doesn't hold any information for layout of a program. It is managed by
/// [`super::layout::Layout`].
pub struct BlockData {
    params: HashSet<Value>,
}
