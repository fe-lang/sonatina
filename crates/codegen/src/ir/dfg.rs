//! This module contains Sonatine IR instructions definitions.

use std::collections::HashSet;

use id_arena::{Arena, Id};

use super::{Insn, InsnData, Value};

#[derive(Default, Debug)]
pub struct DataFlowGraph {
    blocks: Arena<BlockData>,
    insns: Arena<InsnData>,
}

impl DataFlowGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn make_block(&mut self) -> Block {
        let block = BlockData::default();
        self.blocks.alloc(block)
    }

    pub fn store_insn(&mut self, insn: InsnData) -> Insn {
        self.insns.alloc(insn)
    }
}

/// An opaque reference to [`BlockData`]
pub type Block = Id<BlockData>;

/// A block data definition.
/// A Block data doesn't hold any information for layout of a program. It is managed by
/// [`super::layout::Layout`].
#[derive(Debug, Default)]
pub struct BlockData {
    params: HashSet<Value>,
}
