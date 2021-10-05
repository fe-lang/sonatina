//! This module contains Sonatine IR instructions definitions.

use std::collections::HashSet;

use id_arena::{Arena, Id};

use super::{Insn, InsnData, Value, ValueData};

#[derive(Default, Debug)]
pub struct DataFlowGraph {
    blocks: Arena<BlockData>,
    insns: Arena<InsnData>,
    values: Arena<ValueData>,
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

    pub fn store_value(&mut self, value: ValueData) -> Value {
        self.values.alloc(value)
    }

    pub fn insn_data(&self, insn: Insn) -> &InsnData {
        &self.insns[insn]
    }

    pub fn insn_data_mut(&mut self, insn: Insn) -> &mut InsnData {
        &mut self.insns[insn]
    }

    pub fn block_data(&self, block: Block) -> &BlockData {
        &self.blocks[block]
    }

    pub fn block_data_mut(&mut self, block: Block) -> &mut BlockData {
        &mut self.blocks[block]
    }
}

/// An opaque reference to [`BlockData`]
pub type Block = Id<BlockData>;

/// A block data definition.
/// A Block data doesn't hold any information for layout of a program. It is managed by
/// [`super::layout::Layout`].
#[derive(Debug, Default, Clone)]
pub struct BlockData {
    params: HashSet<Value>,
}
