//! This module contains function layout information including block order and instruction order.
use std::collections::HashMap;

use super::{Block, Insn};

#[derive(Debug, Clone)]
pub struct Layout {
    blocks: HashMap<Block, BlockNode>,
    insns: HashMap<Insn, InsnNode>,
    first_block: Option<Block>,
    last_block: Option<Block>,
}

impl Default for Layout {
    fn default() -> Self {
        Self::new()
    }
}

impl Layout {
    pub fn new() -> Self {
        Self {
            blocks: HashMap::new(),
            insns: HashMap::new(),
            first_block: None,
            last_block: None,
        }
    }

    pub fn first_block(&self) -> Option<Block> {
        self.first_block
    }

    pub fn last_block(&self) -> Option<Block> {
        self.last_block
    }

    pub fn prev_block_of(&self, block: Block) -> Option<Block> {
        let block_node = self.blocks.get(&block)?;
        block_node.prev
    }

    pub fn next_block_of(&self, block: Block) -> Option<Block> {
        let block_node = self.blocks.get(&block)?;
        block_node.next
    }

    pub fn is_block_inserted(&self, block: Block) -> bool {
        self.blocks.get(&block).is_some()
    }

    pub fn append_block(&mut self, block: Block) {
        debug_assert!(!self.is_block_inserted(block));

        let mut block_node = BlockNode::default();

        if let Some(last_block) = self.last_block {
            let mut last_block_node = self.blocks.get_mut(&last_block).unwrap();
            last_block_node.prev = Some(block);
            block_node.prev = Some(last_block);
        } else {
            self.first_block = Some(block);
        }

        self.blocks.insert(block, BlockNode::default());
        self.last_block = Some(block);
    }

    pub fn insert_block_after(&mut self, block: Block, after: Block) {
        debug_assert!(!self.is_block_inserted(block) && self.is_block_inserted(after));
        if self.last_block == Some(after) {
            self.append_block(block);
        }

        let mut block_node = BlockNode::default();
        let mut after_block_node = self.blocks.get_mut(&after).unwrap();

        block_node.prev = Some(after);
        block_node.next = after_block_node.next;
        after_block_node.next = Some(block);

        self.blocks.insert(block, block_node);
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = Block> + 'a {
        BlockIter {
            next: self.first_block,
            blocks: &self.blocks,
        }
    }
}

struct BlockIter<'a> {
    next: Option<Block>,
    blocks: &'a HashMap<Block, BlockNode>,
}

impl<'a> Iterator for BlockIter<'a> {
    type Item = Block;

    fn next(&mut self) -> Option<Block> {
        let next = self.next?;
        self.next = self.blocks[&next].next;
        Some(next)
    }
}

#[derive(Default, Debug, Clone)]
struct BlockNode {
    prev: Option<Block>,
    next: Option<Block>,
    first_insn: Option<Insn>,
    last_insn: Option<Insn>,
}

#[derive(Debug, Clone)]
struct InsnNode {
    /// An block in which the insn exists.
    block: Block,
    /// A previous instruction.
    prev: Option<Insn>,
    /// A next instruction.
    next: Option<Insn>,
}
