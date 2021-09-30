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
        debug_assert!(self.is_block_inserted(block));
        self.blocks[&block].prev
    }

    pub fn next_block_of(&self, block: Block) -> Option<Block> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[&block].next
    }

    pub fn is_block_inserted(&self, block: Block) -> bool {
        self.blocks.get(&block).is_some()
    }

    pub fn first_insn_of(&self, block: Block) -> Option<Insn> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[&block].first_insn
    }

    pub fn last_insn_of(&self, block: Block) -> Option<Insn> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[&block].last_insn
    }

    pub fn insn_block(&self, insn: Insn) -> Block {
        debug_assert!(self.is_insn_inserted(insn));

        self.insns[&insn].block
    }

    pub fn is_insn_inserted(&self, insn: Insn) -> bool {
        self.insns.get(&insn).is_some()
    }

    pub fn iter_block(&self) -> impl Iterator<Item = Block> + '_ {
        BlockIter {
            next: self.first_block,
            blocks: &self.blocks,
        }
    }

    pub fn iter_insn(&self, block: Block) -> impl Iterator<Item = Insn> + '_ {
        debug_assert!(self.is_block_inserted(block));
        InsnIter {
            next: self.blocks[&block].first_insn,
            insns: &self.insns,
        }
    }

    pub fn append_block(&mut self, block: Block) {
        debug_assert!(!self.is_block_inserted(block));

        let mut block_node = BlockNode::default();

        if let Some(last_block) = self.last_block {
            let mut last_block_node = self.blocks.get_mut(&last_block).unwrap();
            last_block_node.next = Some(block);
            block_node.prev = Some(last_block);
        } else {
            self.first_block = Some(block);
        }

        self.blocks.insert(block, block_node);
        self.last_block = Some(block);
    }

    pub fn insert_block_before(&mut self, block: Block, before: Block) {
        debug_assert!(self.is_block_inserted(before));
        debug_assert!(!self.is_block_inserted(block));

        let mut block_node = BlockNode::default();
        let mut before_block_node = self.blocks.get_mut(&before).unwrap();

        match before_block_node.prev {
            Some(prev) => block_node.prev = Some(prev),
            None => self.first_block = Some(block),
        }

        block_node.next = Some(before);
        before_block_node.prev = Some(block);
        self.blocks.insert(block, block_node);
    }

    pub fn insert_block_after(&mut self, block: Block, after: Block) {
        debug_assert!(self.is_block_inserted(after));
        debug_assert!(!self.is_block_inserted(block));

        let mut block_node = BlockNode::default();
        let mut after_block_node = self.blocks.get_mut(&after).unwrap();

        match after_block_node.next {
            Some(next) => block_node.next = Some(next),
            None => self.last_block = Some(block),
        }
        block_node.prev = Some(after);
        after_block_node.next = Some(block);
        self.blocks.insert(block, block_node);
    }

    pub fn append_insn(&mut self, insn: Insn, block: Block) {
        debug_assert!(self.is_block_inserted(block));
        debug_assert!(!self.is_insn_inserted(insn));

        let block_node = self.blocks.get_mut(&block).unwrap();
        let mut insn_node = InsnNode::new(block);

        if let Some(last_insn) = block_node.last_insn {
            insn_node.prev = Some(last_insn);
            self.insns.get_mut(&last_insn).unwrap().next = Some(insn);
        } else {
            block_node.first_insn = Some(insn);
        }

        block_node.last_insn = Some(insn);
        self.insns.insert(insn, insn_node);
    }

    pub fn insert_insn_before(&mut self, insn: Insn, before: Insn) {
        debug_assert!(self.is_insn_inserted(before));
        debug_assert!(!self.is_insn_inserted(insn));

        let before_insn_node = self.insns.get_mut(&before).unwrap();
        let block = before_insn_node.block;
        let mut insn_node = InsnNode::new(block);

        match before_insn_node.prev {
            Some(prev) => insn_node.prev = Some(prev),
            None => self.blocks.get_mut(&block).unwrap().first_insn = Some(insn),
        }
        insn_node.next = Some(before);
        before_insn_node.prev = Some(insn);
        self.insns.insert(insn, insn_node);
    }

    pub fn insert_insn_after(&mut self, insn: Insn, after: Insn) {
        debug_assert!(self.is_insn_inserted(after));
        debug_assert!(!self.is_insn_inserted(insn));

        let after_insn_node = self.insns.get_mut(&after).unwrap();
        let block = after_insn_node.block;
        let mut insn_node = InsnNode::new(block);

        match after_insn_node.next {
            Some(next) => insn_node.next = Some(next),
            None => self.blocks.get_mut(&block).unwrap().last_insn = Some(insn),
        }
        insn_node.prev = Some(after);
        after_insn_node.next = Some(insn);
        self.insns.insert(insn, insn_node);
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

struct InsnIter<'a> {
    next: Option<Insn>,
    insns: &'a HashMap<Insn, InsnNode>,
}

impl<'a> Iterator for InsnIter<'a> {
    type Item = Insn;

    fn next(&mut self) -> Option<Insn> {
        let next = self.next?;
        self.next = self.insns[&next].next;
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

impl InsnNode {
    fn new(block: Block) -> Self {
        Self {
            block,
            prev: None,
            next: None,
        }
    }
}
