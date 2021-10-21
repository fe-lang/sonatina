//! This module contains function layout information including block order and instruction order.
use cranelift_entity::SecondaryMap;

use super::{Block, Insn};

#[derive(Debug, Clone)]
pub struct Layout {
    blocks: SecondaryMap<Block, BlockNode>,
    insns: SecondaryMap<Insn, InsnNode>,
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
            blocks: SecondaryMap::new(),
            insns: SecondaryMap::new(),
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
        self.blocks[block].prev
    }

    pub fn next_block_of(&self, block: Block) -> Option<Block> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[block].next
    }

    pub fn is_block_inserted(&self, block: Block) -> bool {
        self.blocks.get(block).is_some()
    }

    pub fn first_insn_of(&self, block: Block) -> Option<Insn> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[block].first_insn
    }

    pub fn last_insn_of(&self, block: Block) -> Option<Insn> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[block].last_insn
    }

    pub fn prev_insn_of(&self, insn: Insn) -> Option<Insn> {
        debug_assert!(self.is_insn_inserted(insn));
        self.insns[insn].prev
    }

    pub fn next_insn_of(&self, insn: Insn) -> Option<Insn> {
        debug_assert!(self.is_insn_inserted(insn));
        self.insns[insn].next
    }

    pub fn insn_block(&self, insn: Insn) -> Block {
        debug_assert!(self.is_insn_inserted(insn));
        self.insns[insn].block.unwrap()
    }

    pub fn is_insn_inserted(&self, insn: Insn) -> bool {
        self.insns.get(insn).is_some()
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
            next: self.blocks[block].first_insn,
            insns: &self.insns,
        }
    }

    pub fn append_block(&mut self, block: Block) {
        debug_assert!(!self.is_block_inserted(block));

        let mut block_node = BlockNode::default();

        if let Some(last_block) = self.last_block {
            let last_block_node = &mut self.blocks[last_block];
            last_block_node.next = Some(block);
            block_node.prev = Some(last_block);
        } else {
            self.first_block = Some(block);
        }

        self.blocks[block] = block_node;
        self.last_block = Some(block);
    }

    pub fn insert_block_before(&mut self, block: Block, before: Block) {
        debug_assert!(self.is_block_inserted(before));
        debug_assert!(!self.is_block_inserted(block));

        let mut block_node = BlockNode::default();

        match self.blocks[before].prev {
            Some(prev) => {
                block_node.prev = Some(prev);
                self.blocks[prev].next = Some(block);
            }
            None => self.first_block = Some(block),
        }

        block_node.next = Some(before);
        self.blocks[before].prev = Some(block);
        self.blocks[block] = block_node;
    }

    pub fn insert_block_after(&mut self, block: Block, after: Block) {
        debug_assert!(self.is_block_inserted(after));
        debug_assert!(!self.is_block_inserted(block));

        let mut block_node = BlockNode::default();

        match self.blocks[after].next {
            Some(next) => {
                block_node.next = Some(next);
                self.blocks[next].prev = Some(block);
            }
            None => self.last_block = Some(block),
        }
        block_node.prev = Some(after);
        self.blocks[after].next = Some(block);
        self.blocks[block] = block_node;
    }

    pub fn remove_block(&mut self, block: Block) {
        debug_assert!(self.is_block_inserted(block));

        let block_node = &mut self.blocks[block];
        let prev_block = block_node.prev;
        let next_block = block_node.next;
        match (prev_block, next_block) {
            (Some(prev), Some(next)) => {
                self.blocks[prev].next = Some(next);
                self.blocks[next].prev = Some(prev);
            }
            (Some(prev), None) => {
                self.blocks[prev].next = None;
                self.last_block = Some(prev);
            }
            (None, Some(next)) => {
                self.blocks[next].prev = None;
                self.first_block = Some(next);
            }
            (None, None) => {
                self.first_block = None;
                self.last_block = None
            }
        }

        self.blocks[block] = BlockNode::default();
    }

    pub fn append_insn(&mut self, insn: Insn, block: Block) {
        debug_assert!(self.is_block_inserted(block));
        debug_assert!(!self.is_insn_inserted(insn));

        let block_node = &mut self.blocks[block];
        let mut insn_node = InsnNode::with_block(block);

        if let Some(last_insn) = block_node.last_insn {
            insn_node.prev = Some(last_insn);
            self.insns[last_insn].next = Some(insn);
        } else {
            block_node.first_insn = Some(insn);
        }

        block_node.last_insn = Some(insn);
        self.insns[insn] = insn_node;
    }

    pub fn prepend_insn(&mut self, insn: Insn, block: Block) {
        debug_assert!(self.is_block_inserted(block));
        debug_assert!(!self.is_insn_inserted(insn));

        let block_node = &mut self.blocks[block];
        let mut insn_node = InsnNode::with_block(block);

        if let Some(first_insn) = block_node.first_insn {
            insn_node.next = Some(first_insn);
            self.insns[first_insn].prev = Some(insn);
        } else {
            block_node.last_insn = Some(insn);
        }

        block_node.first_insn = Some(insn);
        self.insns[insn] = insn_node;
    }

    pub fn insert_insn_before(&mut self, insn: Insn, before: Insn) {
        debug_assert!(self.is_insn_inserted(before));
        debug_assert!(!self.is_insn_inserted(insn));

        let before_insn_node = &self.insns[before];
        let block = before_insn_node.block.unwrap();
        let mut insn_node = InsnNode::with_block(block);

        match before_insn_node.prev {
            Some(prev) => {
                insn_node.prev = Some(prev);
                self.insns[prev].next = Some(insn);
            }
            None => self.blocks[block].first_insn = Some(insn),
        }
        insn_node.next = Some(before);
        self.insns[before].prev = Some(insn);
        self.insns[insn] = insn_node;
    }

    pub fn insert_insn_after(&mut self, insn: Insn, after: Insn) {
        debug_assert!(self.is_insn_inserted(after));
        debug_assert!(!self.is_insn_inserted(insn));

        let after_insn_node = &self.insns[after];
        let block = after_insn_node.block.unwrap();
        let mut insn_node = InsnNode::with_block(block);

        match after_insn_node.next {
            Some(next) => {
                insn_node.next = Some(next);
                self.insns[next].prev = Some(insn);
            }
            None => self.blocks[block].last_insn = Some(insn),
        }
        insn_node.prev = Some(after);
        self.insns[after].next = Some(insn);
        self.insns[insn] = insn_node;
    }

    /// Remove instruction from the layout.
    pub fn remove_insn(&mut self, insn: Insn) {
        debug_assert!(self.is_insn_inserted(insn));

        let insn_node = &self.insns[insn];
        let block_node = &mut self.blocks[insn_node.block.unwrap()];
        let prev_insn = insn_node.prev;
        let next_insn = insn_node.next;
        match (prev_insn, next_insn) {
            (Some(prev), Some(next)) => {
                self.insns[prev].next = Some(next);
                self.insns[next].prev = Some(prev);
            }
            (Some(prev), None) => {
                self.insns[prev].next = None;
                block_node.last_insn = Some(prev);
            }
            (None, Some(next)) => {
                self.insns[next].prev = None;
                block_node.first_insn = Some(next);
            }
            (None, None) => {
                block_node.first_insn = None;
                block_node.last_insn = None;
            }
        }

        self.insns[insn] = InsnNode::default();
    }
}

struct BlockIter<'a> {
    next: Option<Block>,
    blocks: &'a SecondaryMap<Block, BlockNode>,
}

impl<'a> Iterator for BlockIter<'a> {
    type Item = Block;

    fn next(&mut self) -> Option<Block> {
        let next = self.next?;
        self.next = self.blocks[next].next;
        Some(next)
    }
}

struct InsnIter<'a> {
    next: Option<Insn>,
    insns: &'a SecondaryMap<Insn, InsnNode>,
}

impl<'a> Iterator for InsnIter<'a> {
    type Item = Insn;

    fn next(&mut self) -> Option<Insn> {
        let next = self.next?;
        self.next = self.insns[next].next;
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

#[derive(Debug, Clone, Default)]
struct InsnNode {
    /// An block in which the insn exists.
    block: Option<Block>,
    /// A previous instruction.
    prev: Option<Insn>,
    /// A next instruction.
    next: Option<Insn>,
}

impl InsnNode {
    fn with_block(block: Block) -> Self {
        Self {
            block: Some(block),
            prev: None,
            next: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use super::super::{dfg::DataFlowGraph, insn::ImmediateOp, InsnData};

    impl DataFlowGraph {
        /// Returns dummy instruction.
        fn make_dummy_insn(&mut self) -> Insn {
            let insn_data = InsnData::Immediate {
                code: ImmediateOp::I8(0),
            };
            self.make_insn(insn_data)
        }
    }

    #[test]
    fn test_block_insertion() {
        let mut layout = Layout::new();
        let mut dfg = DataFlowGraph::new();
        assert_eq!(layout.first_block, None);
        assert_eq!(layout.last_block, None);

        // block1.
        let b1 = dfg.make_block();
        layout.append_block(b1);
        assert_eq!(layout.first_block, Some(b1));
        assert_eq!(layout.last_block, Some(b1));
        assert_eq!(layout.prev_block_of(b1), None);
        assert_eq!(layout.next_block_of(b1), None);

        // block1 -> block2.
        let b2 = dfg.make_block();
        layout.append_block(b2);
        assert_eq!(layout.first_block, Some(b1));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b1), None);
        assert_eq!(layout.next_block_of(b1), Some(b2));
        assert_eq!(layout.prev_block_of(b2), Some(b1));
        assert_eq!(layout.next_block_of(b2), None);

        // block1 -> block3 -> block2.
        let b3 = dfg.make_block();
        layout.insert_block_after(b3, b1);
        assert_eq!(layout.first_block, Some(b1));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b2), Some(b3));
        assert_eq!(layout.next_block_of(b1), Some(b3));
        assert_eq!(layout.prev_block_of(b3), Some(b1));
        assert_eq!(layout.next_block_of(b3), Some(b2));

        // block1 -> block3 -> block4 -> block2.
        let b4 = dfg.make_block();
        layout.insert_block_before(b4, b2);
        assert_eq!(layout.first_block, Some(b1));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b2), Some(b4));
        assert_eq!(layout.next_block_of(b3), Some(b4));
        assert_eq!(layout.prev_block_of(b4), Some(b3));
        assert_eq!(layout.next_block_of(b4), Some(b2));
    }

    #[test]
    fn test_block_removal() {
        let mut layout = Layout::new();
        let mut dfg = DataFlowGraph::new();

        // block1 -> block2 -> block3 -> block4.
        let b1 = dfg.make_block();
        let b2 = dfg.make_block();
        let b3 = dfg.make_block();
        let b4 = dfg.make_block();
        layout.append_block(b1);
        layout.append_block(b2);
        layout.append_block(b3);
        layout.append_block(b4);

        // block1 -> block2 -> block4.
        layout.remove_block(b3);
        assert_eq!(layout.first_block, Some(b1));
        assert_eq!(layout.last_block, Some(b4));
        assert_eq!(layout.prev_block_of(b4), Some(b2));
        assert_eq!(layout.next_block_of(b2), Some(b4));

        // block1 -> block2.
        layout.remove_block(b4);
        assert_eq!(layout.first_block, Some(b1));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b2), Some(b1));
        assert_eq!(layout.next_block_of(b2), None);

        // block2.
        layout.remove_block(b1);
        assert_eq!(layout.first_block, Some(b2));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b2), None);
        assert_eq!(layout.next_block_of(b2), None);

        // .
        layout.remove_block(b2);
        assert_eq!(layout.first_block, None);
        assert_eq!(layout.last_block, None);
    }

    #[test]
    fn test_insn_insertion() {
        let mut layout = Layout::new();
        let mut dfg = DataFlowGraph::new();
        let b1 = dfg.make_block();
        layout.append_block(b1);
        assert_eq!(layout.first_insn_of(b1), None);
        assert_eq!(layout.last_insn_of(b1), None);

        // insn1.
        let i1 = dfg.make_dummy_insn();
        layout.append_insn(i1, b1);
        assert_eq!(layout.first_insn_of(b1), Some(i1));
        assert_eq!(layout.last_insn_of(b1), Some(i1));
        assert_eq!(layout.insn_block(i1), b1);
        assert_eq!(layout.prev_insn_of(i1), None);
        assert_eq!(layout.next_insn_of(i1), None);

        // insn1 -> insn2.
        let i2 = dfg.make_dummy_insn();
        layout.append_insn(i2, b1);
        assert_eq!(layout.first_insn_of(b1), Some(i1));
        assert_eq!(layout.last_insn_of(b1), Some(i2));
        assert_eq!(layout.prev_insn_of(i2), Some(i1));
        assert_eq!(layout.next_insn_of(i1), Some(i2));

        // insn1 -> insn3 -> insn2.
        let i3 = dfg.make_dummy_insn();
        layout.insert_insn_after(i3, i1);
        assert_eq!(layout.first_insn_of(b1), Some(i1));
        assert_eq!(layout.last_insn_of(b1), Some(i2));
        assert_eq!(layout.next_insn_of(i1), Some(i3));
        assert_eq!(layout.prev_insn_of(i2), Some(i3));
        assert_eq!(layout.prev_insn_of(i3), Some(i1));
        assert_eq!(layout.next_insn_of(i3), Some(i2));

        // insn1 -> insn3 -> insn4 -> insn2.
        let i4 = dfg.make_dummy_insn();
        layout.insert_insn_before(i4, i2);
        assert_eq!(layout.first_insn_of(b1), Some(i1));
        assert_eq!(layout.last_insn_of(b1), Some(i2));
        assert_eq!(layout.next_insn_of(i3), Some(i4));
        assert_eq!(layout.prev_insn_of(i2), Some(i4));
        assert_eq!(layout.prev_insn_of(i4), Some(i3));
        assert_eq!(layout.next_insn_of(i4), Some(i2));
    }

    #[test]
    fn test_insn_removal() {
        let mut layout = Layout::new();
        let mut dfg = DataFlowGraph::new();
        let b1 = dfg.make_block();
        layout.append_block(b1);

        // insn1 -> insn2 -> insn3 -> insn4.
        let i1 = dfg.make_dummy_insn();
        let i2 = dfg.make_dummy_insn();
        let i3 = dfg.make_dummy_insn();
        let i4 = dfg.make_dummy_insn();
        layout.append_insn(i1, b1);
        layout.append_insn(i2, b1);
        layout.append_insn(i3, b1);
        layout.append_insn(i4, b1);

        // insn1 -> insn2 -> insn4.
        layout.remove_insn(i3);
        assert_eq!(layout.first_insn_of(b1), Some(i1));
        assert_eq!(layout.last_insn_of(b1), Some(i4));
        assert_eq!(layout.next_insn_of(i2), Some(i4));
        assert_eq!(layout.prev_insn_of(i4), Some(i2));

        // insn1 -> insn2.
        layout.remove_insn(i4);
        assert_eq!(layout.first_insn_of(b1), Some(i1));
        assert_eq!(layout.last_insn_of(b1), Some(i2));
        assert_eq!(layout.next_insn_of(i1), Some(i2));
        assert_eq!(layout.prev_insn_of(i2), Some(i1));

        // insn2.
        layout.remove_insn(i1);
        assert_eq!(layout.first_insn_of(b1), Some(i2));
        assert_eq!(layout.last_insn_of(b1), Some(i2));
        assert_eq!(layout.next_insn_of(i2), None);
        assert_eq!(layout.prev_insn_of(i2), None);

        // .
        layout.remove_insn(i2);
        assert_eq!(layout.first_insn_of(b1), None);
        assert_eq!(layout.last_insn_of(b1), None);
    }
}
