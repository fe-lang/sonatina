//! This module contains function layout information including block order and
//! instruction order.
use cranelift_entity::SecondaryMap;

use super::{BlockId, InstId};

#[derive(Debug, Clone)]
pub struct Layout {
    blocks: SecondaryMap<BlockId, BlockNode>,
    insts: SecondaryMap<InstId, InstNode>,
    entry_block: Option<BlockId>,
    last_block: Option<BlockId>,
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
            insts: SecondaryMap::new(),
            entry_block: None,
            last_block: None,
        }
    }

    pub fn entry_block(&self) -> Option<BlockId> {
        self.entry_block
    }

    pub fn last_block(&self) -> Option<BlockId> {
        self.last_block
    }

    pub fn is_last_block(&self, block: BlockId) -> bool {
        self.last_block == Some(block)
    }

    pub fn is_block_empty(&self, block: BlockId) -> bool {
        self.first_inst_of(block).is_none()
    }

    pub fn prev_block_of(&self, block: BlockId) -> Option<BlockId> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[block].prev
    }

    pub fn next_block_of(&self, block: BlockId) -> Option<BlockId> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[block].next
    }

    pub fn is_block_inserted(&self, block: BlockId) -> bool {
        Some(block) == self.entry_block || self.blocks[block] != BlockNode::default()
    }

    pub fn first_inst_of(&self, block: BlockId) -> Option<InstId> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[block].first_inst
    }

    pub fn is_first_inst(&self, inst: InstId) -> bool {
        let block = self.inst_block(inst);
        self.first_inst_of(block) == Some(inst)
    }

    pub fn last_inst_of(&self, block: BlockId) -> Option<InstId> {
        debug_assert!(self.is_block_inserted(block));
        self.blocks[block].last_inst
    }

    pub fn prev_inst_of(&self, inst: InstId) -> Option<InstId> {
        debug_assert!(self.is_inst_inserted(inst));
        self.insts[inst].prev
    }

    pub fn next_inst_of(&self, inst: InstId) -> Option<InstId> {
        debug_assert!(self.is_inst_inserted(inst));
        self.insts[inst].next
    }

    pub fn inst_block(&self, inst: InstId) -> BlockId {
        debug_assert!(self.is_inst_inserted(inst));
        self.insts[inst].block.unwrap()
    }

    pub fn is_inst_inserted(&self, inst: InstId) -> bool {
        self.insts[inst] != InstNode::default()
    }

    pub fn iter_block(&self) -> impl Iterator<Item = BlockId> + '_ {
        BlockIter {
            next: self.entry_block,
            blocks: &self.blocks,
        }
    }

    pub fn iter_inst(&self, block: BlockId) -> impl Iterator<Item = InstId> + '_ {
        debug_assert!(self.is_block_inserted(block));
        InstIter {
            next: self.blocks[block].first_inst,
            insts: &self.insts,
        }
    }

    pub fn append_block(&mut self, block: BlockId) {
        debug_assert!(!self.is_block_inserted(block));

        let mut block_node = BlockNode::default();

        if let Some(last_block) = self.last_block {
            let last_block_node = &mut self.blocks[last_block];
            last_block_node.next = Some(block);
            block_node.prev = Some(last_block);
        } else {
            self.entry_block = Some(block);
        }

        self.blocks[block] = block_node;
        self.last_block = Some(block);
    }

    pub fn insert_block_before(&mut self, block: BlockId, before: BlockId) {
        debug_assert!(self.is_block_inserted(before));
        debug_assert!(!self.is_block_inserted(block));

        let mut block_node = BlockNode::default();

        match self.blocks[before].prev {
            Some(prev) => {
                block_node.prev = Some(prev);
                self.blocks[prev].next = Some(block);
            }
            None => self.entry_block = Some(block),
        }

        block_node.next = Some(before);
        self.blocks[before].prev = Some(block);
        self.blocks[block] = block_node;
    }

    pub fn insert_block_after(&mut self, block: BlockId, after: BlockId) {
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

    pub fn remove_block(&mut self, block: BlockId) {
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
                self.entry_block = Some(next);
            }
            (None, None) => {
                self.entry_block = None;
                self.last_block = None
            }
        }

        self.blocks[block] = BlockNode::default();
    }

    pub fn append_inst(&mut self, inst: InstId, block: BlockId) {
        debug_assert!(self.is_block_inserted(block));
        debug_assert!(!self.is_inst_inserted(inst));

        let block_node = &mut self.blocks[block];
        let mut inst_node = InstNode::with_block(block);

        if let Some(last_inst) = block_node.last_inst {
            inst_node.prev = Some(last_inst);
            self.insts[last_inst].next = Some(inst);
        } else {
            block_node.first_inst = Some(inst);
        }

        block_node.last_inst = Some(inst);
        self.insts[inst] = inst_node;
    }

    pub fn prepend_inst(&mut self, inst: InstId, block: BlockId) {
        debug_assert!(self.is_block_inserted(block));
        debug_assert!(!self.is_inst_inserted(inst));

        let block_node = &mut self.blocks[block];
        let mut inst_node = InstNode::with_block(block);

        if let Some(first_inst) = block_node.first_inst {
            inst_node.next = Some(first_inst);
            self.insts[first_inst].prev = Some(inst);
        } else {
            block_node.last_inst = Some(inst);
        }

        block_node.first_inst = Some(inst);
        self.insts[inst] = inst_node;
    }

    pub fn insert_inst_before(&mut self, inst: InstId, before: InstId) {
        debug_assert!(self.is_inst_inserted(before));
        debug_assert!(!self.is_inst_inserted(inst));

        let before_inst_node = &self.insts[before];
        let block = before_inst_node.block.unwrap();
        let mut inst_node = InstNode::with_block(block);

        match before_inst_node.prev {
            Some(prev) => {
                inst_node.prev = Some(prev);
                self.insts[prev].next = Some(inst);
            }
            None => self.blocks[block].first_inst = Some(inst),
        }
        inst_node.next = Some(before);
        self.insts[before].prev = Some(inst);
        self.insts[inst] = inst_node;
    }

    pub fn insert_inst_after(&mut self, inst: InstId, after: InstId) {
        debug_assert!(self.is_inst_inserted(after));
        debug_assert!(!self.is_inst_inserted(inst));

        let after_inst_node = &self.insts[after];
        let block = after_inst_node.block.unwrap();
        let mut inst_node = InstNode::with_block(block);

        match after_inst_node.next {
            Some(next) => {
                inst_node.next = Some(next);
                self.insts[next].prev = Some(inst);
            }
            None => self.blocks[block].last_inst = Some(inst),
        }
        inst_node.prev = Some(after);
        self.insts[after].next = Some(inst);
        self.insts[inst] = inst_node;
    }

    /// Remove instruction from the layout.
    pub fn remove_inst(&mut self, inst: InstId) {
        debug_assert!(self.is_inst_inserted(inst));

        let inst_node = &self.insts[inst];
        let block_node = &mut self.blocks[inst_node.block.unwrap()];
        let prev_inst = inst_node.prev;
        let next_inst = inst_node.next;
        match (prev_inst, next_inst) {
            (Some(prev), Some(next)) => {
                self.insts[prev].next = Some(next);
                self.insts[next].prev = Some(prev);
            }
            (Some(prev), None) => {
                self.insts[prev].next = None;
                block_node.last_inst = Some(prev);
            }
            (None, Some(next)) => {
                self.insts[next].prev = None;
                block_node.first_inst = Some(next);
            }
            (None, None) => {
                block_node.first_inst = None;
                block_node.last_inst = None;
            }
        }

        self.insts[inst] = InstNode::default();
    }
}

struct BlockIter<'a> {
    next: Option<BlockId>,
    blocks: &'a SecondaryMap<BlockId, BlockNode>,
}

impl Iterator for BlockIter<'_> {
    type Item = BlockId;

    fn next(&mut self) -> Option<BlockId> {
        let next = self.next?;
        self.next = self.blocks[next].next;
        Some(next)
    }
}

struct InstIter<'a> {
    next: Option<InstId>,
    insts: &'a SecondaryMap<InstId, InstNode>,
}

impl Iterator for InstIter<'_> {
    type Item = InstId;

    fn next(&mut self) -> Option<InstId> {
        let next = self.next?;
        self.next = self.insts[next].next;
        Some(next)
    }
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
struct BlockNode {
    prev: Option<BlockId>,
    next: Option<BlockId>,
    first_inst: Option<InstId>,
    last_inst: Option<InstId>,
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
struct InstNode {
    /// An block in which the inst exists.
    block: Option<BlockId>,
    /// A previous instruction.
    prev: Option<InstId>,
    /// A next instruction.
    next: Option<InstId>,
}

impl InstNode {
    fn with_block(block: BlockId) -> Self {
        Self {
            block: Some(block),
            prev: None,
            next: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{super::dfg::DataFlowGraph, *};
    use crate::{
        HasInst,
        builder::test_util::test_isa,
        inst::{self, InstId, arith::Add},
        isa::Isa,
        module::ModuleCtx,
    };

    impl DataFlowGraph {
        /// Returns dummy instruction.
        fn make_dummy_inst(&mut self, is: &impl HasInst<Add>) -> InstId {
            let v0 = self.make_imm_value(1i32);
            let v1 = self.make_imm_value(2i32);
            let add = inst::arith::Add::new(is, v0, v1);
            self.make_inst(add)
        }
    }

    #[test]
    fn test_block_insertion() {
        let mut layout = Layout::new();
        let ctx = ModuleCtx::new(&test_isa());
        let mut dfg = DataFlowGraph::new(ctx);
        assert_eq!(layout.entry_block, None);
        assert_eq!(layout.last_block, None);

        // block1.
        let b1 = dfg.make_block();
        layout.append_block(b1);
        assert_eq!(layout.entry_block, Some(b1));
        assert_eq!(layout.last_block, Some(b1));
        assert_eq!(layout.prev_block_of(b1), None);
        assert_eq!(layout.next_block_of(b1), None);

        // block1 -> block2.
        let b2 = dfg.make_block();
        layout.append_block(b2);
        assert_eq!(layout.entry_block, Some(b1));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b1), None);
        assert_eq!(layout.next_block_of(b1), Some(b2));
        assert_eq!(layout.prev_block_of(b2), Some(b1));
        assert_eq!(layout.next_block_of(b2), None);

        // block1 -> block3 -> block2.
        let b3 = dfg.make_block();
        layout.insert_block_after(b3, b1);
        assert_eq!(layout.entry_block, Some(b1));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b2), Some(b3));
        assert_eq!(layout.next_block_of(b1), Some(b3));
        assert_eq!(layout.prev_block_of(b3), Some(b1));
        assert_eq!(layout.next_block_of(b3), Some(b2));

        // block1 -> block3 -> block4 -> block2.
        let b4 = dfg.make_block();
        layout.insert_block_before(b4, b2);
        assert_eq!(layout.entry_block, Some(b1));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b2), Some(b4));
        assert_eq!(layout.next_block_of(b3), Some(b4));
        assert_eq!(layout.prev_block_of(b4), Some(b3));
        assert_eq!(layout.next_block_of(b4), Some(b2));
    }

    #[test]
    fn test_block_removal() {
        let mut layout = Layout::new();
        let ctx = ModuleCtx::new(&test_isa());
        let mut dfg = DataFlowGraph::new(ctx);

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
        assert_eq!(layout.entry_block, Some(b1));
        assert_eq!(layout.last_block, Some(b4));
        assert_eq!(layout.prev_block_of(b4), Some(b2));
        assert_eq!(layout.next_block_of(b2), Some(b4));

        // block1 -> block2.
        layout.remove_block(b4);
        assert_eq!(layout.entry_block, Some(b1));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b2), Some(b1));
        assert_eq!(layout.next_block_of(b2), None);

        // block2.
        layout.remove_block(b1);
        assert_eq!(layout.entry_block, Some(b2));
        assert_eq!(layout.last_block, Some(b2));
        assert_eq!(layout.prev_block_of(b2), None);
        assert_eq!(layout.next_block_of(b2), None);

        // .
        layout.remove_block(b2);
        assert_eq!(layout.entry_block, None);
        assert_eq!(layout.last_block, None);
    }

    #[test]
    fn test_inst_insertion() {
        let mut layout = Layout::new();
        let test_isa = test_isa();
        let is = test_isa.inst_set();
        let ctx = ModuleCtx::new(&test_isa);
        let mut dfg = DataFlowGraph::new(ctx);
        let b1 = dfg.make_block();
        layout.append_block(b1);
        assert_eq!(layout.first_inst_of(b1), None);
        assert_eq!(layout.last_inst_of(b1), None);

        // inst1.
        let i1 = dfg.make_dummy_inst(is);
        layout.append_inst(i1, b1);
        assert_eq!(layout.first_inst_of(b1), Some(i1));
        assert_eq!(layout.last_inst_of(b1), Some(i1));
        assert_eq!(layout.inst_block(i1), b1);
        assert_eq!(layout.prev_inst_of(i1), None);
        assert_eq!(layout.next_inst_of(i1), None);

        // inst1 -> inst2.
        let i2 = dfg.make_dummy_inst(is);
        layout.append_inst(i2, b1);
        assert_eq!(layout.first_inst_of(b1), Some(i1));
        assert_eq!(layout.last_inst_of(b1), Some(i2));
        assert_eq!(layout.prev_inst_of(i2), Some(i1));
        assert_eq!(layout.next_inst_of(i1), Some(i2));

        // inst1 -> inst3 -> inst2.
        let i3 = dfg.make_dummy_inst(is);
        layout.insert_inst_after(i3, i1);
        assert_eq!(layout.first_inst_of(b1), Some(i1));
        assert_eq!(layout.last_inst_of(b1), Some(i2));
        assert_eq!(layout.next_inst_of(i1), Some(i3));
        assert_eq!(layout.prev_inst_of(i2), Some(i3));
        assert_eq!(layout.prev_inst_of(i3), Some(i1));
        assert_eq!(layout.next_inst_of(i3), Some(i2));

        // inst1 -> inst3 -> inst4 -> inst2.
        let i4 = dfg.make_dummy_inst(is);
        layout.insert_inst_before(i4, i2);
        assert_eq!(layout.first_inst_of(b1), Some(i1));
        assert_eq!(layout.last_inst_of(b1), Some(i2));
        assert_eq!(layout.next_inst_of(i3), Some(i4));
        assert_eq!(layout.prev_inst_of(i2), Some(i4));
        assert_eq!(layout.prev_inst_of(i4), Some(i3));
        assert_eq!(layout.next_inst_of(i4), Some(i2));
    }

    #[test]
    fn test_inst_removal() {
        let mut layout = Layout::new();
        let test_isa = test_isa();
        let is = test_isa.inst_set();
        let ctx = ModuleCtx::new(&test_isa);
        let mut dfg = DataFlowGraph::new(ctx);
        let b1 = dfg.make_block();
        layout.append_block(b1);

        // inst1 -> inst2 -> inst3 -> inst4.
        let i1 = dfg.make_dummy_inst(is);
        let i2 = dfg.make_dummy_inst(is);
        let i3 = dfg.make_dummy_inst(is);
        let i4 = dfg.make_dummy_inst(is);
        layout.append_inst(i1, b1);
        layout.append_inst(i2, b1);
        layout.append_inst(i3, b1);
        layout.append_inst(i4, b1);

        // inst1 -> inst2 -> inst4.
        layout.remove_inst(i3);
        assert_eq!(layout.first_inst_of(b1), Some(i1));
        assert_eq!(layout.last_inst_of(b1), Some(i4));
        assert_eq!(layout.next_inst_of(i2), Some(i4));
        assert_eq!(layout.prev_inst_of(i4), Some(i2));

        // inst1 -> inst2.
        layout.remove_inst(i4);
        assert_eq!(layout.first_inst_of(b1), Some(i1));
        assert_eq!(layout.last_inst_of(b1), Some(i2));
        assert_eq!(layout.next_inst_of(i1), Some(i2));
        assert_eq!(layout.prev_inst_of(i2), Some(i1));

        // inst2.
        layout.remove_inst(i1);
        assert_eq!(layout.first_inst_of(b1), Some(i2));
        assert_eq!(layout.last_inst_of(b1), Some(i2));
        assert_eq!(layout.next_inst_of(i2), None);
        assert_eq!(layout.prev_inst_of(i2), None);

        // .
        layout.remove_inst(i2);
        assert_eq!(layout.first_inst_of(b1), None);
        assert_eq!(layout.last_inst_of(b1), None);
    }
}
