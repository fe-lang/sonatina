use cranelift_entity::{entity_impl, packed_option::PackedOption, PrimaryMap, SecondaryMap};
use fxhash::FxHashMap;
use smallvec::SmallVec;

use crate::{cfg::ControlFlowGraph, domtree::DomTree, ir::Block};

#[derive(Debug, Default)]
pub struct LoopTree {
    /// Stores loops.
    /// The index of an outer loops is guaranteed to be lower than its inner loops because loops
    /// are found in RPO.
    loops: PrimaryMap<Loop, LoopData>,

    /// Maps blocks to its contained loop.
    /// If the block is contained by multiple nested loops, then the block is mapped to the innermost loop.
    block_to_loop: SecondaryMap<Block, PackedOption<Loop>>,
}

impl LoopTree {
    pub fn new() -> Self {
        Self::default()
    }

    /// Compute the `LoopTree` of the block.
    pub fn compute(&mut self, cfg: &ControlFlowGraph, domtree: &DomTree) {
        self.clear();

        // Find loop headers in RPO, this means outer loops are guaranteed to be inserted first,
        // then its inner loops are inserted.
        for &block in domtree.rpo() {
            for &pred in cfg.preds_of(block) {
                if domtree.dominates(block, pred) {
                    let loop_data = LoopData {
                        header: block,
                        parent: None.into(),
                        children: SmallVec::new(),
                    };

                    self.loops.push(loop_data);
                    break;
                }
            }
        }

        self.analyze_loops(cfg, domtree);
    }

    /// Returns all loops.
    /// The result iterator guarantees outer loops are returned before its inner loops.
    pub fn loops(&self) -> impl DoubleEndedIterator<Item = Loop> {
        self.loops.keys()
    }

    /// Returns all blocks in the loop.
    pub fn iter_blocks_post_order<'a, 'b>(
        &'a self,
        cfg: &'b ControlFlowGraph,
        lp: Loop,
    ) -> BlocksInLoopPostOrder<'a, 'b> {
        BlocksInLoopPostOrder::new(self, cfg, lp)
    }

    /// Returns `true` if the `block` is in the `lp`.
    pub fn is_in_loop(&self, block: Block, lp: Loop) -> bool {
        let mut loop_of_block = self.loop_of_block(block);
        while let Some(cur_lp) = loop_of_block {
            if lp == cur_lp {
                return true;
            }
            loop_of_block = self.parent_loop(cur_lp);
        }
        false
    }

    /// Returns number of loops found.
    pub fn loop_num(&self) -> usize {
        self.loops.len()
    }

    /// Map `block` to `lp`.
    pub fn map_block(&mut self, block: Block, lp: Loop) {
        self.block_to_loop[block] = lp.into();
    }

    /// Clear the internal state of `LoopTree`.
    pub fn clear(&mut self) {
        self.loops.clear();
        self.block_to_loop.clear();
    }

    /// Returns header block of the `lp`.
    pub fn loop_header(&self, lp: Loop) -> Block {
        self.loops[lp].header
    }

    /// Get parent loop of the `lp` if exists.
    pub fn parent_loop(&self, lp: Loop) -> Option<Loop> {
        self.loops[lp].parent.expand()
    }

    /// Returns the loop that the `block` belongs to.
    /// If the `block` belongs to multiple loops, then returns the innermost loop.
    pub fn loop_of_block(&self, block: Block) -> Option<Loop> {
        self.block_to_loop[block].expand()
    }

    /// Analyze loops. This method does
    /// 1. Mapping each blocks to its contained loop.
    /// 2. Setting parent and child of the loops.
    fn analyze_loops(&mut self, cfg: &ControlFlowGraph, domtree: &DomTree) {
        let mut worklist = vec![];

        // Iterate loops reversely to ensure analyze inner loops first.
        for cur_lp in self.loops.keys().rev() {
            let cur_lp_header = self.loop_header(cur_lp);

            // Add predecessors of the loop header to worklist.
            for &block in cfg.preds_of(cur_lp_header) {
                if domtree.dominates(cur_lp_header, block) {
                    worklist.push(block);
                }
            }

            while let Some(block) = worklist.pop() {
                match self.block_to_loop[block].expand() {
                    Some(lp_of_block) => {
                        let outermost_parent = self.outermost_parent(lp_of_block);

                        // If outermost parent is current loop, then the block is already visited.
                        if outermost_parent == cur_lp {
                            continue;
                        } else {
                            self.loops[cur_lp].children.push(outermost_parent);
                            self.loops[outermost_parent].parent = cur_lp.into();

                            let lp_header_of_block = self.loop_header(lp_of_block);
                            worklist.extend(cfg.preds_of(lp_header_of_block));
                        }
                    }

                    // If the block is not mapped to any loops, then map it to the loop.
                    None => {
                        self.map_block(block, cur_lp);
                        // If block is not loop header, then add its predecessors to the worklist.
                        if block != cur_lp_header {
                            worklist.extend(cfg.preds_of(block));
                        }
                    }
                }
            }
        }
    }

    /// Returns the outermost parent loop of `lp`. If `lp` doesn't have any parent, then returns `lp`
    /// itself.
    fn outermost_parent(&self, mut lp: Loop) -> Loop {
        while let Some(parent) = self.parent_loop(lp) {
            lp = parent;
        }
        lp
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loop(u32);
entity_impl!(Loop);

#[derive(Debug, Clone, PartialEq, Eq)]
struct LoopData {
    /// A header of the loop.
    header: Block,

    /// A parent loop that includes the loop.
    parent: PackedOption<Loop>,

    /// Child loops that the loop includes.
    children: SmallVec<[Loop; 4]>,
}

pub struct BlocksInLoopPostOrder<'a, 'b> {
    lpt: &'a LoopTree,
    cfg: &'b ControlFlowGraph,
    lp: Loop,
    stack: Vec<Block>,
    block_state: FxHashMap<Block, BlockState>,
}

impl<'a, 'b> BlocksInLoopPostOrder<'a, 'b> {
    fn new(lpt: &'a LoopTree, cfg: &'b ControlFlowGraph, lp: Loop) -> Self {
        let loop_header = lpt.loop_header(lp);

        Self {
            lpt,
            cfg,
            lp,
            stack: vec![loop_header],
            block_state: FxHashMap::default(),
        }
    }
}

impl<'a, 'b> Iterator for BlocksInLoopPostOrder<'a, 'b> {
    type Item = Block;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(&block) = self.stack.last() {
            match self.block_state.get(&block) {
                // The block is already visited, but not returned from the iterator,
                // so mark the block as `Finished` and return the block.
                Some(BlockState::Visited) => {
                    let block = self.stack.pop().unwrap();
                    self.block_state.insert(block, BlockState::Finished);
                    return Some(block);
                }

                // The block is already returned, so just remove the block from the stack.
                Some(BlockState::Finished) => {
                    self.stack.pop().unwrap();
                }

                // The block is not visited yet, so push its unvisited in-loop successors to the stack and mark the block as `Visited`.
                None => {
                    self.block_state.insert(block, BlockState::Visited);
                    for &succ in self.cfg.succs_of(block) {
                        if self.block_state.get(&succ).is_none()
                            && self.lpt.is_in_loop(succ, self.lp)
                        {
                            self.stack.push(succ);
                        }
                    }
                }
            }
        }

        None
    }
}

enum BlockState {
    Visited,
    Finished,
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        ir::builder::test_util::{build_test_isa, func_builder},
        Function, Type,
    };

    fn compute_loop(func: &Function) -> LoopTree {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        let mut lpt = LoopTree::new();
        cfg.compute(func);
        domtree.compute(&cfg);
        lpt.compute(&cfg, &domtree);
        lpt
    }

    #[test]
    fn simple_loop() {
        let isa = build_test_isa();
        let mut builder = func_builder(&[], None, &isa);
        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();

        builder.switch_to_block(b0);
        let v0 = builder.make_imm_value(0i32);
        builder.jump(b1);

        builder.switch_to_block(b1);
        let v1 = builder.phi(&[(v0, b0)]);
        let c0 = builder.make_imm_value(10i32);
        let v2 = builder.eq(v1, c0);
        builder.br(v2, b3, b2);

        builder.switch_to_block(b2);
        let c1 = builder.make_imm_value(1i32);
        let v3 = builder.add(v1, c1);
        builder.jump(b1);
        builder.append_phi_arg(v1, v3, b2);

        builder.switch_to_block(b3);
        builder.ret(None);

        builder.seal_all();

        let func = builder.build();
        let lpt = compute_loop(&func);

        debug_assert_eq!(lpt.loop_num(), 1);
        let lp0 = lpt.loops().next().unwrap();
        debug_assert_eq!(lpt.loop_of_block(b0), None);
        debug_assert_eq!(lpt.loop_of_block(b1), Some(lp0));
        debug_assert_eq!(lpt.loop_of_block(b2), Some(lp0));
        debug_assert_eq!(lpt.loop_of_block(b3), None);

        debug_assert_eq!(lpt.loop_header(lp0), b1);
    }

    #[test]
    fn continue_loop() {
        let isa = build_test_isa();
        let mut builder = func_builder(&[], None, &isa);
        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();
        let b5 = builder.append_block();
        let b6 = builder.append_block();

        builder.switch_to_block(b0);
        let v0 = builder.make_imm_value(0i32);
        builder.jump(b1);

        builder.switch_to_block(b1);
        let v1 = builder.phi(&[(v0, b0)]);
        let c0 = builder.make_imm_value(10i32);
        let v2 = builder.eq(v1, c0);
        builder.br(v2, b5, b2);

        builder.switch_to_block(b2);
        let c1 = builder.make_imm_value(5i32);
        let v3 = builder.eq(v1, c1);
        builder.br(v3, b3, b4);

        builder.switch_to_block(b3);
        builder.jump(b5);

        builder.switch_to_block(b4);
        let c2 = builder.make_imm_value(3i32);
        let v4 = builder.add(v1, c2);
        builder.append_phi_arg(v1, v4, b4);
        builder.jump(b1);

        builder.switch_to_block(b5);
        let c3 = builder.make_imm_value(1i32);
        let v5 = builder.add(v1, c3);
        builder.append_phi_arg(v1, v5, b5);
        builder.jump(b1);

        builder.switch_to_block(b6);
        builder.ret(None);

        builder.seal_all();

        let func = builder.build();
        let lpt = compute_loop(&func);

        debug_assert_eq!(lpt.loop_num(), 1);
        let lp0 = lpt.loops().next().unwrap();

        debug_assert_eq!(lpt.loop_of_block(b0), None);
        debug_assert_eq!(lpt.loop_of_block(b1), Some(lp0));
        debug_assert_eq!(lpt.loop_of_block(b2), Some(lp0));
        debug_assert_eq!(lpt.loop_of_block(b3), Some(lp0));
        debug_assert_eq!(lpt.loop_of_block(b4), Some(lp0));
        debug_assert_eq!(lpt.loop_of_block(b5), Some(lp0));
        debug_assert_eq!(lpt.loop_of_block(b6), None);

        debug_assert_eq!(lpt.loop_header(lp0), b1);
    }

    #[test]
    fn single_block_loop() {
        let isa = build_test_isa();
        let mut builder = func_builder(&[Type::I1], None, &isa);
        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        let arg = builder.args()[0];

        builder.switch_to_block(b0);
        builder.jump(b1);

        builder.switch_to_block(b1);
        builder.br(arg, b1, b2);

        builder.switch_to_block(b2);
        builder.ret(None);

        builder.seal_all();
        let func = builder.build();
        let lpt = compute_loop(&func);

        debug_assert_eq!(lpt.loop_num(), 1);
        let lp0 = lpt.loops().next().unwrap();

        debug_assert_eq!(lpt.loop_of_block(b0), None);
        debug_assert_eq!(lpt.loop_of_block(b1), Some(lp0));
        debug_assert_eq!(lpt.loop_of_block(b2), None);
    }

    #[test]
    fn nested_loop() {
        let isa = build_test_isa();
        let mut builder = func_builder(&[Type::I1], None, &isa);
        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();
        let b5 = builder.append_block();
        let b6 = builder.append_block();
        let b7 = builder.append_block();
        let b8 = builder.append_block();
        let b9 = builder.append_block();
        let b10 = builder.append_block();
        let b11 = builder.append_block();

        let arg = builder.args()[0];

        builder.switch_to_block(b0);
        builder.jump(b1);

        builder.switch_to_block(b1);
        builder.jump(b2);

        builder.switch_to_block(b2);
        builder.br(arg, b3, b7);

        builder.switch_to_block(b3);
        builder.jump(b4);

        builder.switch_to_block(b4);
        builder.jump(b5);

        builder.switch_to_block(b5);
        builder.br(arg, b4, b6);

        builder.switch_to_block(b6);
        builder.br(arg, b3, b10);

        builder.switch_to_block(b7);
        builder.jump(b8);

        builder.switch_to_block(b8);
        builder.br(arg, b9, b7);

        builder.switch_to_block(b9);
        builder.br(arg, b1, b10);

        builder.switch_to_block(b10);
        builder.jump(b1);

        builder.switch_to_block(b11);
        builder.ret(None);

        builder.seal_all();

        let func = builder.build();
        let lpt = compute_loop(&func);

        debug_assert_eq!(lpt.loop_num(), 4);
        let l0 = lpt.loop_of_block(b1).unwrap();
        let l1 = lpt.loop_of_block(b3).unwrap();
        let l2 = lpt.loop_of_block(b4).unwrap();
        let l3 = lpt.loop_of_block(b7).unwrap();

        debug_assert_eq!(lpt.loop_of_block(b0), None);
        debug_assert_eq!(lpt.loop_of_block(b1), Some(l0));
        debug_assert_eq!(lpt.loop_of_block(b2), Some(l0));
        debug_assert_eq!(lpt.loop_of_block(b3), Some(l1));
        debug_assert_eq!(lpt.loop_of_block(b4), Some(l2));
        debug_assert_eq!(lpt.loop_of_block(b5), Some(l2));
        debug_assert_eq!(lpt.loop_of_block(b6), Some(l1));
        debug_assert_eq!(lpt.loop_of_block(b7), Some(l3));
        debug_assert_eq!(lpt.loop_of_block(b8), Some(l3));
        debug_assert_eq!(lpt.loop_of_block(b9), Some(l0));
        debug_assert_eq!(lpt.loop_of_block(b10), Some(l0));
        debug_assert_eq!(lpt.loop_of_block(b11), None);

        debug_assert_eq!(lpt.parent_loop(l0), None);
        debug_assert_eq!(lpt.parent_loop(l1), Some(l0));
        debug_assert_eq!(lpt.parent_loop(l2), Some(l1));
        debug_assert_eq!(lpt.parent_loop(l3), Some(l0));

        debug_assert_eq!(lpt.loop_header(l0), b1);
        debug_assert_eq!(lpt.loop_header(l1), b3);
        debug_assert_eq!(lpt.loop_header(l2), b4);
        debug_assert_eq!(lpt.loop_header(l3), b7);
    }
}
