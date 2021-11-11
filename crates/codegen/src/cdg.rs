//! This module contains `ControlDependenceGragh (CDG)`.

use super::{
    cfg::ControlFlowGraph,
    domtree::{DFSet, DomTree},
    Block, Function,
};

#[derive(Debug)]
pub struct ControlDependenceGragh {
    /// Dummy entry block to calculate CDG.
    entry: Block,
    /// Canonical dummy exit block to calculate CDG. All blocks ends with `return` has an edge to
    /// this block.
    exit: Block,

    /// Reverse control flow graph of the function.
    rcfg: ControlFlowGraph,

    /// Dominator tree of reverse control flow graph.
    domtree: DomTree,
    /// Dominance frontier set of reverse control flow graph.
    df: DFSet,
}

impl Default for ControlDependenceGragh {
    fn default() -> Self {
        Self {
            entry: Block(0),
            exit: Block(0),
            rcfg: ControlFlowGraph::default(),
            domtree: DomTree::default(),
            df: DFSet::default(),
        }
    }
}

impl ControlDependenceGragh {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn compute(&mut self, func: &Function) {
        self.clear();

        self.rcfg.compute(func);
        if self.rcfg.entry().is_none() {
            return;
        }
        let real_entry = self.rcfg.entry().unwrap();

        self.entry = Block(func.dfg.blocks.len() as u32);
        self.exit = Block(self.entry.0 + 1);

        // Add edges from dummy entry block to real entry block and dummy exit block.
        self.rcfg.add_edge(self.entry, real_entry);
        self.rcfg.add_edge(self.entry, self.exit);

        // Add edges from real exit blocks to dummy exit block.
        let real_exits = std::mem::take(&mut self.rcfg.exits);
        for exit in &real_exits {
            self.rcfg.add_edge(*exit, self.exit);
        }

        self.rcfg.reverse_edges(self.exit, &[self.entry]);

        self.domtree.compute(&self.rcfg);
        self.df = self.domtree.compute_df(&self.rcfg);
    }

    pub fn clear(&mut self) {
        self.rcfg.clear();
        self.domtree.clear();
        self.df.clear();
    }

    /// Returns all blocks that `block` depends upon.
    pub fn incoming_blocks_of(&self, block: Block) -> impl Iterator<Item = &Block> {
        self.df
            .frontier(block)
            .filter(|block| **block != self.entry && **block != self.exit)
    }

    /// Returns `true` if `dependent` depends on `on`.
    pub fn does_depend_on(&self, dependent: Block, on: Block) -> bool {
        self.df.in_frontier_of(on, dependent)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::test_util::func_builder;

    fn test_incomings(cdg: &ControlDependenceGragh, dependent: Block, incomings: &[Block]) -> bool {
        if cdg.incoming_blocks_of(dependent).count() != incomings.len() {
            return false;
        }

        for incoming in incomings {
            if !cdg.does_depend_on(dependent, *incoming) {
                return false;
            }
        }

        true
    }

    #[test]
    fn cdg_if_else() {
        let mut builder = func_builder(vec![super::super::Type::I64], vec![]);

        let entry_block = builder.append_block();
        let then_block = builder.append_block();
        let else_block = builder.append_block();
        let merge_block = builder.append_block();

        let arg0 = builder.args()[0];

        builder.switch_to_block(entry_block);
        builder.br(arg0, then_block, else_block);

        builder.switch_to_block(then_block);
        let v1 = builder.imm_i64(1);
        builder.jump(merge_block);

        builder.switch_to_block(else_block);
        let v2 = builder.imm_i64(2);
        builder.jump(merge_block);

        builder.switch_to_block(merge_block);
        let v3 = builder.phi(&[(v1, then_block), (v2, else_block)]);
        builder.add(v3, arg0);
        builder.ret(&[]);

        builder.seal_all();
        let func = builder.build();
        let mut cdg = ControlDependenceGragh::new();
        cdg.compute(&func);

        assert!(test_incomings(&cdg, entry_block, &[]));
        assert!(test_incomings(&cdg, then_block, &[entry_block]));
        assert!(test_incomings(&cdg, else_block, &[entry_block]));
        assert!(test_incomings(&cdg, merge_block, &[]));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn cdg_complex() {
        let mut builder = func_builder(vec![], vec![]);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let e = builder.append_block();
        let f = builder.append_block();
        let g = builder.append_block();
        let h = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.imm_u8(1);
        builder.br(v0, b, c);

        builder.switch_to_block(b);
        builder.jump(g);

        builder.switch_to_block(c);
        builder.br(v0, d, e);

        builder.switch_to_block(d);
        builder.jump(f);

        builder.switch_to_block(e);
        builder.jump(f);

        builder.switch_to_block(f);
        builder.jump(g);

        builder.switch_to_block(g);
        builder.br(v0, a, h);

        builder.switch_to_block(h);
        builder.ret(&[]);

        builder.seal_all();

        let func = builder.build();
        let mut cdg = ControlDependenceGragh::new();
        cdg.compute(&func);

        assert!(test_incomings(&cdg, a, &[g]));
        assert!(test_incomings(&cdg, b, &[a]));
        assert!(test_incomings(&cdg, c, &[a]));
        assert!(test_incomings(&cdg, d, &[c]));
        assert!(test_incomings(&cdg, e, &[c]));
        assert!(test_incomings(&cdg, f, &[a]));
        assert!(test_incomings(&cdg, g, &[g]));
        assert!(test_incomings(&cdg, h, &[]));
    }
}
