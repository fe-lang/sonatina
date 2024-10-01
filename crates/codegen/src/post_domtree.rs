//! This module contains implementation of `Post Dominator Tree`.

use sonatina_ir::{BlockId, ControlFlowGraph, Function};

use super::domtree::{DFSet, DomTree};

#[derive(Debug)]
pub struct PostDomTree {
    /// Dummy entry block to calculate CDG.
    entry: BlockId,
    /// Canonical dummy exit block to calculate CDG. All blocks ends with
    /// `return` has an edge to this block.
    exit: BlockId,

    /// Reverse control flow graph of the function.
    rcfg: ControlFlowGraph,

    /// Dominator tree of reverse control flow graph.
    domtree: DomTree,
}

impl Default for PostDomTree {
    fn default() -> Self {
        Self {
            entry: BlockId(0),
            exit: BlockId(0),
            rcfg: ControlFlowGraph::default(),
            domtree: DomTree::default(),
        }
    }
}

impl PostDomTree {
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

        self.entry = BlockId(func.dfg.blocks.len() as u32);
        self.exit = BlockId(self.entry.0 + 1);

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
    }

    pub fn idom_of(&self, block: BlockId) -> Option<PDTIdom> {
        match self.domtree.idom_of(block)? {
            block if block == self.entry => Some(PDTIdom::DummyEntry(self.entry)),
            block if block == self.exit => Some(PDTIdom::DummyExit(self.exit)),
            other => Some(PDTIdom::Real(other)),
        }
    }

    pub fn clear(&mut self) {
        self.rcfg.clear();
        self.domtree.clear();
    }

    /// Compute post dominance frontiers of each blocks.
    pub fn compute_df(&self) -> PDFSet {
        let df_set = self.domtree.compute_df(&self.rcfg);

        PDFSet {
            entry: self.entry,
            exit: self.exit,
            df_set,
        }
    }

    /// Returns `true` if block is reachable from the exit blocks.
    pub fn is_reachable(&self, block: BlockId) -> bool {
        self.domtree.is_reachable(block)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum PDTIdom {
    DummyEntry(BlockId),
    DummyExit(BlockId),
    Real(BlockId),
}

/// Post Dominance frontiers of each blocks.
#[derive(Debug)]
pub struct PDFSet {
    /// Dummy entry block of the post dominator tree.
    entry: BlockId,

    /// Canonical dummy exit block of the post dominator tree.
    exit: BlockId,

    df_set: DFSet,
}

impl PDFSet {
    pub fn frontiers(&self, block: BlockId) -> impl Iterator<Item = &BlockId> {
        self.df_set
            .frontiers(block)
            .filter(|block| **block != self.entry && **block != self.exit)
    }

    pub fn in_frontier_of(&self, block: BlockId, of: BlockId) -> bool {
        self.df_set.in_frontier_of(block, of)
    }

    pub fn frontier_num_of(&self, of: BlockId) -> usize {
        self.frontiers(of).count()
    }

    pub fn clear(&mut self) {
        self.df_set.clear();
    }
}

impl Default for PDFSet {
    fn default() -> Self {
        Self {
            entry: BlockId(0),
            exit: BlockId(0),
            df_set: DFSet::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::many_single_char_names)]

    use sonatina_ir::{
        builder::test_util::*,
        inst::{
            arith::Add,
            control_flow::{Br, Jump, Phi, Return},
        },
        prelude::*,
        Type,
    };

    use super::*;

    fn calc_dom(func: &Function) -> (PostDomTree, PDFSet) {
        let mut post_dom_tree = PostDomTree::new();
        post_dom_tree.compute(func);
        let pdf = post_dom_tree.compute_df();
        (post_dom_tree, pdf)
    }

    fn test_pdf(pdf: &PDFSet, of: BlockId, frontieres: &[BlockId]) -> bool {
        if pdf.frontier_num_of(of) != frontieres.len() {
            return false;
        }

        for &block in frontieres {
            if !pdf.in_frontier_of(block, of) {
                return false;
            }
        }

        true
    }

    #[test]
    fn pd_if_else() {
        let (evm, mut builder) = test_func_builder(&[Type::I32], Type::Void);
        let is = evm.inst_set();

        let entry_block = builder.append_block();
        let then_block = builder.append_block();
        let else_block = builder.append_block();
        let merge_block = builder.append_block();

        let arg0 = builder.args()[0];

        builder.switch_to_block(entry_block);
        builder.insert_inst_no_result_with(|| Br::new(is, arg0, then_block, else_block));

        builder.switch_to_block(then_block);
        let v1 = builder.make_imm_value(1i64);
        builder.insert_inst_no_result_with(|| Jump::new(is, merge_block));

        builder.switch_to_block(else_block);
        let v2 = builder.make_imm_value(2i64);
        builder.insert_inst_no_result_with(|| Jump::new(is, merge_block));

        builder.switch_to_block(merge_block);
        let v3 = builder.insert_inst_with(
            || Phi::new(is, vec![(v1, then_block), (v2, else_block)], Type::I64),
            Type::I64,
        );
        builder.insert_inst_with(|| Add::new(is, v3, arg0), Type::I64);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();

        let module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &module.funcs[func_ref];
        let (post_dom_tree, pdf) = calc_dom(func);

        assert!(post_dom_tree.is_reachable(entry_block));
        assert!(post_dom_tree.is_reachable(else_block));
        assert!(post_dom_tree.is_reachable(then_block));
        assert!(post_dom_tree.is_reachable(merge_block));

        assert!(test_pdf(&pdf, entry_block, &[]));
        assert!(test_pdf(&pdf, then_block, &[entry_block]));
        assert!(test_pdf(&pdf, else_block, &[entry_block]));
        assert!(test_pdf(&pdf, merge_block, &[]));
    }

    #[test]
    fn infinite_loop() {
        let (evm, mut builder) = test_func_builder(&[], Type::Void);
        let is = evm.inst_set();

        let a = builder.append_block();
        builder.switch_to_block(a);
        builder.insert_inst_no_result_with(|| Jump::new(is, a));

        builder.seal_all();

        let module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &module.funcs[func_ref];
        let (post_dom_tree, pdf) = calc_dom(func);

        assert!(!post_dom_tree.is_reachable(a));
        assert!(test_pdf(&pdf, a, &[]));
    }

    #[test]
    fn test_multiple_return() {
        let (evm, mut builder) = test_func_builder(&[], Type::Void);
        let is = evm.inst_set();

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let e = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.make_imm_value(1i8);
        builder.insert_inst_no_result_with(|| Br::new(is, v0, b, c));

        builder.switch_to_block(b);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.switch_to_block(c);
        builder.insert_inst_no_result_with(|| Br::new(is, v0, d, e));

        builder.switch_to_block(d);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.switch_to_block(e);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();

        let module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &module.funcs[func_ref];
        let (post_dom_tree, pdf) = calc_dom(func);

        assert!(post_dom_tree.is_reachable(a));
        assert!(post_dom_tree.is_reachable(b));
        assert!(post_dom_tree.is_reachable(c));
        assert!(post_dom_tree.is_reachable(d));
        assert!(post_dom_tree.is_reachable(e));

        assert!(test_pdf(&pdf, a, &[]));
        assert!(test_pdf(&pdf, b, &[a]));
        assert!(test_pdf(&pdf, c, &[a]));
        assert!(test_pdf(&pdf, d, &[c]));
        assert!(test_pdf(&pdf, e, &[c]));
    }

    #[test]
    fn pd_complex() {
        let (evm, mut builder) = test_func_builder(&[], Type::Void);
        let is = evm.inst_set();

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let e = builder.append_block();
        let f = builder.append_block();
        let g = builder.append_block();
        let h = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.make_imm_value(1i8);
        builder.insert_inst_no_result_with(|| Br::new(is, v0, b, c));

        builder.switch_to_block(b);
        builder.insert_inst_no_result_with(|| Jump::new(is, g));

        builder.switch_to_block(c);
        builder.insert_inst_no_result_with(|| Br::new(is, v0, d, e));

        builder.switch_to_block(d);
        builder.insert_inst_no_result_with(|| Jump::new(is, f));

        builder.switch_to_block(e);
        builder.insert_inst_no_result_with(|| Jump::new(is, f));

        builder.switch_to_block(f);
        builder.insert_inst_no_result_with(|| Jump::new(is, g));

        builder.switch_to_block(g);
        builder.insert_inst_no_result_with(|| Br::new(is, v0, a, h));

        builder.switch_to_block(h);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();

        let module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &module.funcs[func_ref];
        let (post_dom_tree, pdf) = calc_dom(func);

        assert!(post_dom_tree.is_reachable(a));
        assert!(post_dom_tree.is_reachable(b));
        assert!(post_dom_tree.is_reachable(c));
        assert!(post_dom_tree.is_reachable(d));
        assert!(post_dom_tree.is_reachable(e));
        assert!(post_dom_tree.is_reachable(f));
        assert!(post_dom_tree.is_reachable(g));
        assert!(post_dom_tree.is_reachable(h));

        assert!(test_pdf(&pdf, a, &[g]));
        assert!(test_pdf(&pdf, b, &[a]));
        assert!(test_pdf(&pdf, c, &[a]));
        assert!(test_pdf(&pdf, d, &[c]));
        assert!(test_pdf(&pdf, e, &[c]));
        assert!(test_pdf(&pdf, f, &[a]));
        assert!(test_pdf(&pdf, g, &[g]));
        assert!(test_pdf(&pdf, h, &[]));
    }
}
