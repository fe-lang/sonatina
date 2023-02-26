use crate::{cfg::ControlFlowGraph, domtree::DomTree, loop_analysis::LoopTree};
use sonatina_ir as ir;

pub struct StackAlloc {
    // Stored here for re-use; see `fn clear`
    cfg: ControlFlowGraph,
    dom_tree: DomTree,
    loop_tree: LoopTree,
}

impl StackAlloc {
    pub fn compute(&mut self, _function: &ir::Function) {
        self.clear();
    }
    pub fn clear(&mut self) {
        self.cfg.clear();
        self.dom_tree.clear();
        self.loop_tree.clear();
    }
}
