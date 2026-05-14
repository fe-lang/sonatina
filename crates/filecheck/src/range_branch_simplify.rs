use std::path::{Path, PathBuf};

use sonatina_codegen::{
    domtree::DomTree, loop_analysis::LoopTree, optim::range_branch_simplify::RangeBranchSimplify,
};
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct RangeBranchSimplifyTransform {
    cfg: ControlFlowGraph,
    domtree: DomTree,
    lpt: LoopTree,
}

impl FuncTransform for RangeBranchSimplifyTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.domtree.compute(&self.cfg);
        self.lpt.compute(&self.cfg, &self.domtree);
        RangeBranchSimplify::new().run(func, &self.cfg, &self.lpt);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("range_branch_simplify")
    }
}
