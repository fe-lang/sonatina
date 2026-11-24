use std::path::{Path, PathBuf};

use sonatina_codegen::{
    domtree::DomTree,
    loop_analysis::LoopTree,
    optim::{
        cfg_cleanup::CfgCleanup, merge_index_checks::MergeIndexChecks,
        range_branch_simplify::RangeBranchSimplify,
    },
};
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct MergeIndexChecksTransform {
    cfg: ControlFlowGraph,
    domtree: DomTree,
    lpt: LoopTree,
}

impl FuncTransform for MergeIndexChecksTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        MergeIndexChecks.run(func, &self.cfg);
        self.domtree.compute(&self.cfg);
        self.lpt.compute(&self.cfg, &self.domtree);
        RangeBranchSimplify::new().run(func, &self.cfg, &self.domtree, &self.lpt);
        CfgCleanup::new().run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("merge_index_checks")
    }
}
