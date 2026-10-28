use std::path::{Path, PathBuf};

use sonatina_codegen::{domtree::DomTree, optim::compare_sub_fusion::CompareSubFusion};
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct CompareSubFusionTransform {
    cfg: ControlFlowGraph,
    domtree: DomTree,
}

impl FuncTransform for CompareSubFusionTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.domtree.compute(&self.cfg);
        CompareSubFusion::new().run(func, &self.domtree);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("compare_sub_fusion")
    }
}
