use std::path::{Path, PathBuf};

use sonatina_codegen::{
    domtree::DomTree, loop_analysis::LoopTree, optim::hoist_insert_chains::HoistInsertChains,
};
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct HoistInsertChainsTransform {
    cfg: ControlFlowGraph,
    domtree: DomTree,
    lpt: LoopTree,
}

impl FuncTransform for HoistInsertChainsTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.domtree.compute(&self.cfg);
        self.lpt.compute(&self.cfg, &self.domtree);
        HoistInsertChains.run(func, &self.domtree, &self.lpt);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("hoist_insert_chains")
    }
}
