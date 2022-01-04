use std::path::{Path, PathBuf};

use sonatina_codegen::{
    cfg::ControlFlowGraph, domtree::DomTree, loop_analysis::LoopTree, optim::licm::LicmSolver,
    Function,
};

use super::{FuncTransform, FIXTURE_ROOT};

#[derive(Default)]
pub struct LicmTransformer {
    solver: LicmSolver,
    cfg: ControlFlowGraph,
    domtree: DomTree,
    lpt: LoopTree,
}

impl FuncTransform for LicmTransformer {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.domtree.compute(&self.cfg);
        self.lpt.compute(&self.cfg, &self.domtree);
        self.solver.run(func, &mut self.cfg, &mut self.lpt);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("licm")
    }
}
