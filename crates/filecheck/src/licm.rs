use std::path::{Path, PathBuf};

use sonatina_codegen::{
    cfg_edit::CleanupMode,
    domtree::DomTree,
    loop_analysis::LoopTree,
    optim::{cfg_cleanup::CfgCleanup, licm::LicmSolver},
};
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct LicmTransformer {
    cfg: ControlFlowGraph,
    domtree: DomTree,
    lpt: LoopTree,
}

impl FuncTransform for LicmTransformer {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.domtree.compute(&self.cfg);
        self.lpt.compute(&self.cfg, &self.domtree);
        let mut solver = LicmSolver::new();
        solver.run(func, &mut self.cfg, &mut self.lpt);
        CfgCleanup::new(CleanupMode::Strict).run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("licm")
    }
}
