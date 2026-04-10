use std::path::{Path, PathBuf};

use sonatina_codegen::{
    cfg_edit::CleanupMode,
    domtree::DomTree,
    optim::{cfg_cleanup::CfgCleanup, gvn::GvnSolver},
};
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct GvnTransform {
    domtree: DomTree,
    cfg: ControlFlowGraph,
}

impl FuncTransform for GvnTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.domtree.compute(&self.cfg);
        let mut solver = GvnSolver::new();
        solver.run(func, &mut self.cfg, &mut self.domtree);
        CfgCleanup::new(CleanupMode::Strict).run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("gvn")
    }
}
