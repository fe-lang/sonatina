use std::path::{Path, PathBuf};

use sonatina_codegen::{
    cfg_edit::CleanupMode,
    optim::{cfg_cleanup::CfgCleanup, sccp::SccpSolver},
};

use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct SccpTransform {
    cfg: ControlFlowGraph,
}

impl FuncTransform for SccpTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        let mut solver = SccpSolver::new();
        solver.run(func, &mut self.cfg);
        CfgCleanup::new(CleanupMode::Strict).run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("sccp")
    }
}
