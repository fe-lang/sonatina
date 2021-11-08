use std::path::{Path, PathBuf};

use sonatina_codegen::{cfg::ControlFlowGraph, optim::sccp::SccpSolver, Function};

use super::{FuncTransform, FIXTURE_ROOT};

#[derive(Default)]
pub struct SccpTransform {
    cfg: ControlFlowGraph,
    solver: SccpSolver,
}

impl FuncTransform for SccpTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.solver.run(func, &mut self.cfg);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("sccp")
    }
}
