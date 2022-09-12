use std::path::{Path, PathBuf};

use sonatina_codegen::{cfg::ControlFlowGraph, optim::sccp::SccpSolver};

use sonatina_ir::{isa::TargetIsa, Function};

use super::{FuncTransform, FIXTURE_ROOT};

#[derive(Default)]
pub struct SccpTransform {
    cfg: ControlFlowGraph,
}

impl FuncTransform for SccpTransform {
    fn transform(&mut self, func: &mut Function, isa: &TargetIsa) {
        self.cfg.compute(func);
        let mut solver = SccpSolver::new(isa);
        solver.run(func, &mut self.cfg);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("sccp")
    }
}
