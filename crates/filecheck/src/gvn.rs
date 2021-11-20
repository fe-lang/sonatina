use std::path::{Path, PathBuf};

use sonatina_codegen::{cfg::ControlFlowGraph, optim::gvn::GvnSolver, Function};

use super::{FuncTransform, FIXTURE_ROOT};

#[derive(Default)]
pub struct GvnTransform {
    solver: GvnSolver,
    cfg: ControlFlowGraph,
}

impl FuncTransform for GvnTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.solver.run(func, &self.cfg);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("gvn")
    }
}
