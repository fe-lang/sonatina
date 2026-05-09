use std::path::{Path, PathBuf};

use sonatina_codegen::optim::load_store::LoadStoreSolver;
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct LoadStoreTransform {
    cfg: ControlFlowGraph,
}

impl FuncTransform for LoadStoreTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        LoadStoreSolver::new().run(func, &mut self.cfg);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("load_store")
    }
}
