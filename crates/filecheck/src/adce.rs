use std::path::{Path, PathBuf};

use sonatina_codegen::optim::adce::AdceSolver;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct AdceTransform {}

impl FuncTransform for AdceTransform {
    fn transform(&mut self, func: &mut Function) {
        let mut solver = AdceSolver::new();
        solver.run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("adce")
    }
}
