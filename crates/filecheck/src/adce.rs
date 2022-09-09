use std::path::{Path, PathBuf};

use sonatina_codegen::optim::adce::AdceSolver;

use sonatina_ir::{isa::TargetIsa, Function};

use super::{FuncTransform, FIXTURE_ROOT};

#[derive(Default)]
pub struct AdceTransform {}

impl FuncTransform for AdceTransform {
    fn transform(&mut self, func: &mut Function, isa: &TargetIsa) {
        let mut solver = AdceSolver::new(isa);
        solver.run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("adce")
    }
}
