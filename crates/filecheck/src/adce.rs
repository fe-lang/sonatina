use std::path::{Path, PathBuf};

use sonatina_codegen::{optim::adce::AdceSolver, Function};

use super::{FuncTransform, FIXTURE_ROOT};

#[derive(Default)]
pub struct AdceTransform {
    solver: AdceSolver,
}

impl FuncTransform for AdceTransform {
    fn transform(&mut self, func: &mut Function) {
        self.solver.run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("adce")
    }
}
