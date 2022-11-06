use std::path::{Path, PathBuf};

use sonatina_codegen::optim::insn_simplify::InsnSimplifySolver;

use sonatina_ir::Function;

use super::{FuncTransform, FIXTURE_ROOT};

#[derive(Default)]
pub struct InsnSimplifyTransform {}

impl FuncTransform for InsnSimplifyTransform {
    fn transform(&mut self, func: &mut Function) {
        let mut solver = InsnSimplifySolver::new();
        solver.run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("insn_simplify")
    }
}
