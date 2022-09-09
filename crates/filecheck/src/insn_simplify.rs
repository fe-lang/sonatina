use std::path::{Path, PathBuf};

use sonatina_codegen::optim::insn_simplify::InsnSimplifySolver;

use sonatina_ir::{isa::TargetIsa, Function};

use super::{FuncTransform, FIXTURE_ROOT};

#[derive(Default)]
pub struct InsnSimplifyTransform {}

impl FuncTransform for InsnSimplifyTransform {
    fn transform(&mut self, func: &mut Function, isa: &TargetIsa) {
        let mut solver = InsnSimplifySolver::new(isa);
        solver.run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("insn_simplify")
    }
}
