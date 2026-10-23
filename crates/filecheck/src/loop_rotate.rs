use std::path::{Path, PathBuf};

use sonatina_codegen::optim::loop_rotate::LoopRotate;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

pub struct LoopRotateTransform;

impl FuncTransform for LoopRotateTransform {
    fn transform(&mut self, func: &mut Function) {
        LoopRotate::new().run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("loop_rotate")
    }
}
