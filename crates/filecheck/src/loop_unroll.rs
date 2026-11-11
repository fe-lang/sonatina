use std::path::{Path, PathBuf};

use sonatina_codegen::optim::loop_unroll::LoopUnroll;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

pub struct LoopUnrollTransform;

impl FuncTransform for LoopUnrollTransform {
    fn transform(&mut self, func: &mut Function) {
        LoopUnroll::default().run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("loop_unroll")
    }
}

pub struct LoopUnrollSmallTransform;

impl FuncTransform for LoopUnrollSmallTransform {
    fn transform(&mut self, func: &mut Function) {
        LoopUnroll::small().run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("loop_unroll_small")
    }
}
