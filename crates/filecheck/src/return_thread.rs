use std::path::{Path, PathBuf};

use sonatina_codegen::optim::return_thread::ReturnThread;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

pub struct ReturnThreadTransform;

impl FuncTransform for ReturnThreadTransform {
    fn transform(&mut self, func: &mut Function) {
        ReturnThread.run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("return_thread")
    }
}
