use std::path::{Path, PathBuf};

use sonatina_codegen::optim::jump_thread::JumpThread;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

pub struct JumpThreadTransform;

impl FuncTransform for JumpThreadTransform {
    fn transform(&mut self, func: &mut Function) {
        JumpThread::new().run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("jump_thread")
    }
}
