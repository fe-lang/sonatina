use std::path::{Path, PathBuf};

use sonatina_codegen::optim::bool_phi_fold::BoolPhiFold;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

pub struct BoolPhiFoldTransform;

impl FuncTransform for BoolPhiFoldTransform {
    fn transform(&mut self, func: &mut Function) {
        BoolPhiFold::new().run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("bool_phi_fold")
    }
}
