use std::path::{Path, PathBuf};

use sonatina_codegen::optim::narrow_object_loads::NarrowObjectLoads;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

pub struct NarrowObjectLoadsTransform;

impl FuncTransform for NarrowObjectLoadsTransform {
    fn transform(&mut self, func: &mut Function) {
        NarrowObjectLoads.run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("narrow_object_loads")
    }
}
