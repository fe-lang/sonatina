use std::path::{Path, PathBuf};

use sonatina_codegen::transform::erase_unit_values;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct EraseUnitValuesTransform;

impl FuncTransform for EraseUnitValuesTransform {
    fn transform(&mut self, func: &mut Function) {
        erase_unit_values(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("erase_unit_values")
    }
}
