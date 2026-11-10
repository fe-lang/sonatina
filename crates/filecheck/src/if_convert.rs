use std::path::{Path, PathBuf};

use sonatina_codegen::optim::if_convert::IfConvert;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

pub struct IfConvertTransform;

impl FuncTransform for IfConvertTransform {
    fn transform(&mut self, func: &mut Function) {
        IfConvert.run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("if_convert")
    }
}
