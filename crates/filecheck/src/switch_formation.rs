use std::path::{Path, PathBuf};

use sonatina_codegen::optim::switch_formation::SwitchFormation;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

pub struct SwitchFormationTransform;

impl FuncTransform for SwitchFormationTransform {
    fn transform(&mut self, func: &mut Function) {
        SwitchFormation::new().run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("switch_formation")
    }
}
