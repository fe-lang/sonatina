use std::path::{Path, PathBuf};

use sonatina_codegen::{cfg_edit::CleanupMode, optim::cfg_cleanup::CfgCleanup};
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct CfgCleanupTransform {}

impl FuncTransform for CfgCleanupTransform {
    fn transform(&mut self, func: &mut Function) {
        let mut pass = CfgCleanup::new(CleanupMode::Strict);
        pass.run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("cfg_cleanup")
    }
}
