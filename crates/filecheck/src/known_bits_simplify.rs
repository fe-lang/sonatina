use std::path::{Path, PathBuf};

use sonatina_codegen::{
    cfg_edit::CleanupMode,
    optim::{cfg_cleanup::CfgCleanup, known_bits_simplify::KnownBitsSimplify},
};
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct KnownBitsSimplifyTransform;

impl FuncTransform for KnownBitsSimplifyTransform {
    fn transform(&mut self, func: &mut Function) {
        KnownBitsSimplify::new().run(func);
        CfgCleanup::new(CleanupMode::Strict).run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("known_bits_simplify")
    }
}
