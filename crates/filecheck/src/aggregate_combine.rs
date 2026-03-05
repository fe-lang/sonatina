use std::path::{Path, PathBuf};

use sonatina_codegen::{
    cfg_edit::CleanupMode,
    optim::{aggregate::AggregateCombine, cfg_cleanup::CfgCleanup},
};
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct AggregateCombineTransform;

impl FuncTransform for AggregateCombineTransform {
    fn transform(&mut self, func: &mut Function) {
        CfgCleanup::new(CleanupMode::Strict).run(func);
        AggregateCombine::default().run(func);
        CfgCleanup::new(CleanupMode::Strict).run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("aggregate_combine")
    }
}
