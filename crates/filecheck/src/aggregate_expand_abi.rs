use std::path::{Path, PathBuf};

use sonatina_codegen::transform::aggregate::AggregateExpandAbi;
use sonatina_ir::{Function, Module};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct AggregateExpandAbiTransform;

impl FuncTransform for AggregateExpandAbiTransform {
    fn transform(&mut self, _: &mut Function) {}

    fn transform_module(&mut self, module: &Module) {
        AggregateExpandAbi::default().run(module);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("aggregate_expand_abi")
    }
}
