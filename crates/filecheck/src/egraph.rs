use std::path::{Path, PathBuf};

use sonatina_codegen::optim::egraph::run_egraph_pass;

use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct EgraphTransform {}

impl FuncTransform for EgraphTransform {
    fn transform(&mut self, func: &mut Function) {
        run_egraph_pass(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("egraph")
    }
}
