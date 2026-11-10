use std::path::{Path, PathBuf};

use sonatina_codegen::{domtree::DomTree, optim::coalesce_object_copies::CoalesceObjectCopies};
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct CoalesceObjectCopiesTransform {
    cfg: ControlFlowGraph,
    domtree: DomTree,
}

impl FuncTransform for CoalesceObjectCopiesTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.domtree.compute(&self.cfg);
        CoalesceObjectCopies.run(func, &self.cfg, &self.domtree);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("coalesce_object_copies")
    }
}
