use std::path::{Path, PathBuf};

use sonatina_codegen::{
    cfg_edit::CleanupMode,
    domtree::DomTree,
    loop_analysis::LoopTree,
    optim::{cfg_cleanup::CfgCleanup, code_sink::CodeSink},
};
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct CodeSinkTransform {
    cfg: ControlFlowGraph,
    domtree: DomTree,
    lpt: LoopTree,
}

impl FuncTransform for CodeSinkTransform {
    fn transform(&mut self, func: &mut Function) {
        self.cfg.compute(func);
        self.domtree.compute(&self.cfg);
        self.lpt.compute(&self.cfg, &self.domtree);
        CodeSink::new().run(func, &self.cfg, &self.domtree, &self.lpt);
        CfgCleanup::new(CleanupMode::Strict).run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("code_sink")
    }
}
