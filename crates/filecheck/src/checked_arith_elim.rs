use std::path::{Path, PathBuf};

use sonatina_codegen::{
    cfg_edit::CleanupMode,
    domtree::DomTree,
    loop_analysis::LoopTree,
    optim::{
        branch_canonicalize::BranchCanonicalize, cfg_cleanup::CfgCleanup,
        checked_arith_elim::CheckedArithElim, load_store::LoadStoreSolver, sccp::SccpSolver,
    },
};
use sonatina_ir::{ControlFlowGraph, Function};

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct CheckedArithElimTransform {
    cfg: ControlFlowGraph,
    domtree: DomTree,
    lpt: LoopTree,
}

impl FuncTransform for CheckedArithElimTransform {
    fn transform(&mut self, func: &mut Function) {
        BranchCanonicalize::new().run(func);

        self.cfg.compute(func);
        LoadStoreSolver::new().run(func, &mut self.cfg);
        self.cfg.compute(func);
        self.domtree.compute(&self.cfg);
        self.lpt.compute(&self.cfg, &self.domtree);
        CheckedArithElim::new().run(func, &self.cfg, &self.lpt);

        self.cfg.compute(func);
        SccpSolver::new().run(func, &mut self.cfg);
        CfgCleanup::new(CleanupMode::Strict).run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("checked_arith_elim")
    }
}
