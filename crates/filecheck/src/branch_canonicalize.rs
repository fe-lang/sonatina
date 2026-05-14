use std::path::{Path, PathBuf};

use sonatina_codegen::optim::branch_canonicalize::BranchCanonicalize;
use sonatina_ir::Function;

use super::{FIXTURE_ROOT, FuncTransform};

#[derive(Default)]
pub struct BranchCanonicalizeTransform;

impl FuncTransform for BranchCanonicalizeTransform {
    fn transform(&mut self, func: &mut Function) {
        BranchCanonicalize::new().run(func);
    }

    fn test_root(&self) -> PathBuf {
        Path::new(FIXTURE_ROOT).join("branch_canonicalize")
    }
}
