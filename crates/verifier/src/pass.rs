//! Verification pass

use crate::VerificationCtx;

pub trait VerificationPass {
    fn run(&mut self, ctx: &mut VerificationCtx) -> VerificationResult;
}

#[derive(Debug)]
pub enum VerificationResult {
    Pass,
    Fail,
    FailFatal,
}
