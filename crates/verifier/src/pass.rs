//! Verification pass

use crate::VerificationCtx;

pub trait VerificationPass {
    fn run(&mut self, ctx: VerificationCtx);
}
