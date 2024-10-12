//! Verification pass

use cranelift_entity::entity_impl;

use crate::{error::ErrorData, VerificationCtx};

#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct PassRef(pub u32);
entity_impl!(PassRef, "pass");

pub trait VerificationPass {
    fn new(pass_ref: PassRef) -> Self;

    fn run(&mut self, ctx: VerificationCtx);

    fn report_nonfatal(&self, ctx: &mut VerificationCtx, errs: &[ErrorData]) {
        for e in errs {
            let _err_ref = ctx.error_stack.push(*e);
        }
    }

    fn report_fatal(&self, _ctx: &VerificationCtx, _e: ErrorData) -> !;
}
