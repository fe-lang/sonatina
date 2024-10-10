//! Verification pass

use std::sync::Arc;

use cranelift_entity::entity_impl;

use crate::{error::ErrorData, VerificationCtx};

#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct PassRef(pub u32);
entity_impl!(PassRef, "pass");

pub trait VerificationPass {
    fn new(pass_ref: PassRef) -> Self;

    fn run(&mut self, ctx: Arc<VerificationCtx>);

    fn report_nonfatal(&self, ctx: &VerificationCtx, errs: &[ErrorData]) {
        ctx.with_error_stack_mut(|s| {
            for e in errs {
                let _err_ref = s.errors.push(*e);
            }
        })
    }

    fn report_fatal(&self, _ctx: &VerificationCtx, _e: ErrorData) -> !;
}
