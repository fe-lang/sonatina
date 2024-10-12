//! Verification pass

use crate::{error::ErrorData, VerificationCtx};

pub trait VerificationPass {
    fn run(&mut self, ctx: VerificationCtx);

    fn report_nonfatal(&self, ctx: &mut VerificationCtx, errs: &[ErrorData]) {
        for e in errs {
            let _err_ref = ctx.error_stack.push(*e);
        }
    }

    fn report_fatal(&self, ctx: &mut VerificationCtx, e: ErrorData);
}
