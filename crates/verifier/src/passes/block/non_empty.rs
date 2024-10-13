use smallvec::SmallVec;

use crate::{
    error::{ErrorData, ErrorKind::EmptyBlock, TraceInfoBuilder},
    pass::VerificationResult,
    VerificationCtx, VerificationPass,
};

pub struct NonEmpty;

impl VerificationPass for NonEmpty {
    fn run(&mut self, ctx: &mut VerificationCtx) -> VerificationResult {
        let layout = &ctx.func.layout;

        let mut errs = SmallVec::<[ErrorData; 8]>::new();

        for block in layout.iter_block() {
            if layout.is_block_empty(block) {
                let trace_info = TraceInfoBuilder::new(ctx.func_ref).block(block).build();
                let e = ErrorData::new(EmptyBlock(block), trace_info);
                errs.push(e);
            }
        }

        if !errs.is_empty() {
            ctx.report_nonfatal(errs);

            return VerificationResult::Fail;
        }

        VerificationResult::Pass
    }
}
