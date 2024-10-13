use crate::{
    error::{
        ErrorKind::{NotEndedByTerminator, TerminatorBeforeEnd},
        TraceInfoBuilder,
    },
    pass::VerificationResult,
    VerificationCtx, VerificationPass,
};

pub struct EndInTerminator;

impl VerificationPass for EndInTerminator {
    fn run(&mut self, ctx: &mut VerificationCtx) -> VerificationResult {
        let layout = &ctx.func.layout;
        let dfg = &ctx.func.dfg;

        for block in layout.iter_block() {
            let last_inst = layout.last_inst_of(block).expect("pass dependency error");

            // check last instruction in block is terminator
            if !dfg.is_terminator(last_inst) {
                let trace_info = TraceInfoBuilder::new(ctx.func_ref).block(block).build();
                ctx.report_fatal(NotEndedByTerminator(last_inst), trace_info);

                return VerificationResult::FailFatal;
            }

            // check no instruction mid-block is terminator
            for inst in layout.iter_inst(block) {
                if inst == last_inst {
                    break;
                }

                if dfg.is_terminator(inst) {
                    let trace_info = TraceInfoBuilder::new(ctx.func_ref).block(block).build();
                    ctx.report_fatal(TerminatorBeforeEnd(inst), trace_info);

                    return VerificationResult::FailFatal;
                }
            }
        }

        VerificationResult::Pass
    }
}
