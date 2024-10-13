use sonatina_ir::{module::FuncRef, BlockId, InstId};

use crate::{
    error::{ErrorData, ErrorKind, TraceInfoBuilder},
    pass::VerificationResult,
    VerificationCtx, VerificationPass,
};

pub struct EndInTerminator;

impl EndInTerminator {
    pub fn new_error_at(&mut self, inst: InstId, block: BlockId, func_ref: FuncRef) -> ErrorData {
        let trace_info = TraceInfoBuilder::new(func_ref).block(block).build();

        ErrorData::new(ErrorKind::NotEndedByTerminator(inst), trace_info)
    }
}

impl VerificationPass for EndInTerminator {
    fn run(&mut self, ctx: &mut VerificationCtx) -> VerificationResult {
        let layout = &ctx.func.layout;
        let dfg = &ctx.func.dfg;

        for block in layout.iter_block() {
            let last_inst = layout.last_inst_of(block).expect("pass dependency error");

            // check last instruction in block is terminator
            if !dfg.is_terminator(last_inst) {
                let e = self.new_error_at(last_inst, block, ctx.func_ref);
                ctx.report_fatal(e);

                return VerificationResult::FailFatal;
            }

            // check no instruction mid-block is terminator
            for inst in layout.iter_inst(block) {
                if inst == last_inst {
                    break;
                }

                if dfg.is_terminator(inst) {
                    let e = self.new_error_at(inst, block, ctx.func_ref);
                    ctx.report_fatal(e);

                    return VerificationResult::FailFatal;
                }
            }
        }

        VerificationResult::Pass
    }
}
