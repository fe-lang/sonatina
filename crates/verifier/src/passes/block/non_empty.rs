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

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    use sonatina_ir::{
        builder::test_util::test_func_builder,
        inst::control_flow::{Jump, Return},
        isa::Isa,
        Type,
    };

    use super::*;

    #[test]
    fn non_empty_block() {
        let (evm, mut builder) = test_func_builder(&[], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let _b1 = builder.append_block(); // empty
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let _b4 = builder.append_block(); // empty
        let _b5 = builder.append_block(); // empty
        let b6 = builder.append_block();

        builder.switch_to_block(b0);
        builder.insert_inst_no_result_with(|| Jump::new(is, b2));

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Jump::new(is, b3));

        builder.switch_to_block(b3);
        builder.insert_inst_no_result_with(|| Jump::new(is, b6));

        builder.switch_to_block(b6);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();

        let module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &module.funcs[func_ref];

        let mut ctx = VerificationCtx::new(func_ref, func);
        let res = NonEmpty.run(&mut ctx);
        assert_eq!(res, VerificationResult::Fail);

        let mut err_msgs = String::new();

        let errs = ctx
            .error_stack
            .into_errs_iter(func, func_ref)
            .into_iter()
            .collect::<Vec<_>>();

        for e in errs {
            write!(&mut err_msgs, "{}\n", e).unwrap();
        }

        assert_eq!(
            "empty block, block1
trace_info:
0: block1
1: func public %test_func() -> unit
empty block, block4
trace_info:
0: block4
1: func public %test_func() -> unit
empty block, block5
trace_info:
0: block5
1: func public %test_func() -> unit
",
            err_msgs
        );
    }
}
