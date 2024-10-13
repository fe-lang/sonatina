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

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        builder::test_util::test_func_builder,
        inst::{
            control_flow::{Jump, Return},
            logic::Xor,
        },
        isa::Isa,
        Type,
    };

    use super::*;

    #[test]
    fn last_inst_not_terminator() {
        let (evm, mut builder) = test_func_builder(&[Type::I1], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();

        let arg = builder.args()[0];

        builder.switch_to_block(b0);
        let c1 = builder.make_imm_value(false);
        builder.insert_inst_with(|| Xor::new(is, arg, c1), Type::I1);

        builder.seal_all();

        let module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &module.funcs[func_ref];

        let mut ctx = VerificationCtx::new(func_ref, func);
        let res = EndInTerminator.run(&mut ctx);
        assert_eq!(res, VerificationResult::FailFatal);

        let errs = ctx
            .error_stack
            .into_errs_iter(func, func_ref)
            .into_iter()
            .collect::<Vec<_>>();
        assert_eq!(1, errs.len());

        assert_eq!(
            "last instruction not terminator, xor v0 0.i1
trace_info:
0: block0
1: func public %test_func(i1) -> unit",
            errs[0].to_string()
        );
    }

    #[test]
    fn terminator_mid_block() {
        let (evm, mut builder) = test_func_builder(&[], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();

        builder.switch_to_block(b0);
        builder.insert_inst_no_result(Jump::new(is, b1));
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();

        let module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &module.funcs[func_ref];

        let mut ctx = VerificationCtx::new(func_ref, func);
        let res = EndInTerminator.run(&mut ctx);
        assert_eq!(res, VerificationResult::FailFatal);

        let errs = ctx
            .error_stack
            .into_errs_iter(func, func_ref)
            .into_iter()
            .collect::<Vec<_>>();
        assert_eq!(1, errs.len());

        assert_eq!(
            "terminator instruction mid-block, jump block1
trace_info:
0: block0
1: func public %test_func() -> unit",
            errs[0].to_string()
        );
    }
}
