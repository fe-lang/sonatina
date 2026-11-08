use sonatina_filecheck::{
    FileCheckRunner, adce::AdceTransform, aggregate_combine::AggregateCombineTransform,
    aggregate_scalarize::AggregateScalarizeTransform, bool_phi_fold::BoolPhiFoldTransform,
    branch_canonicalize::BranchCanonicalizeTransform, cfg_cleanup::CfgCleanupTransform,
    checked_arith_elim::CheckedArithElimTransform, code_sink::CodeSinkTransform,
    compare_sub_fusion::CompareSubFusionTransform, gvn::GvnTransform,
    if_convert::IfConvertTransform, jump_thread::JumpThreadTransform,
    known_bits_simplify::KnownBitsSimplifyTransform, licm::LicmTransformer,
    load_store::LoadStoreTransform, loop_rotate::LoopRotateTransform,
    loop_strength_reduce::LoopStrengthReduceTransform,
    narrow_object_loads::NarrowObjectLoadsTransform,
    range_branch_simplify::RangeBranchSimplifyTransform, return_thread::ReturnThreadTransform,
    sccp::SccpTransform, switch_formation::SwitchFormationTransform,
};

fn main() {
    let mut runner = FileCheckRunner::new(SccpTransform::default());
    runner.run();

    runner.attach_transformer(CfgCleanupTransform::default());
    runner.run();

    runner.attach_transformer(BranchCanonicalizeTransform);
    runner.run();

    runner.attach_transformer(AggregateCombineTransform);
    runner.run();

    runner.attach_transformer(AggregateScalarizeTransform);
    runner.run();

    runner.attach_transformer(AdceTransform::default());
    runner.run();

    runner.attach_transformer(CheckedArithElimTransform::default());
    runner.run();

    runner.attach_transformer(KnownBitsSimplifyTransform);
    runner.run();

    runner.attach_transformer(JumpThreadTransform);
    runner.run();

    runner.attach_transformer(IfConvertTransform);
    runner.run();

    runner.attach_transformer(RangeBranchSimplifyTransform::default());
    runner.run();

    runner.attach_transformer(BoolPhiFoldTransform);
    runner.run();

    runner.attach_transformer(ReturnThreadTransform);
    runner.run();

    runner.attach_transformer(NarrowObjectLoadsTransform);
    runner.run();

    runner.attach_transformer(SwitchFormationTransform);
    runner.run();

    runner.attach_transformer(CompareSubFusionTransform::default());
    runner.run();

    runner.attach_transformer(LoadStoreTransform::default());
    runner.run();

    runner.attach_transformer(GvnTransform::default());
    runner.run();

    runner.attach_transformer(LicmTransformer::default());
    runner.run();

    runner.attach_transformer(LoopRotateTransform);
    runner.run();

    runner.attach_transformer(LoopStrengthReduceTransform::default());
    runner.run();

    runner.attach_transformer(CodeSinkTransform::default());
    runner.run();

    runner.print_results();
    if !runner.is_ok() {
        std::process::exit(101);
    }
}
