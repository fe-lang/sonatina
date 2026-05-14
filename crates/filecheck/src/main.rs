use sonatina_filecheck::{
    FileCheckRunner, adce::AdceTransform, aggregate_combine::AggregateCombineTransform,
    aggregate_scalarize::AggregateScalarizeTransform,
    branch_canonicalize::BranchCanonicalizeTransform, cfg_cleanup::CfgCleanupTransform,
    checked_arith_elim::CheckedArithElimTransform, gvn::GvnTransform,
    known_bits_simplify::KnownBitsSimplifyTransform, licm::LicmTransformer,
    load_store::LoadStoreTransform, loop_strength_reduce::LoopStrengthReduceTransform,
    range_branch_simplify::RangeBranchSimplifyTransform, sccp::SccpTransform,
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

    runner.attach_transformer(RangeBranchSimplifyTransform::default());
    runner.run();

    runner.attach_transformer(LoadStoreTransform::default());
    runner.run();

    runner.attach_transformer(GvnTransform::default());
    runner.run();

    runner.attach_transformer(LicmTransformer::default());
    runner.run();

    runner.attach_transformer(LoopStrengthReduceTransform::default());
    runner.run();

    runner.print_results();
    if !runner.is_ok() {
        std::process::exit(101);
    }
}
