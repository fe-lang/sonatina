use sonatina_filecheck::{
    FileCheckRunner, adce::AdceTransform, aggregate_combine::AggregateCombineTransform,
    aggregate_scalarize::AggregateScalarizeTransform, cfg_cleanup::CfgCleanupTransform,
    checked_arith_elim::CheckedArithElimTransform, gvn::GvnTransform, licm::LicmTransformer,
    loop_strength_reduce::LoopStrengthReduceTransform, sccp::SccpTransform,
};

fn main() {
    let mut runner = FileCheckRunner::new(SccpTransform::default());
    runner.run();

    runner.attach_transformer(CfgCleanupTransform::default());
    runner.run();

    runner.attach_transformer(AggregateCombineTransform);
    runner.run();

    runner.attach_transformer(AggregateScalarizeTransform);
    runner.run();

    runner.attach_transformer(AdceTransform::default());
    runner.run();

    runner.attach_transformer(CheckedArithElimTransform::default());
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
