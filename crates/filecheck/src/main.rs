use sonatina_filecheck::{
    adce::AdceTransform, licm::LicmTransformer, sccp::SccpTransform, FileCheckRunner,
};

fn main() {
    let mut runner = FileCheckRunner::new(SccpTransform::default());
    runner.run();

    runner.attach_transformer(AdceTransform::default());
    runner.run();

    // TODO: Uncomment here when we implement corresponding egglog optimization
    // pass. runner.attach_transformer(InsnSimplifyTransform::default());
    // runner.run();

    // runner.attach_transformer(GvnTransform::default());
    // runner.run();

    runner.attach_transformer(LicmTransformer::default());
    runner.run();

    runner.print_results();
    if !runner.is_ok() {
        std::process::exit(101);
    }
}
