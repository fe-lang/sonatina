use sonatina_filecheck::{
    adce::AdceTransform, gvn::GvnTransform, sccp::SccpTransform, FileCheckRunner,
};

fn main() {
    let mut runner = FileCheckRunner::new(SccpTransform::default());
    runner.run();

    runner.attach_transformer(AdceTransform::default());
    runner.run();

    runner.attach_transformer(GvnTransform::default());
    runner.run();

    runner.print_results();
    if !runner.is_ok() {
        std::process::exit(101);
    }
}
