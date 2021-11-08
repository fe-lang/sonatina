use sonatina_filecheck::{sccp::SccpTransform, FileCheckRunner};

fn main() {
    let mut sccp = FileCheckRunner::new(SccpTransform::default());
    sccp.run();
    sccp.print_results();
    if !sccp.is_ok() {
        std::process::exit(101);
    }
}
