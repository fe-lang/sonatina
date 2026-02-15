mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::optim::Pipeline;
use sonatina_ir::ir_writer::ModuleWriter;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/opt_pipeline/",
    glob: "*.sntn"
)]
fn test_opt_pipeline(fixture: Fixture<&str>) {
    let mut parsed = common::parse_module(fixture.path());
    Pipeline::default_pipeline().run(&mut parsed.module);

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    snap_test!(writer.dump_string(), fixture.path());
}
