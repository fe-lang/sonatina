mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::optim::aggregate::ObjectLowerToMemory;
use sonatina_ir::ir_writer::ModuleWriter;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/object_lowering/",
    glob: "*.sntn"
)]
fn test_object_lowering(fixture: Fixture<&str>) {
    let parsed = common::parse_module(fixture.path());

    ObjectLowerToMemory.run(&parsed.module);

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Standard),
    );
    assert!(
        !report.has_errors(),
        "object lowering should preserve verifier invariants:\n{report}"
    );

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    snap_test!(writer.dump_string(), fixture.path());
}
