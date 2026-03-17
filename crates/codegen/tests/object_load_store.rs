mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::optim::aggregate::ObjectLoadStore;
use sonatina_ir::ir_writer::ModuleWriter;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/object_load_store/",
    glob: "*.sntn"
)]
fn test_object_load_store(fixture: Fixture<&str>) {
    let parsed = common::parse_module(fixture.path());

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Standard),
    );
    assert!(
        !report.has_errors(),
        "object/enum IR should verify before object load/store cleanup:\n{report}"
    );

    for func_ref in parsed.module.funcs() {
        parsed
            .module
            .func_store
            .modify(func_ref, |func| ObjectLoadStore::default().run(func));
    }

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Standard),
    );
    assert!(
        !report.has_errors(),
        "object load/store cleanup should preserve verifier invariants:\n{report}"
    );

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    snap_test!(writer.dump_string(), fixture.path());
}
