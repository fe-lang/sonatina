mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::transform::aggregate::ObjectReturnOutParam;
use sonatina_ir::ir_writer::ModuleWriter;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

#[dir_test(dir: "$CARGO_MANIFEST_DIR/test_files/object_abi/", glob: "*.sntn")]
fn test_object_abi(fixture: Fixture<&str>) {
    let parsed = common::parse_module(fixture.path());

    ObjectReturnOutParam.run(&parsed.module);

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Standard),
    );
    assert!(
        !report.has_errors(),
        "object ABI rewriting should preserve verifier invariants:\n{report}"
    );

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    snap_test!(writer.dump_string(), fixture.path());
}

#[test]
fn object_abi_type_interning_is_deterministic() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/test_files/object_abi/get_function_ptr_params.sntn"
    );
    let compounds = || {
        let parsed = common::parse_module(path);
        ObjectReturnOutParam.run(&parsed.module);
        parsed.module.ctx.with_ty_store(|store| {
            store
                .all_compounds()
                .map(|(_, ty)| format!("{ty:?}"))
                .collect::<Vec<_>>()
        })
    };
    let first = compounds();
    for _ in 0..8 {
        assert_eq!(compounds(), first);
    }
}
