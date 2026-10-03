mod common;

use std::{fmt::Write, hint::black_box, time::Instant};

use dir_test::{Fixture, dir_test};
use sonatina_codegen::optim::aggregate::ObjectLoadStore;
use sonatina_ir::ir_writer::ModuleWriter;
use sonatina_parser::parse_module;
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

/// Run with `/usr/bin/time` as well when measuring on a shared machine. The
/// per-case timer excludes parsing; process CPU/RSS includes the entire probe.
#[test]
#[ignore = "manual release-profile scaling measurement; run with --release --ignored --nocapture"]
fn available_field_store_scaling() {
    if cfg!(debug_assertions) {
        panic!("measure a release-built compiler");
    }
    for fields in [64, 256, 1024, 4096, 16384] {
        for scalars in [0, 8192] {
            let mut source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc private %entry(v0.i256) -> objref<[i256; {fields}]> {{\nblock0:\nv1.objref<[i256; {fields}]> = obj.alloc [i256; {fields}];\n"
            );
            let mut next = 2;
            for field in 0..fields {
                writeln!(
                    source,
                    "v{next}.objref<i256> = obj.index v1 {field}.i64;\nobj.store v{next} v0;"
                )
                .unwrap();
                next += 1;
            }
            let mut previous = 0;
            for _ in 0..scalars {
                writeln!(source, "v{next}.i256 = add v{previous} 1.i256;").unwrap();
                previous = next;
                next += 1;
            }
            writeln!(
                source,
                "obj.store v{} v{previous};\nreturn v1;\n}}",
                fields + 1
            )
            .unwrap();
            let parsed = parse_module(&source).expect("valid object-store workload");
            let report = verify_module(
                &parsed.module,
                &VerifierConfig::for_level(VerificationLevel::Full),
            );
            assert!(!report.has_errors(), "{report}");
            let started = Instant::now();
            for function in parsed.module.funcs() {
                parsed.module.func_store.modify(function, |func| {
                    black_box(ObjectLoadStore::default().run(func));
                });
            }
            println!(
                "fields={fields},scalars={scalars},seconds={:.6}",
                started.elapsed().as_secs_f64()
            );
            let report = verify_module(
                &parsed.module,
                &VerifierConfig::for_level(VerificationLevel::Full),
            );
            assert!(!report.has_errors(), "{report}");
            black_box(parsed);
        }
    }
}
