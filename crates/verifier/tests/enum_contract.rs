//! Executable specification for the enum verifier replacement.
//!
//! Concrete executions independently check rejection and required acceptance at
//! both semantic verification levels. Exploration exhaustion is not a proof.
#[path = "support/enum_concrete.rs"]
mod concrete;

use sonatina_parser::parse_module;
use sonatina_verifier::{Location, VerificationLevel, VerifierConfig, verify_module};

fn execute(source: &str, limit: usize) -> concrete::Execution {
    let run = concrete::execute(source, limit);
    if run.exhausted == 0 {
        let parsed = parse_module(source).expect("valid fixture syntax");
        for level in [VerificationLevel::Standard, VerificationLevel::Full] {
            let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
            for (&(func, inst), &readable) in &run.reads {
                let rejected = report.errors().any(|diagnostic| matches!(diagnostic.primary, Location::Inst { func: at_func, inst: at, .. } if at_func == func && at == inst));
                assert_eq!(
                    rejected, !readable,
                    "{level:?} read {inst:?}: {source}\n{report}\n{run:?}"
                );
            }
            assert_eq!(
                report.is_ok(),
                run.invalid_reads() == 0,
                "{level:?}: {source}\n{report}\n{run:?}"
            );
        }
    }
    run
}

const CASES: &[(&str, &str, usize)] = &[
    (
        "direct-unwritten-scalar",
        include_str!("fixtures/enum_contract/direct-unwritten-scalar.sntn"),
        1,
    ),
    (
        "phi-unwritten-scalar",
        include_str!("fixtures/enum_contract/phi-unwritten-scalar.sntn"),
        1,
    ),
    (
        "direct-inactive-scalar",
        include_str!("fixtures/enum_contract/direct-inactive-scalar.sntn"),
        1,
    ),
    (
        "phi-inactive-scalar",
        include_str!("fixtures/enum_contract/phi-inactive-scalar.sntn"),
        1,
    ),
    (
        "direct-inactive-payload",
        include_str!("fixtures/enum_contract/direct-inactive-payload.sntn"),
        1,
    ),
    (
        "descendant-inactive-payload",
        include_str!("fixtures/enum_contract/descendant-inactive-payload.sntn"),
        1,
    ),
    (
        "fresh-vs-input",
        include_str!("fixtures/enum_contract/fresh-vs-input.sntn"),
        0,
    ),
    (
        "fresh-no-input-write",
        include_str!("fixtures/enum_contract/fresh-no-input-write.sntn"),
        0,
    ),
    (
        "recovered-alias",
        include_str!("fixtures/enum_contract/recovered-alias.sntn"),
        1,
    ),
    (
        "private-container",
        include_str!("fixtures/enum_contract/private-container.sntn"),
        0,
    ),
    (
        "private-container-no-raw-write",
        include_str!("fixtures/enum_contract/private-container-no-raw-write.sntn"),
        0,
    ),
    (
        "exposed-container",
        include_str!("fixtures/enum_contract/exposed-container.sntn"),
        1,
    ),
    (
        "nested-same-tag",
        include_str!("fixtures/enum_contract/nested-same-tag.sntn"),
        0,
    ),
    (
        "nested-no-tag-write",
        include_str!("fixtures/enum_contract/nested-no-tag-write.sntn"),
        0,
    ),
    (
        "nested-payloadless-tag",
        include_str!("fixtures/enum_contract/nested-payloadless-tag.sntn"),
        0,
    ),
    (
        "nested-different-payload-tag",
        include_str!("fixtures/enum_contract/nested-different-payload-tag.sntn"),
        1,
    ),
];

#[test]
fn concrete_calls_have_independent_read_witnesses() {
    for (source, invalid) in [
        (
            include_str!("fixtures/enum_contract/call-returned-raw-alias.sntn"),
            1,
        ),
        (
            include_str!("fixtures/enum_contract/call-derived-holder.sntn"),
            1,
        ),
        (
            include_str!("fixtures/enum_contract/call-derived-return.sntn"),
            1,
        ),
        (
            include_str!("fixtures/enum_contract/private-unrelated-call.sntn"),
            0,
        ),
    ] {
        let run = concrete::execute(source, 128);
        assert_eq!(run.invalid_reads(), invalid, "{run:?}");
        assert_eq!(run.exhausted, 0);
        assert!(run.returned > 0);
    }
}

#[test]
fn calls_replace_reference_array_summaries_and_existing_cells() {
    let source = r#"
target = "evm-ethereum-osaka"
type @R = { i256 };
func private %replace(v0.objref<[objref<@R>; 2]>, v1.objref<@R>) {
block0:
 v2.objref<objref<@R>> = obj.index v0 0.i8;
 obj.store v2 v1;
 return;
}
func private %entry() -> i256 {
block0:
 v0.objref<@R> = obj.alloc @R;
 v1.objref<i256> = obj.proj v0 0.i8;
 obj.store v1 17.i256;
 v2.objref<[objref<@R>; 2]> = obj.alloc [objref<@R>; 2];
 v3.objref<objref<@R>> = obj.index v2 0.i8;
 obj.store v3 v0;
 v4.objref<objref<@R>> = obj.index v2 1.i8;
 obj.store v4 v0;
 call %replace v2 v0;
 v5.objref<objref<@R>> = obj.index v2 0.i8;
 v6.objref<@R> = obj.load v5;
 v7.objref<i256> = obj.proj v6 0.i8;
 v8.i256 = obj.load v7;
 return v8;
}
"#;
    for with_enum in [false, true] {
        let source = if with_enum {
            source
                .replace("type @R", "type @E = enum { #Some(i256) };\ntype @R")
                .replace(
                    "func private %entry() -> i256 {\nblock0:",
                    "func private %entry() -> i256 {\nblock0:\n v20.objref<@E> = obj.alloc @E;\n enum.write_variant v20 #Some (31.i256);",
                )
        } else {
            source.to_owned()
        };
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), 0);
        assert_eq!(run.returned, 1);
    }
}

#[test]
fn calls_preserve_private_objects_and_reference_cells() {
    let source = include_str!("fixtures/enum_contract/private-unrelated-call.sntn");
    for holder in [false, true] {
        let source = if holder {
            source
                .replace("func private %noise", "type @Holder = { objref<i256> };\nfunc private %noise")
                .replace(
                    " v2.i256 = call %noise",
                    " v40.objref<@Holder> = obj.alloc @Holder;\n v4.objref<objref<i256>> = obj.proj v40 0.i8;\n obj.store v4 v1;\n v2.i256 = call %noise",
                )
                .replace(" v3.i256 = obj.load v1;", " v5.objref<i256> = obj.load v4;\n v3.i256 = obj.load v5;")
        } else {
            source.to_owned()
        };
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), 0);
        assert_eq!(run.returned, 1);
    }
}

#[test]
fn call_eligibility_includes_undefined_enum_reference_arguments() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #Some(i256) };
func private %derive(v0.objref<@E>) -> objref<i256> {
block0:
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 return v1;
}
func private %entry() -> i256 {
block0:
 v0.objref<i256> = call %derive undef.objref<@E>;
 v1.i256 = obj.load v0;
 return v1;
}
"#;
    let parsed = parse_module(source).unwrap();
    for level in [VerificationLevel::Standard, VerificationLevel::Full] {
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert!(
            report
                .errors()
                .any(|error| error.message.contains("unknown local reference provenance")),
            "{report}"
        );
    }
}

#[test]
fn call_returned_reference_arrays_keep_unrelated_objects_private() {
    let source = include_str!("fixtures/enum_contract/private-unrelated-call.sntn")
        .replace(
            "func private %entry",
            r#"func private %references() -> [objref<i256>; 2] {
block0:
 v0.objref<i256> = obj.alloc i256;
 obj.store v0 31.i256;
 v1.[objref<i256>; 2] = insert_value undef.[objref<i256>; 2] 0.i8 v0;
 v2.[objref<i256>; 2] = insert_value v1 1.i8 v0;
 return v2;
}
func private %entry"#,
        )
        .replace(
            " v2.i256 = call %noise",
            " v10.[objref<i256>; 2] = call %references;\n v2.i256 = call %noise",
        );
    let run = execute(&source, 128);
    assert_eq!(run.invalid_reads(), 0);
    assert_eq!(run.returned, 1);
}

#[test]
fn call_returned_objects_are_externally_reachable() {
    let source =
        include_str!("fixtures/enum_contract/call-returned-raw-alias.sntn").replace("\r\n", "\n");
    // include_str! retains checkout line endings; exercise both forms on every host.
    for source in [source.clone(), source.replace('\n', "\r\n")] {
        for write in [
            "",
            "mstore v100 0.i256 i256;",
            "v9.*i256 = alloca i256;\n mstore v9 0.i256 i256;",
        ] {
            for observed in [false, true] {
                let mut source = source.replace("mstore v100 0.i256 i256;", write);
                if observed {
                    source = source
                    .replace(" v2.objref<i256> = enum.proj v1 #Some 0.i8;", " v2.enumtag(@E) = enum.get_tag v1;")
                    .replace(" v3.i256 = obj.load v2;", " br_table v2 block2 (1.enumtag(@E) block1);\nblock1:\n v4.objref<i256> = enum.proj v1 #Some 0.i8;\n v3.i256 = obj.load v4;")
                    .replace(" return v3;", " return v3;\nblock2:\n return 0.i256;");
                }
                let run = execute(&source, 128);
                assert_eq!(
                    run.invalid_reads(),
                    usize::from(write.starts_with("mstore"))
                );
                assert!(run.returned > 0);
            }
        }
    }
}

#[test]
fn calls_derive_payload_aliases_without_caller_projections() {
    for source in [
        include_str!("fixtures/enum_contract/call-derived-holder.sntn"),
        include_str!("fixtures/enum_contract/call-derived-return.sntn"),
    ] {
        for before in [
            "",
            "v40.enumtag(@E) = enum.get_tag v0;",
            "v40.objref<i256> = enum.proj v0 #Some 0.i8;",
        ] {
            for initialize in [false, true] {
                let source = source
                    .replace(
                        " call %change v0 v1;",
                        &format!(" {before}\n call %change v0 v1;"),
                    )
                    .replace(
                        " v1.objref<i256> = call %derive v0;",
                        &format!(" {before}\n v1.objref<i256> = call %derive v0;"),
                    );
                let source = if initialize {
                    source
                        .replace(" v5.objref<i256> = obj.load v2;", " enum.write_variant v0 #Some (31.i256);\n v5.objref<i256> = obj.load v2;")
                        .replace(" v2.i256 = obj.load v1;", " enum.write_variant v0 #Some (31.i256);\n v2.i256 = obj.load v1;")
                } else {
                    source
                };
                let run = execute(&source, 128);
                assert_eq!(run.invalid_reads(), usize::from(!initialize));
                assert_eq!(run.returned, 1);
            }
        }
    }
}

#[test]
fn nested_call_holders_preserve_derived_reference_guards() {
    let source = include_str!("fixtures/enum_contract/call-derived-holder.sntn")
        .replace("func private %change", "type @Outer = { objref<@Holder> };\nfunc private %change")
        .replace("func private %entry", r#"func private %wrap(v100.objref<@E>, v101.objref<@Outer>) {
block0:
 v0.objref<objref<@Holder>> = obj.proj v101 0.i8;
 v1.objref<@Holder> = obj.load v0;
 call %change v100 v1;
 return;
}
func private %entry"#)
        .replace(" call %change v0 v1;", " v7.objref<@Outer> = obj.alloc @Outer;\n v8.objref<objref<@Holder>> = obj.proj v7 0.i8;\n obj.store v8 v1;\n call %wrap v0 v7;");
    for restored in [false, true] {
        let source = if restored {
            source.replace(
                " v5.objref<i256> = obj.load v2;",
                " enum.write_variant v0 #Some (31.i256);\n v5.objref<i256> = obj.load v2;",
            )
        } else {
            source.clone()
        };
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), usize::from(!restored));
        assert_eq!(run.returned, 1);
    }
}

#[test]
fn repeated_calls_rebind_derived_results_without_losing_guards() {
    let source = include_str!("fixtures/enum_contract/call-derived-return.sntn")
        .replace(" v1.objref<i256> = call %derive v0;", " jump block1;\nblock1:\n v3.i8 = phi (0.i8 block0) (v4 block1);\n v1.objref<i256> = call %derive v0;")
        .replace(" return v2;", " v4.i8 = add v3 1.i8;\n v5.i1 = lt v4 2.i8;\n br v5 block1 block2;\nblock2:\n return v2;");
    for restored in [false, true] {
        let source = if restored {
            source.replace(
                " v2.i256 = obj.load v1;",
                " enum.write_variant v0 #Some (31.i256);\n v2.i256 = obj.load v1;",
            )
        } else {
            source.clone()
        };
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), usize::from(!restored));
        assert_eq!(run.exhausted, 0);
        assert_eq!(run.returned, 1);
    }
}

#[test]
fn call_derived_array_subobjects_use_bounded_typed_summaries() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
func private %derive(v100.objref<[@E; 2]>) -> objref<i256> {
block0:
 v0.objref<@E> = obj.index v100 0.i256;
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 enum.set_tag v0 #None;
 return v1;
}
func private %entry() -> i256 {
block0:
 v0.objref<[@E; 2]> = obj.alloc [@E; 2];
 v1.objref<@E> = obj.index v0 0.i256;
 enum.write_variant v1 #Some (17.i256);
 v2.objref<i256> = call %derive v0;
 v3.i256 = obj.load v2;
 return v3;
}
"#;
    assert_eq!(execute(source, 128).invalid_reads(), 1);
    let large = source.replace("[@E; 2]", "[@E; 1000000000]");
    let parsed = parse_module(&large).unwrap();
    for level in [VerificationLevel::Standard, VerificationLevel::Full] {
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert!(
            report
                .errors()
                .any(|error| error.message.contains("ancestor enum variant")),
            "{report}"
        );
    }
}

#[test]
fn returned_opaque_holders_publish_later_stored_references() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
type @Holder = { objref<@E> };
func private %holder() -> objref<@Holder> {
block0:
 v0.objref<@Holder> = obj.alloc @Holder;
 v1.*@Holder = obj.materialize.heap v0;
 return v0;
}
func private %entry(v100.*i256) -> i256 {
block0:
 v0.objref<@Holder> = call %holder;
 v1.objref<objref<@E>> = obj.proj v0 0.i8;
 v2.objref<@E> = obj.alloc @E;
 obj.store v1 v2;
 enum.write_variant v2 #Some (17.i256);
 v3.objref<i256> = enum.proj v2 #Some 0.i8;
 mstore v100 0.i256 i256;
 v4.i256 = obj.load v3;
 return v4;
}
"#;
    assert_eq!(execute(source, 128).invalid_reads(), 1);
    let safe = source.replace("mstore v100 0.i256 i256;", "");
    assert_eq!(execute(&safe, 128).invalid_reads(), 0);
}

#[test]
fn documented_controls_have_concrete_witnesses() {
    for &(name, source, invalid) in CASES {
        let run = execute(source, 128);
        assert_eq!(run.exhausted, 0, "{name}: {run:?}");
        assert!(run.returned > 0, "vacuous fixture {name}: {run:?}");
        assert!(!run.reads.is_empty(), "no covered read in {name}");
        assert_eq!(run.invalid_reads(), invalid, "{name}: {run:?}");
    }
}

#[test]
fn local_carriers_preserve_initialized_and_invalid_read_outcomes() {
    for (carrier, reference) in [
        ("", "v1"),
        (
            "jump block1;\nblock1:\n v2.objref<i256> = phi (v1 block0);",
            "v2",
        ),
        (
            "v2.@Holder = insert_value undef.@Holder 0.i8 v1;\n v3.objref<i256> = extract_value v2 0.i8;",
            "v3",
        ),
        (
            "v2.@Carrier = enum.make @Carrier #Wrap (v1);\n v3.objref<i256> = enum.extract v2 #Wrap 0.i8;",
            "v3",
        ),
        (
            "v2.objref<@Holder> = obj.alloc @Holder;\n v3.objref<objref<i256>> = obj.proj v2 0.i8;\n obj.store v3 v1;\n v4.objref<i256> = obj.load v3;",
            "v4",
        ),
    ] {
        for (initialization, mutation, invalid) in [
            ("enum.set_tag v0 #Some;", "", 1),
            ("enum.write_variant v0 #Some (17.i256);", "", 0),
            (
                "enum.write_variant v0 #Some (17.i256);",
                "enum.set_tag v0 #None;",
                1,
            ),
        ] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256) }};
type @Holder = {{ objref<i256> }};
type @Carrier = enum {{ #Wrap(objref<i256>) }};
func private %entry() -> i256 {{
block0:
 v0.objref<@Choice> = obj.alloc @Choice;
 {initialization}
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 {carrier}
 {mutation}
 v10.i256 = obj.load {reference};
 return v10;
}}
"#
            );
            let run = execute(&source, 128);
            assert_eq!(run.exhausted, 0, "{source}");
            assert_eq!(run.returned, 1, "{source}");
            assert_eq!(run.invalid_reads(), invalid, "{source}\n{run:?}");
        }
    }
}

#[test]
fn assertions_filter_executions_without_initializing_storage() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Choice = enum { #None, #Some(i256) };
func private %entry() -> i256 {
block0:
 v0.objref<@Choice> = obj.alloc @Choice;
 enum.set_tag v0 #Some;
 v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;
 v2.objref<i256> = enum.proj v1 #Some 0.i8;
 v3.i256 = obj.load v2;
 return v3;
}
"#;
    let run = execute(source, 128);
    assert_eq!(run.assumptions_pruned, 1);
    assert_eq!(run.returned, 0);
    assert!(run.reads.is_empty());
    let initialized = source.replace(
        "enum.set_tag v0 #Some;",
        "enum.write_variant v0 #Some (17.i256);",
    );
    let run = execute(&initialized, 128);
    assert_eq!(run.assumptions_pruned, 0);
    assert_eq!(run.returned, 1);
    assert_eq!(run.reads.len(), 1);
    assert_eq!(run.invalid_reads(), 0);
}

#[test]
fn phi_chooses_the_initialized_object_on_each_predecessor() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Choice = enum { #None, #Some(i256) };
func private %entry(v100.i1) -> i256 {
block0:
 br v100 block1 block2;
block1:
 v0.objref<@Choice> = obj.alloc @Choice;
 enum.write_variant v0 #Some (17.i256);
 jump block3;
block2:
 v1.objref<@Choice> = obj.alloc @Choice;
 enum.write_variant v1 #Some (31.i256);
 jump block3;
block3:
 v2.objref<@Choice> = phi (v0 block1) (v1 block2);
 v3.objref<i256> = enum.proj v2 #Some 0.i8;
 v4.i256 = obj.load v3;
 return v4;
}
"#;
    let run = execute(source, 128);
    assert_eq!(run.returned, 2);
    assert_eq!(run.invalid_reads(), 0);
    let missing = source.replace(
        "enum.write_variant v1 #Some (31.i256);",
        "enum.set_tag v1 #Some;",
    );
    let run = execute(&missing, 128);
    assert_eq!(run.returned, 2);
    assert_eq!(run.invalid_reads(), 1);
}

#[test]
fn repeated_allocation_does_not_reinitialize_an_older_instance() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Choice = enum { #None, #Some(i256) };
func private %entry() -> i256 {
block0:
 v0.objref<@Choice> = obj.alloc @Choice;
 enum.write_variant v0 #Some (17.i256);
 jump block1;
block1:
 v1.i8 = phi (0.i8 block0) (v2 block1);
 v3.objref<@Choice> = phi (v0 block0) (v4 block1);
 v4.objref<@Choice> = obj.alloc @Choice;
 enum.write_variant v4 #Some (31.i256);
 v5.objref<i256> = enum.proj v3 #Some 0.i8;
 v6.i256 = obj.load v5;
 enum.set_tag v4 #None;
 v2.i8 = add v1 1.i8;
 v7.i1 = lt v2 2.i8;
 br v7 block1 block2;
block2:
 return v6;
}
"#;
    let run = execute(source, 128);
    assert_eq!(run.exhausted, 0);
    assert_eq!(run.returned, 1);
    assert_eq!(run.max_objects, 3);
    assert_eq!(run.invalid_reads(), 1);
    let preserved = source.replace("enum.set_tag v4 #None;", "enum.set_tag v4 #Some;");
    assert_eq!(execute(&preserved, 128).invalid_reads(), 0);
    assert_eq!(execute(source, 4).exhausted, 1);
}

#[test]
fn containment_exposure_respects_store_order_and_exact_overwrites() {
    for order in ["before", "after"] {
        for overwrite in ["none", "before", "after"] {
            let expose = "v8.*@Outer = obj.materialize.stack v6;";
            let replace = "obj.store v3 v4;";
            let before = if order == "before" { expose } else { "" };
            let after = if order == "after" { expose } else { "" };
            let replace_before = if overwrite == "before" { replace } else { "" };
            let replace_after = if overwrite == "after" { replace } else { "" };
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256) }};
type @Holder = {{ objref<@Choice> }};
type @Outer = {{ objref<@Holder> }};
func private %entry(v100.*i256) -> i256 {{
block0:
 v0.objref<@Choice> = obj.alloc @Choice;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v2.objref<@Holder> = obj.alloc @Holder;
 v3.objref<objref<@Choice>> = obj.proj v2 0.i8;
 v4.objref<@Choice> = obj.alloc @Choice;
 enum.write_variant v4 #Some (31.i256);
 v6.objref<@Outer> = obj.alloc @Outer;
 v7.objref<objref<@Holder>> = obj.proj v6 0.i8;
 obj.store v7 v2;
 {before}
 obj.store v3 v0;
 {replace_before}
 {after}
 {replace_after}
 mstore v100 0.i256 i256;
 v10.i256 = obj.load v1;
 return v10;
}}
"#
            );
            let run = execute(&source, 128);
            assert_eq!(run.exhausted, 0);
            let remains_private = order == "after" && overwrite == "before";
            assert_eq!(
                run.invalid_reads(),
                usize::from(!remains_private),
                "{source}\n{run:?}"
            );
        }
    }
}

#[test]
fn snapshots_copy_values_and_retain_references_to_mutable_objects() {
    for reference in [false, true] {
        let (field_ty, field_value, read) = if reference {
            (
                "objref<i256>",
                "v1",
                "v5.objref<i256> = extract_value v4 0.i8;\n v6.i256 = obj.load v5;",
            )
        } else {
            ("i256", "17.i256", "v6.i256 = extract_value v4 0.i8;")
        };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256) }};
type @Copy = {{ {field_ty} }};
func private %entry() -> i256 {{
block0:
 v0.objref<@Choice> = obj.alloc @Choice;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v2.objref<@Copy> = obj.alloc @Copy;
 v3.@Copy = insert_value undef.@Copy 0.i8 {field_value};
 obj.store v2 v3;
 v4.@Copy = obj.load v2;
 enum.set_tag v0 #None;
 {read}
 return v6;
}}
"#
        );
        let run = execute(&source, 128);
        assert_eq!(run.returned, 1);
        assert_eq!(run.invalid_reads(), usize::from(reference), "{source}");
    }
}

#[test]
fn descendant_reads_require_ancestors_but_not_unrelated_siblings() {
    for array in [false, true] {
        let (payload, projection) = if array {
            (
                "[i256; 2]",
                "v2.objref<i256> = obj.index v1 0.i256;\n v3.objref<i256> = obj.index v1 1.i8;",
            )
        } else {
            (
                "@Pair",
                "v2.objref<i256> = obj.proj v1 0.i256;\n v3.objref<i256> = obj.proj v1 1.i8;",
            )
        };
        for (mutation, invalid) in [("", 1), ("enum.set_tag v0 #None;", 2)] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @Pair = {{ i256, i256 }};
type @Choice = enum {{ #None, #Some({payload}) }};
func private %entry() -> i256 {{
block0:
 v0.objref<@Choice> = obj.alloc @Choice;
 enum.set_tag v0 #Some;
 v1.objref<{payload}> = enum.proj v0 #Some 0.i8;
 {projection}
 obj.store v2 17.i256;
 {mutation}
 v4.i256 = obj.load v2;
 v5.i256 = obj.load v3;
 return v4;
}}
"#
            );
            let run = execute(&source, 128);
            assert_eq!(run.returned, 1);
            assert_eq!(run.invalid_reads(), invalid, "{source}");
        }
    }
}

#[test]
fn copying_an_unwritten_nested_enum_does_not_initialize_its_payload() {
    let source = include_str!("fixtures/enum_contract/copied-unwritten-nested-enum.sntn");
    for write in ["obj.store v3 v1;", "enum.write_variant v2 #Some (v1);"] {
        for initialized in [false, true] {
            let source = source.replace("obj.store v3 v1;", write);
            let source = if initialized {
                source.replace(
                    "enum.set_tag v0 #Some;",
                    "enum.write_variant v0 #Some (17.i256);",
                )
            } else {
                source
            };
            let run = execute(&source, 128);
            assert_eq!(run.returned, 1);
            assert_eq!(run.exhausted, 0);
            assert_eq!(run.reads.len(), 1);
            assert_eq!(run.invalid_reads(), usize::from(!initialized), "{source}");
        }
    }
}

#[test]
fn a_store_through_a_phi_establishes_the_selected_view() {
    for initialize in [true, false] {
        let write = if initialize {
            "obj.store v4 17.i256;"
        } else {
            ""
        };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry(v100.i1) -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.set_tag v0 #Some;
 v1.objref<@E> = obj.alloc @E;
 enum.set_tag v1 #Some;
 br v100 block1 block2;
block1:
 jump block3;
block2:
 jump block3;
block3:
 v2.objref<@E> = phi (v0 block1) (v1 block2);
 v4.objref<i256> = enum.proj v2 #Some 0.i8;
 {write}
 v5.objref<i256> = enum.proj v2 #Some 0.i256;
 v6.i256 = obj.load v5;
 return v6;
}}
"#
        );
        assert_eq!(
            execute(&source, 128).invalid_reads(),
            usize::from(!initialize)
        );
    }
}

#[test]
fn immutable_and_paired_phi_observations_refine_only_the_observed_value() {
    for immutable in [false, true] {
        for predicate in [false, true] {
            if predicate && !immutable {
                continue;
            }
            let (ty, left, right, tag_left, tag_right, tag_ty, branch, read) = if immutable {
                let (tag_left, tag_right, tag_ty, branch) = if predicate {
                    (
                        "v10.i1 = enum.is_variant v0 #Some;",
                        "v11.i1 = enum.is_variant v1 #Some;",
                        "i1",
                        "br v3 block4 block5;",
                    )
                } else {
                    (
                        "v10.enumtag(@E) = enum.tag v0;",
                        "v11.enumtag(@E) = enum.tag v1;",
                        "enumtag(@E)",
                        "br_table v3 block5 (1.enumtag(@E) block4);",
                    )
                };
                (
                    "@E",
                    "v0.@E = enum.make @E #Some (17.i256);",
                    "v1.@E = enum.make @E #None;",
                    tag_left,
                    tag_right,
                    tag_ty,
                    branch,
                    "v5.i256 = enum.extract v2 #Some 0.i8;",
                )
            } else {
                (
                    "objref<@E>",
                    "v0.objref<@E> = obj.alloc @E;\n enum.write_variant v0 #Some (17.i256);",
                    "v1.objref<@E> = obj.alloc @E;\n enum.set_tag v1 #None;",
                    "v10.enumtag(@E) = enum.get_tag v0;",
                    "v11.enumtag(@E) = enum.get_tag v1;",
                    "enumtag(@E)",
                    "br_table v3 block5 (1.enumtag(@E) block4);",
                    "v4.objref<i256> = enum.proj v2 #Some 0.i8;\n v5.i256 = obj.load v4;",
                )
            };
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry(v100.i1) -> i256 {{
block0:
 br v100 block1 block2;
block1:
 {left}
 {tag_left}
 jump block3;
block2:
 {right}
 {tag_right}
 jump block3;
block3:
 v2.{ty} = phi (v0 block1) (v1 block2);
 v3.{tag_ty} = phi (v10 block1) (v11 block2);
 {branch}
block4:
 {read}
 return v5;
block5:
 return 0.i256;
}}
"#
            );
            assert_eq!(execute(&source, 128).invalid_reads(), 0);
        }
    }
}

#[test]
fn loop_index_rebinding_does_not_initialize_another_element() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #Some([i256; 2]) };
func private %entry() -> i256 {
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.set_tag v0 #Some;
 v1.objref<[i256; 2]> = enum.proj v0 #Some 0.i8;
 jump block1;
block1:
 v2.i8 = phi (0.i8 block0) (v3 block2);
 v4.objref<i256> = obj.index v1 v2;
 v5.i1 = lt v2 1.i8;
 br v5 block2 block3;
block2:
 obj.store v4 17.i256;
 v3.i8 = add v2 1.i8;
 jump block1;
block3:
 v6.i256 = obj.load v4;
 return v6;
}
"#;
    assert_eq!(execute(source, 128).invalid_reads(), 1);
    let source = source.replace(
        "v6.i256 = obj.load v4;",
        "obj.store v4 31.i256;\n v6.i256 = obj.load v4;",
    );
    assert_eq!(execute(&source, 128).invalid_reads(), 0);
}

#[test]
fn inactive_reference_cells_survive_conditional_joins_and_exposure() {
    for retain in [true, false] {
        let write = if retain {
            "enum.write_variant v2 #Hold (v0);"
        } else {
            ""
        };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
type @Holder = enum {{ #None, #Hold(objref<@E>) }};
func private %entry(v100.i1, v101.*i256) -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v2.objref<@Holder> = obj.alloc @Holder;
 enum.set_tag v2 #None;
 br v100 block1 block2;
block1:
 {write}
 enum.set_tag v2 #None;
 jump block3;
block2:
 jump block3;
block3:
 v3.*@Holder = obj.materialize.stack v2;
 mstore v101 0.i256 i256;
 v4.i256 = obj.load v1;
 return v4;
}}
"#
        );
        assert_eq!(execute(&source, 128).invalid_reads(), usize::from(retain));
    }
}

#[test]
fn repeated_allocations_preserve_the_older_instances_exposure() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
func private %entry(v100.*i256) -> i256 {
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 jump block1;
block1:
 v1.i8 = phi (0.i8 block0) (v2 block1);
 v3.objref<@E> = phi (v0 block0) (v4 block1);
 v4.objref<@E> = obj.alloc @E;
 enum.write_variant v4 #Some (31.i256);
 v8.*@E = obj.materialize.stack v4;
 v2.i8 = add v1 1.i8;
 v7.i1 = lt v2 2.i8;
 br v7 block1 block2;
block2:
 mstore v100 0.i256 i256;
 v5.objref<i256> = enum.proj v3 #Some 0.i8;
 v6.i256 = obj.load v5;
 return v6;
}
"#;
    assert_eq!(execute(source, 128).invalid_reads(), 1);
    let private = source.replace("v8.*@E = obj.materialize.stack v4;", "");
    assert_eq!(execute(&private, 128).invalid_reads(), 0);
}

#[test]
fn opaque_results_retain_local_guards() {
    for mutate in [false, true] {
        let mutation = if mutate { "enum.set_tag v0 #None;" } else { "" };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %identity(v100.objref<i256>) -> objref<i256> {{
block0:
 return v100;
}}
func private %entry() -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v2.objref<i256> = call %identity v1;
 v3.objref<@E> = enum.assert_variant_ref v0 #Some;
 {mutation}
 v4.i256 = obj.load v2;
 return v4;
}}
"#
        );
        let parsed = parse_module(&source).unwrap();
        for level in [VerificationLevel::Standard, VerificationLevel::Full] {
            let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
            // The call may return a different object, but its possible local
            // alias must still carry the guard of v1 after the parent retag.
            assert_eq!(report.has_errors(), mutate, "{source}\n{report}");
        }
    }
}

#[test]
fn imported_aggregate_references_predate_fresh_allocations() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
type @Input = { objref<@E>, objref<@E> };
func private %entry(v100.@Input) -> i256 {
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<@E> = extract_value v100 0.i8;
 enum.set_tag v1 #None;
 v2.objref<i256> = enum.proj v0 #Some 0.i8;
 v3.i256 = obj.load v2;
 return v3;
}
"#;
    for level in [VerificationLevel::Standard, VerificationLevel::Full] {
        let parsed = parse_module(source).unwrap();
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert!(report.is_ok(), "{report}");
        let aliases = source.replace(
            "v0.objref<@E> = obj.alloc @E;",
            "v0.objref<@E> = extract_value v100 1.i8;",
        );
        let parsed = parse_module(&aliases).unwrap();
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert!(report.has_errors(), "incoming fields can alias: {report}");
    }
}

#[test]
fn malformed_ssa_is_rejected_before_enum_dataflow_at_both_levels() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
func private %entry() -> i256 {
block0:
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v0.objref<@E> = obj.alloc @E;
 v2.i256 = obj.load v1;
 return v2;
}
"#;
    for level in [VerificationLevel::Standard, VerificationLevel::Full] {
        let parsed = parse_module(source).unwrap();
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert!(
            report
                .errors()
                .any(|diagnostic| diagnostic.code.as_str() == "IR0500"),
            "{report}"
        );
    }
}

#[test]
fn scalar_interface_loads_can_initialize_enum_fields() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
func private %entry(v100.objref<i256>) -> i256 {
block0:
 v0.i256 = obj.load v100;
 v1.objref<@E> = obj.alloc @E;
 enum.write_variant v1 #Some (v0);
 v2.objref<i256> = enum.proj v1 #Some 0.i8;
 v3.i256 = obj.load v2;
 return v3;
}
"#;
    assert_eq!(execute(source, 128).invalid_reads(), 0);
}

#[test]
fn call_modified_reference_cells_preserve_possible_enum_obligations() {
    for guarded in [false, true] {
        let setup = if guarded {
            "v0.objref<@E> = obj.alloc @E;\n enum.write_variant v0 #Some (17.i256);\n v1.objref<i256> = enum.proj v0 #Some 0.i8;"
        } else {
            "v0.objref<@Pair> = obj.alloc @Pair;\n v1.objref<i256> = obj.proj v0 0.i8;\n obj.store v1 17.i256;"
        };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
type @Pair = {{ i256 }};
type @Holder = {{ objref<i256> }};
func private %change(v100.objref<@Holder>, v101.objref<i256>) {{
block0:
 v0.objref<objref<i256>> = obj.proj v100 0.i8;
 obj.store v0 v101;
 return;
}}
func private %entry() -> i256 {{
block0:
 {setup}
 v2.objref<@Holder> = obj.alloc @Holder;
 v3.objref<objref<i256>> = obj.proj v2 0.i8;
 obj.store v3 v1;
 call %change v2 v1;
 v4.objref<i256> = obj.load v3;
 v5.i256 = obj.load v4;
 return v5;
}}
"#
        );
        for level in [VerificationLevel::Standard, VerificationLevel::Full] {
            let parsed = parse_module(&source).unwrap();
            let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
            // Calls invalidate mutable guarantees; the guarded candidate needs
            // a new caller-side proof even if this particular callee is benign.
            assert_eq!(report.has_errors(), guarded, "{source}\n{report}");
        }
    }
}

#[test]
fn projections_preceding_a_phi_target_write_observe_its_postcondition() {
    for write in [
        "enum.write_variant v2 #Some (31.i256);",
        "enum.set_tag v2 #Some;\n obj.store v3 31.i256;",
    ] {
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry(v100.i1) -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.set_tag v0 #None;
 v1.objref<@E> = obj.alloc @E;
 enum.set_tag v1 #None;
 br v100 block1 block2;
block1:
 jump block3;
block2:
 jump block3;
block3:
 v2.objref<@E> = phi (v0 block1) (v1 block2);
 v3.objref<i256> = enum.proj v2 #Some 0.i8;
 {write}
 v4.i256 = obj.load v3;
 return v4;
}}
"#
        );
        assert_eq!(execute(&source, 128).invalid_reads(), 0);
    }
}

#[test]
fn simultaneous_object_and_payload_phis_keep_their_relationship() {
    for retag in [false, true] {
        let mutation = if retag { "enum.set_tag v4 #None;" } else { "" };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry() -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.set_tag v0 #None;
 v1.objref<@E> = obj.alloc @E;
 enum.set_tag v1 #None;
 v2.objref<i256> = enum.proj v0 #Some 0.i8;
 v3.objref<i256> = enum.proj v1 #Some 0.i8;
 jump block1;
block1:
 v4.objref<@E> = phi (v0 block0) (v1 block2);
 v5.objref<i256> = phi (v2 block0) (v3 block2);
 v6.i8 = phi (0.i8 block0) (v7 block2);
 enum.write_variant v4 #Some (31.i256);
 {mutation}
 v8.i256 = obj.load v5;
 v7.i8 = add v6 1.i8;
 v9.i1 = lt v7 2.i8;
 br v9 block2 block3;
block2:
 jump block1;
block3:
 return v8;
}}
"#
        );
        assert_eq!(execute(&source, 128).invalid_reads(), usize::from(retag));
    }
}

#[test]
fn calls_do_not_reclassify_unresolved_local_references_as_imports() {
    let source = r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
func private %identity(v100.objref<i256>) -> objref<i256> {
block0:
 return v100;
}
func private %entry() -> i256 {
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.set_tag v0 #Some;
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 v2.objref<i256> = call %identity undef.objref<i256>;
 v3.objref<@E> = enum.assert_variant_ref v0 #Some;
 v4.i256 = obj.load v2;
 return v4;
}
"#;
    for level in [VerificationLevel::Standard, VerificationLevel::Full] {
        let parsed = parse_module(source).unwrap();
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert!(
            report
                .errors()
                .any(|diagnostic| diagnostic.message == "unknown local reference provenance"),
            "{report}"
        );
        let known = source.replace("call %identity undef.objref<i256>", "call %identity v1");
        let parsed = parse_module(&known).unwrap();
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert!(report.is_ok(), "{report}");
    }
}
