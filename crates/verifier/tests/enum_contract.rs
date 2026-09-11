//! Executable specification for the enum verifier replacement.
//!
//! These first-stage tests validate the independent execution oracle and fixture
//! expectations. The production comparison becomes a required gate at cutover;
//! the current verifier still has the documented acceptance/rejection defects.
#[path = "support/enum_concrete.rs"]
mod concrete;

use concrete::execute;

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
