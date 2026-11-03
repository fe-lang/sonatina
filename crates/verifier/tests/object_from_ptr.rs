use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

fn report(body: &str) -> sonatina_verifier::VerificationReport {
    let source = format!(
        "target = \"evm-ethereum-osaka\"\ntype @E = enum {{ #None, #Some(i256) }};\ntype @Pair = {{ i256, i8 }};\n{body}"
    );
    let parsed = parse_module(&source).unwrap();
    verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Full),
    )
}

#[test]
fn views_take_the_pointee_type() {
    assert!(
        report(
            r#"
func private %f(v0.*@Pair) -> i8 {
block0:
 v1.objref<@Pair> = obj.from_ptr v0;
 v2.objref<i8> = obj.proj v1 1.i8;
 v3.i8 = obj.load v2;
 return v3;
}
"#
        )
        .is_ok()
    );
    for (operand, result, message) in [
        (
            "i256",
            "objref<i256>",
            "obj.from_ptr operand must be a raw pointer",
        ),
        (
            "*@Pair",
            "objref<i256>",
            "obj.from_ptr result must be an object reference to the pointee type",
        ),
        (
            "*@Pair",
            "*@Pair",
            "obj.from_ptr result must be an object reference to the pointee type",
        ),
    ] {
        let report = report(&format!(
            "func private %f(v0.{operand}) {{\nblock0:\n v1.{result} = obj.from_ptr v0;\n return;\n}}"
        ));
        assert!(
            report
                .errors()
                .any(|diagnostic| diagnostic.message == message),
            "{operand} -> {result}: {report}"
        );
    }
}

#[test]
fn enum_payloads_of_views_need_variant_proofs() {
    // A view of memory has an unknown variant, like an object argument's.
    for (object, view) in [
        ("v0.objref<@E>", ""),
        ("v9.*@E", "v0.objref<@E> = obj.from_ptr v9;"),
    ] {
        for assert in [false, true] {
            let payload = if assert {
                "v1.objref<@E> = enum.assert_variant_ref v0 #Some;\n v2.objref<i256> = enum.proj v1 #Some 0.i8;"
            } else {
                "v2.objref<i256> = enum.proj v0 #Some 0.i8;"
            };
            let report = report(&format!(
                "func private %f({object}) -> i256 {{\nblock0:\n {view}\n {payload}\n v3.i256 = obj.load v2;\n return v3;\n}}"
            ));
            assert_eq!(
                report.is_ok(),
                assert,
                "{object}, assert {assert}: {report}"
            );
        }
    }
}

// A view of raw memory may alias any accessible payload of its type. A local
// object's payloads keep their guards, since only exposure gives them a raw
// address. Other objects' are imported memory to the view, as they are to a
// callee given the same pointer, even after this function changes their tag.
#[test]
fn views_take_guards_only_from_local_payloads() {
    for (setup, valid) in [
        ("", true),
        (
            "v1.objref<@E> = obj.from_ptr v8;\n enum.set_tag v1 #None;",
            true,
        ),
        ("enum.set_tag v0 #None;", true),
        (
            "v1.objref<@E> = obj.alloc @E;\n enum.write_variant v1 #Some (17.i256);\n v2.*@E = obj.materialize.stack v1;",
            true,
        ),
        (
            "v1.objref<@E> = obj.alloc @E;\n enum.write_variant v1 #Some (17.i256);\n v2.*@E = obj.materialize.stack v1;\n enum.set_tag v1 #None;",
            false,
        ),
    ] {
        let report = report(&format!(
            "func private %f(v0.objref<@E>, v8.*@E, v9.*i256) -> i256 {{\nblock0:\n {setup}\n v3.objref<i256> = obj.from_ptr v9;\n v4.i256 = obj.load v3;\n return v4;\n}}"
        ));
        assert_eq!(report.is_ok(), valid, "{setup}: {report}");
    }
}
