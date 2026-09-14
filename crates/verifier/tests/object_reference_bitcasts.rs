use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

const TYPES: &str = r#"
type @Box = { objref<i256> };
type @Nested = { [@Box; 1] };
type @Carrier = enum { #Wrap(@Nested) };
type @Recursive = { objref<@Recursive> };
type @Pointers = { *objref<i256> };
"#;

#[test]
fn bitcasts_cannot_hide_object_references_inside_values() {
    for (object, bits) in [
        ("objref<i256>", "*i256"),
        ("@Box", "*i256"),
        ("[objref<i256>; 1]", "i256"),
        ("@Nested", "i256"),
        ("@Carrier", "[i256; 2]"),
        ("@Recursive", "i256"),
        ("@Box", "@Box"),
        ("[objref<i256>; 0]", "[i256; 0]"),
        ("[objref<i256>; 1000000000]", "[i256; 1000000000]"),
    ] {
        for (from, to) in [(object, bits), (bits, object)] {
            let source = format!(
                "target = \"evm-ethereum-osaka\"\n{TYPES}\nfunc private %cast(v0.{from}) -> {to} {{\nblock0:\n v1.{to} = bitcast v0 {to};\n return v1;\n}}"
            );
            let parsed = parse_module(&source).unwrap();
            for level in [VerificationLevel::Standard, VerificationLevel::Full] {
                let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
                assert!(
                    report.errors().any(|diagnostic| diagnostic.message
                        == "bitcast does not allow object-reference types"),
                    "{level:?}: {source}\n{report}"
                );
            }
        }
    }
}

#[test]
fn bitcasts_of_scalars_and_raw_pointers_remain_valid() {
    for (from, to) in [
        ("i256", "*i256"),
        ("*objref<i256>", "*i256"),
        ("@Pointers", "*i256"),
        ("[i256; 1]", "i256"),
        ("[i256; 0]", "[i8; 0]"),
    ] {
        for (from, to) in [(from, to), (to, from)] {
            let source = format!(
                "target = \"evm-ethereum-osaka\"\n{TYPES}\nfunc private %cast(v0.{from}) -> {to} {{\nblock0:\n v1.{to} = bitcast v0 {to};\n return v1;\n}}"
            );
            let parsed = parse_module(&source).unwrap();
            for level in [VerificationLevel::Standard, VerificationLevel::Full] {
                let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
                assert!(report.is_ok(), "{level:?}: {source}\n{report}");
            }
        }
    }
}

#[test]
fn invalid_recursive_cast_types_receive_diagnostics() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Cycle = { @Cycle };
func private %cast(v0.@Cycle) -> i256 {
block0:
 v1.i256 = bitcast v0 i256;
 return v1;
}
"#;
    let parsed = parse_module(source).unwrap();
    for level in [VerificationLevel::Standard, VerificationLevel::Full] {
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert!(report.has_errors(), "{level:?}: {report}");
    }
}

#[test]
fn an_aggregate_cast_cannot_create_a_raw_alias_to_a_private_enum() {
    let source = include_str!("fixtures/invalid_object_reference_bitcast.sntn");
    let parsed = parse_module(source).unwrap();
    for level in [VerificationLevel::Standard, VerificationLevel::Full] {
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert!(
            report
                .errors()
                .any(|diagnostic| diagnostic.message
                    == "bitcast does not allow object-reference types"),
            "{level:?}: {report}"
        );
    }
}
