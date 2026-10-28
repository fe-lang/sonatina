use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

#[test]
fn memory_copies_take_addresses_and_an_integral_length() {
    for (dest, src, len, valid) in [
        ("*i8", "*i8", "i64", true),
        ("i64", "i64", "i64", true),
        ("i1", "*i8", "i64", true),
        ("[i64; 2]", "*i8", "i64", false),
        ("*i8", "[i64; 2]", "i64", false),
        ("*i8", "*i8", "*i8", false),
    ] {
        let source = format!(
            "target = \"x86_64-unknown-native\"\nfunc public %copy(v0.{dest}, v1.{src}, v2.{len}) {{\nblock0:\n    memcopy v0 v1 v2;\n    return;\n}}"
        );
        let parsed = parse_module(&source).unwrap();
        let report = verify_module(
            &parsed.module,
            &VerifierConfig::for_level(VerificationLevel::Full),
        );
        assert_eq!(report.is_ok(), valid, "{dest} {src} {len}: {report}");
    }
}
