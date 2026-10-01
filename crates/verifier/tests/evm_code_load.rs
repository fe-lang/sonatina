use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

#[test]
fn code_load_requires_a_full_word_result() {
    for ty in ["i256", "i8", "*i256"] {
        let source = format!(
            "target = \"evm-ethereum-osaka\"\nfunc public %read() -> {ty} {{\nblock0:\n v0.{ty} = evm_code_load 0.i256;\n return v0;\n}}"
        );
        let parsed = parse_module(&source).unwrap();
        let report = verify_module(
            &parsed.module,
            &VerifierConfig::for_level(VerificationLevel::Full),
        );
        assert_eq!(report.is_ok(), ty == "i256", "{ty}: {report}");
    }
}
