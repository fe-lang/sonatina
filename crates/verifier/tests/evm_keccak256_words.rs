use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

#[test]
fn keccak256_words_hashes_i256_words_to_an_i256() {
    for (arg, result, ok) in [
        ("i256", "i256", true),
        ("i8", "i256", false),
        ("*i256", "i256", false),
        ("i256", "i8", false),
    ] {
        let source = format!(
            "target = \"evm-ethereum-osaka\"\nfunc public %hash(v0.{arg}) -> {result} {{\nblock0:\n v1.{result} = evm_keccak256_words 1.i256 v0;\n return v1;\n}}"
        );
        let parsed = parse_module(&source).unwrap();
        let report = verify_module(
            &parsed.module,
            &VerifierConfig::for_level(VerificationLevel::Full),
        );
        assert_eq!(report.is_ok(), ok, "{arg} -> {result}: {report}");
    }
}
