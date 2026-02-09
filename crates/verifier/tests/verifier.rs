use sonatina_ir::{InstDowncastMut, inst::arith::Add};
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

fn has_code(report: &sonatina_verifier::VerificationReport, code: &str) -> bool {
    report
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code.as_str() == code)
}

#[test]
fn valid_module_is_ok() {
    let src = r#"
target = "evm-ethereum-london"

func public %ok(v0.i32) -> i32 {
    block0:
        v1.i32 = add v0 1.i32;
        return v1;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn missing_terminator_is_reported() {
    let src = r#"
target = "evm-ethereum-london"

func public %missing_term() -> unit {
    block0:
        v0.i32 = add 1.i32 2.i32;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0201"), "expected IR0201, got {report}");
}

#[test]
fn branch_condition_type_is_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_br() -> unit {
    block0:
        br 1.i32 block1 block1;

    block1:
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0600"), "expected IR0600, got {report}");
}

#[test]
fn call_arity_is_checked() {
    let src = r#"
target = "evm-ethereum-london"

declare external %callee(i32, i32) -> i32;

func public %caller() -> unit {
    block0:
        v0.i32 = call %callee 1.i32;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0603"), "expected IR0603, got {report}");
}

#[test]
fn phi_position_is_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_phi(v0.i1, v1.i32) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v2.i32 = add v1 1.i32;
        v3.i32 = phi (v1 block1) (v1 block2);
        return v3;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0400"), "expected IR0400, got {report}");
}

#[test]
fn users_mismatch_is_reported() {
    let src = r#"
target = "evm-ethereum-london"

func public %users() -> i32 {
    block0:
        v0.i32 = add 1.i32 2.i32;
        return v0;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];

    module.func_store.modify(func_ref, |func| {
        let block = func.layout.entry_block().expect("entry block must exist");
        let inst = func
            .layout
            .first_inst_of(block)
            .expect("first instruction must exist");

        let replacement = func.dfg.make_imm_value(99i32);
        let inst_set = func.inst_set();
        let inst_data = func.dfg.inst_mut(inst);
        let add = <&mut Add as InstDowncastMut>::downcast_mut(inst_set, inst_data)
            .expect("first instruction should be add");
        *add.lhs_mut() = replacement;
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&module, &cfg);

    assert!(has_code(&report, "IR0700"), "expected IR0700, got {report}");
}

#[test]
fn non_terminator_at_end_is_reported() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_tail() -> unit {
    block0:
        jump block1;
        v0.i32 = add 1.i32 2.i32;

    block1:
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0203"), "expected IR0203, got {report}");
}

#[test]
fn zero_max_diagnostics_keeps_reporting() {
    let src = r#"
target = "evm-ethereum-london"

func public %missing_term() -> unit {
    block0:
        v0.i32 = add 1.i32 2.i32;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let mut cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    cfg.max_diagnostics = 0;
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        !report.diagnostics.is_empty(),
        "expected diagnostics with max=0"
    );
    assert!(has_code(&report, "IR0201"), "expected IR0201, got {report}");
}
