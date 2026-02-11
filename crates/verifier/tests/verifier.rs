use sonatina_ir::{InstDowncastMut, Type, ValueId, inst::arith::Add};
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

fn has_code(report: &sonatina_verifier::VerificationReport, code: &str) -> bool {
    report
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code.as_str() == code)
}

fn diagnostic_fingerprint(report: &sonatina_verifier::VerificationReport) -> Vec<String> {
    report
        .diagnostics
        .iter()
        .map(|diagnostic| {
            let notes = diagnostic
                .notes
                .iter()
                .map(|note| note.message.as_str())
                .collect::<Vec<_>>()
                .join("|");
            format!(
                "{}|{}|{}|{}",
                diagnostic.code.as_str(),
                diagnostic.primary,
                diagnostic.message,
                notes
            )
        })
        .collect()
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

#[test]
fn interpreter_gep_fixture_verifies() {
    let src = include_str!("../../interpreter/test_files/gep.sntn");

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn gep_type_computation_matches_codegen_semantics() {
    let src = r#"
target = "evm-ethereum-london"

type @s = {i32, i64};

func public %ptr_scalar(v0.*i32) -> *i32 {
    block0:
        v1.*i32 = gep v0 3.i32;
        return v1;
}

func public %ptr_struct(v0.*@s) -> *i64 {
    block0:
        v1.*i64 = gep v0 0.i32 1.i32;
        return v1;
}

func public %ptr_array(v0.*[i16; 4]) -> *i16 {
    block0:
        v1.*i16 = gep v0 0.i32 2.i32;
        return v1;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn gep_missing_leading_zero_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

type @s = {i32, i64};

func public %bad_gep(v0.*@s) -> *i64 {
    block0:
        v1.*i64 = gep v0 1.i32;
        return v1;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn negative_aggregate_indices_are_rejected() {
    let src = r#"
target = "evm-ethereum-london"

type @s = {i32, i64};

func public %bad_gep(v0.*@s) -> unit {
    block0:
        v1.*i64 = gep v0 0.i32 -1.i32;
        return;
}

func public %bad_insert() -> unit {
    block0:
        v0.@s = insert_value undef.@s -1.i32 1.i32;
        return;
}

func public %bad_extract() -> unit {
    block0:
        v0.i32 = extract_value undef.@s -1.i32;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0606"), "expected IR0606, got {report}");
    assert!(has_code(&report, "IR0608"), "expected IR0608, got {report}");
    assert!(has_code(&report, "IR0607"), "expected IR0607, got {report}");
}

#[test]
fn function_pointer_types_and_get_function_ptr_verify() {
    let src = r#"
target = "evm-ethereum-london"

func public %callee(v0.i32) -> i32 {
    block0:
        return v0;
}

func public %caller(v0.*(i32, i32) -> i32) -> unit {
    block0:
        v1.*(i32) -> i32 = get_function_ptr %callee;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn shift_operand_width_mismatch_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_shift() -> i32 {
    block0:
        v0.i32 = shl 1.i8 1.i32;
        return v0;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0600"), "expected IR0600, got {report}");
}

#[test]
fn by_value_recursive_types_are_rejected_without_layout_recursion() {
    let src = r#"
target = "evm-ethereum-london"

type @node = {i32};

func public %ok() -> unit {
    block0:
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;

    module.ctx.with_ty_store_mut(|store| {
        let node_ref = store.lookup_struct("node").expect("node type must exist");
        let node_ty = Type::Compound(node_ref);
        store.update_struct_fields("node", &[node_ty]);
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&module, &cfg);

    assert!(has_code(&report, "IR0004"), "expected IR0004, got {report}");
}

#[test]
fn cache_diagnostics_order_is_deterministic() {
    let src = r#"
target = "evm-ethereum-london"

global private i32 $G0 = 0;
global private i32 $G1 = 1;

func public %cache() -> i32 {
    block0:
        v0.i32 = add 10.i32 20.i32;
        v1.i32 = ptr_to_int $G0 i32;
        v2.i32 = ptr_to_int $G1 i32;
        v3.i32 = add v0 v1;
        v4.i32 = add v3 v2;
        return v4;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];

    module.func_store.modify(func_ref, |func| {
        let imm10 = 10i32.into();
        let imm20 = 20i32.into();
        let val10 = *func
            .dfg
            .immediates
            .get(&imm10)
            .expect("10 immediate value must exist");
        let val20 = *func
            .dfg
            .immediates
            .get(&imm20)
            .expect("20 immediate value must exist");
        func.dfg.immediates.insert(imm10, val20);
        func.dfg.immediates.insert(imm20, val10);
        let missing_value = ValueId::from_u32(func.dfg.values.len() as u32 + 1000);
        func.dfg.immediates.insert(123i32.into(), missing_value);

        let mut globals: Vec<_> = func
            .dfg
            .globals
            .iter()
            .map(|(gv, value_id)| (*gv, *value_id))
            .collect();
        globals.sort_by_key(|(gv, _)| gv.as_u32());
        let (gv0, val0) = globals[0];
        let (gv1, val1) = globals[1];
        func.dfg.globals.insert(gv0, val1);
        func.dfg.globals.insert(gv1, val0);
        let missing_global = sonatina_ir::GlobalVariableRef::from_u32(900_000);
        let missing_global_value = ValueId::from_u32(func.dfg.values.len() as u32 + 1001);
        func.dfg
            .globals
            .insert(missing_global, missing_global_value);
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report1 = verify_module(&module, &cfg);
    let report2 = verify_module(&module, &cfg);

    assert!(
        has_code(&report1, "IR0702"),
        "expected IR0702, got {report1}"
    );
    assert!(
        has_code(&report1, "IR0703"),
        "expected IR0703, got {report1}"
    );
    assert_eq!(
        diagnostic_fingerprint(&report1),
        diagnostic_fingerprint(&report2),
        "diagnostic ordering should be deterministic"
    );
}

#[test]
fn object_data_directive_rejects_non_const_global() {
    let src = r#"
target = "evm-ethereum-london"

global private i32 $G = 1;

func public %entry() -> unit {
    block0:
        return;
}

object @Contract {
  section runtime {
    entry %entry;
    data $G;
  }
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0611"), "expected IR0611, got {report}");
}

#[test]
fn object_data_directive_requires_initializer() {
    let src = r#"
target = "evm-ethereum-london"

global private const i32 $G;

func public %entry() -> unit {
    block0:
        return;
}

object @Contract {
  section runtime {
    entry %entry;
    data $G;
  }
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0611"), "expected IR0611, got {report}");
}

#[test]
fn object_data_directive_rejects_pointer_type() {
    let src = r#"
target = "evm-ethereum-london"

global private const *i32 $G = 0;

func public %entry() -> unit {
    block0:
        return;
}

object @Contract {
  section runtime {
    entry %entry;
    data $G;
  }
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0611"), "expected IR0611, got {report}");
}

#[test]
fn embed_symbols_must_be_declared_in_same_section() {
    let src = r#"
target = "evm-ethereum-london"

func public %init() -> unit {
    block0:
        v0.i256 = sym_addr &runtime;
        return;
}

func public %runtime() -> unit {
    block0:
        return;
}

object @Contract {
  section init {
    entry %init;
  }
  section runtime {
    entry %runtime;
    embed .init as &runtime;
  }
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0611"), "expected IR0611, got {report}");
}

#[test]
fn embed_symbols_declared_in_same_section_are_accepted() {
    let src = r#"
target = "evm-ethereum-london"

func public %entry() -> unit {
    block0:
        return;
}

func public %init() -> unit {
    block0:
        v0.i256 = sym_addr &runtime;
        v1.i256 = sym_size &runtime;
        return;
}

object @Contract {
  section init {
    entry %init;
    embed .runtime as &runtime;
  }
  section runtime {
    entry %entry;
  }
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn by_value_function_type_in_signature_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

declare external %bad((i32) -> i32) -> unit;
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0610"), "expected IR0610, got {report}");
}

#[test]
fn invalid_declared_signature_type_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

type @node = {i32};
declare external %takes(@node) -> unit;
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;

    module.ctx.with_ty_store_mut(|store| {
        let node_ref = store.lookup_struct("node").expect("node type must exist");
        let node_ty = Type::Compound(node_ref);
        store.update_struct_fields("node", &[node_ty]);
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&module, &cfg);

    assert!(has_code(&report, "IR0004"), "expected IR0004, got {report}");
}

#[test]
fn detached_dfg_block_is_reported_when_disallowed() {
    let src = r#"
target = "evm-ethereum-london"

func public %entry() -> unit {
    block0:
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];
    module.func_store.modify(func_ref, |func| {
        let _ = func.dfg.make_block();
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&module, &cfg);

    assert!(has_code(&report, "IR0103"), "expected IR0103, got {report}");
}

#[test]
fn detached_dfg_block_is_allowed_when_enabled() {
    let src = r#"
target = "evm-ethereum-london"

func public %entry() -> unit {
    block0:
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];
    module.func_store.modify(func_ref, |func| {
        let _ = func.dfg.make_block();
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Fast);
    let report = verify_module(&module, &cfg);

    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}
