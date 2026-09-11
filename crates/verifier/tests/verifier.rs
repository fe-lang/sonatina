use sonatina_ir::{
    InstDowncastMut, Linkage, Signature, Type, Value, ValueId,
    builder::ModuleBuilder,
    inst::{arith::Add, control_flow::BrTable, data::Gep},
    isa::evm::Evm,
    module::ModuleCtx,
    types::CompoundTypeRef,
};
use sonatina_parser::parse_module;
use sonatina_triple::TargetTriple;
use sonatina_verifier::{
    ModuleBuilderVerifyExt, ParseVerifyError, VerificationLevel, VerifierConfig, build_and_verify,
    parse_and_verify_module, verify_module, verify_module_invariants,
};

fn has_code(report: &sonatina_verifier::VerificationReport, code: &str) -> bool {
    report
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.code.as_str() == code)
}

fn has_message(report: &sonatina_verifier::VerificationReport, message: &str) -> bool {
    report
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.message == message)
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

fn next_missing_compound_ref(module: &sonatina_ir::Module) -> CompoundTypeRef {
    module.ctx.with_ty_store(|store| {
        let next_ref = store
            .all_compound_refs()
            .map(|cmpd_ref| cmpd_ref.as_u32())
            .max()
            .expect("at least one compound type must exist")
            + 1;
        CompoundTypeRef::from_u32(next_ref)
    })
}

#[test]
fn parse_and_verify_module_reports_parse_errors() {
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let err = match parse_and_verify_module("this is not valid sonatina ir", &cfg) {
        Ok(_) => panic!("invalid source should fail parse"),
        Err(err) => err,
    };
    assert!(matches!(err, ParseVerifyError::Parse(_)));
}

#[test]
fn parse_and_verify_module_reports_verification_errors() {
    let src = r#"
target = "evm-ethereum-london"

declare external %callee(i32, i32) -> i32;

func public %caller() -> unit {
    block0:
        v0.i32 = call %callee 1.i32;
        return;
}
"#;

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let err = match parse_and_verify_module(src, &cfg) {
        Ok(_) => panic!("source should fail verifier"),
        Err(err) => err,
    };
    let ParseVerifyError::Verify(report) = err else {
        panic!("expected verifier error");
    };
    assert!(has_code(&report, "IR0603"), "expected IR0603, got {report}");
}

#[test]
fn build_and_verify_reports_invalid_builder_module() {
    let triple = TargetTriple::parse("evm-ethereum-london").expect("valid target triple");
    let isa = Evm::new(triple);
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    builder
        .declare_function(Signature::new_unit("main", Linkage::Public, &[]))
        .expect("declaration should succeed");

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = match build_and_verify(builder, &cfg) {
        Ok(_) => panic!("module should fail verification"),
        Err(report) => report,
    };
    assert!(has_code(&report, "IR0105"), "expected IR0105, got {report}");
}

#[test]
fn build_verified_extension_accepts_valid_builder_module() {
    let triple = TargetTriple::parse("evm-ethereum-london").expect("valid target triple");
    let isa = Evm::new(triple);
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    builder
        .declare_function(Signature::new_single(
            "decl",
            Linkage::External,
            &[Type::I32],
            Type::I32,
        ))
        .expect("declaration should succeed");

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let module = builder
        .build_verified(&cfg)
        .expect("external declaration should verify");
    assert_eq!(module.funcs().len(), 1);
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
fn public_signature_with_enum_is_rejected() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func public %bad(v0.@OptionI256) -> @OptionI256 {
block0:
    return v0;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(
        has_code(&report, "IR0610"),
        "expected invalid signature, got {report}"
    );
}

#[test]
fn enum_extract_without_variant_proof_is_rejected() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad(v0.@OptionI256) -> i256 {
block0:
    v1.i256 = enum.extract v0 #Some 0.i8;
    return v1;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(
        has_code(&report, "IR0600"),
        "expected enum.extract verification failure, got {report}"
    );
}

#[test]
fn dominating_enum_assert_variant_proves_value_extract() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %ok(v0.@OptionI256, v1.i1) -> i256 {
block0:
    enum.assert_variant v0 #Some;
    br v1 block1 block2;

block1:
    v2.i256 = enum.extract v0 #Some 0.i8;
    return v2;

block2:
    return 0.i256;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn non_dominating_enum_assert_variant_does_not_prove_value_extract() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad(v0.@OptionI256, v1.i1) -> i256 {
block0:
    br v1 block1 block2;

block1:
    enum.assert_variant v0 #Some;
    jump block3;

block2:
    jump block3;

block3:
    v2.i256 = enum.extract v0 #Some 0.i8;
    return v2;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(
        has_code(&report, "IR0600"),
        "expected enum.extract verification failure without dominating proof, got {report}"
    );
}

#[test]
fn dominating_assert_for_other_variant_does_not_prove_value_extract() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad(v0.@OptionI256) -> i256 {
block0:
    enum.assert_variant v0 #None;
    jump block1;

block1:
    v1.i256 = enum.extract v0 #Some 0.i8;
    return v1;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(
        has_code(&report, "IR0600"),
        "expected enum.extract verification failure with wrong variant proof, got {report}"
    );
}

#[test]
fn dominating_assert_for_other_value_does_not_prove_value_extract() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad(v0.@OptionI256) -> i256 {
block0:
    v1.@OptionI256 = enum.make @OptionI256 #Some (1.i256);
    enum.assert_variant v1 #Some;
    jump block1;

block1:
    v2.i256 = enum.extract v0 #Some 0.i8;
    return v2;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(
        has_code(&report, "IR0600"),
        "expected enum.extract verification failure with wrong value proof, got {report}"
    );
}

#[test]
fn enum_assert_variant_ref_proves_object_field_load() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %ok(v0.objref<@OptionI256>) -> i256 {
block0:
    v1.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.i256 = obj.load v2;
    return v3;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn branch_proven_active_variant_does_not_imply_payload_init() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad() -> i256 {
block0:
    v0.objref<@OptionI256> = obj.alloc @OptionI256;
    enum.set_tag v0 #Some;
    v1.enumtag(@OptionI256) = enum.get_tag v0;
    br_table v1 block2 (1.enumtag(@OptionI256) block1) (0.enumtag(@OptionI256) block2);

block1:
    v2.objref<i256> = enum.proj v0 #Some 0.i8;
    v3.i256 = obj.load v2;
    return v3;

block2:
    return 0.i256;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(
        has_code(&report, "IR0600"),
        "expected enum payload load verification failure without payload store, got {report}"
    );
}

#[test]
fn branch_proven_variant_with_same_block_store_proves_object_field_load() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %ok(v0.objref<@OptionI256>, v1.i256) -> i256 {
block0:
    v2.enumtag(@OptionI256) = enum.get_tag v0;
    br_table v2 block2 (1.enumtag(@OptionI256) block1) (0.enumtag(@OptionI256) block2);

block1:
    v3.objref<i256> = enum.proj v0 #Some 0.i8;
    obj.store v3 v1;
    v4.i256 = obj.load v3;
    return v4;

block2:
    return 0.i256;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn enum_assert_variant_ref_is_invalidated_by_later_tag_write() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad(v0.objref<@OptionI256>) -> i256 {
block0:
    v1.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    enum.set_tag v0 #None;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.i256 = obj.load v2;
    return v3;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(
        has_code(&report, "IR0600"),
        "expected enum payload load verification failure after tag write, got {report}"
    );
}

#[test]
fn same_block_tag_write_and_field_store_prove_enum_field_load() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %ok(v0.objref<@OptionI256>, v1.i256) -> i256 {
block0:
    enum.set_tag v0 #Some;
    v2.objref<i256> = enum.proj v0 #Some 0.i8;
    obj.store v2 v1;
    v3.i256 = obj.load v2;
    return v3;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn enum_assert_variant_ref_is_invalidated_by_intervening_call() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %retag(v0.objref<@OptionI256>) -> unit {
block0:
    enum.set_tag v0 #None;
    return;
}

func private %bad(v0.objref<@OptionI256>) -> i256 {
block0:
    v1.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    call %retag v0;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.i256 = obj.load v2;
    return v3;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(
        has_code(&report, "IR0600"),
        "expected enum payload load verification failure after call barrier, got {report}"
    );
}

#[test]
fn multi_return_functions_and_calls_verify() {
    let src = r#"
target = "evm-ethereum-london"

func private %pair_add(v0.i32, v1.i32) -> (i32, i1) {
    block0:
        (v2.i32, v3.i1) = uaddo v0 v1;
        return (v2, v3);
}

func public %caller(v0.i32, v1.i32) -> (i32, i1) {
    block0:
        (v2.i32, v3.i1) = call %pair_add v0 v1;
        return (v2, v3);
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn multi_return_mismatches_are_reported() {
    let src = r#"
target = "evm-ethereum-london"

declare external %pair_add(i32, i32) -> (i32, i1);

func public %caller() -> i32 {
    block0:
        v0.i32 = call %pair_add 1.i32 2.i32;
        return v0;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn multi_return_call_result_type_mismatch_is_reported() {
    let src = r#"
target = "evm-ethereum-london"

declare external %pair_add(i32, i32) -> (i32, i1);

func public %caller() -> unit {
    block0:
        (v0.i1, v1.i32) = call %pair_add 1.i32 2.i32;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn multi_return_value_mismatches_are_reported() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_arity() -> (i32, i1) {
    block0:
        return 0.i32;
}

func public %bad_type() -> (i32, i1) {
    block0:
        return (0.i1, 0.i1);
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0604"), "expected IR0604, got {report}");
}

#[test]
fn private_objref_helpers_verify() {
    let src = r#"
target = "evm-ethereum-london"

type @pair = { i256, i256 };

func private %make_pair(v0.i256, v1.i256) -> objref<@pair> {
    block0:
        v2.objref<@pair> = obj.alloc @pair;
        v3.objref<i256> = obj.proj v2 0.i8;
        obj.store v3 v0;
        v4.objref<i256> = obj.proj v2 1.i8;
        obj.store v4 v1;
        return v2;
}

func private %sum_pair(v0.objref<@pair>) -> i256 {
    block0:
        v1.objref<i256> = obj.proj v0 0.i8;
        v2.i256 = obj.load v1;
        v3.objref<i256> = obj.proj v0 1.i8;
        v4.i256 = obj.load v3;
        v5.i256 = add v2 v4;
        return v5;
}

func public %entry(v0.i256, v1.i256) -> i256 {
    block0:
        v2.objref<@pair> = call %make_pair v0 v1;
        v3.i256 = call %sum_pair v2;
        return v3;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(report.is_ok(), "expected no verifier errors, got {report}");
}

#[test]
fn obj_init_const_rejects_pointer_payloads() {
    let src = r#"
target = "evm-ethereum-london"

func private %bad(v0.objref<*i256>, v1.constref<*i256>) -> unit {
    block0:
        obj.init.const v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0600"), "expected IR0600, got {report}");
    assert!(
        has_message(
            &report,
            "obj.init.const does not support pointer-typed const data"
        ),
        "expected pointer payload diagnostic, got {report}"
    );
}

#[test]
fn obj_init_const_rejects_reference_payloads() {
    let src = r#"
target = "evm-ethereum-london"

func private %bad(v0.objref<objref<i256>>, v1.constref<objref<i256>>) -> unit {
    block0:
        obj.init.const v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0600"), "expected IR0600, got {report}");
    assert!(
        has_message(
            &report,
            "obj.init.const does not support reference or enum-tag const data"
        ),
        "expected reference payload diagnostic, got {report}"
    );
}

#[test]
fn obj_init_const_rejects_enum_tag_payloads() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad(v0.objref<enumtag(@OptionI256)>, v1.constref<enumtag(@OptionI256)>) -> unit {
    block0:
        obj.init.const v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0600"), "expected IR0600, got {report}");
    assert!(
        has_message(
            &report,
            "obj.init.const does not support reference or enum-tag const data"
        ),
        "expected enum-tag payload diagnostic, got {report}"
    );
}

#[test]
fn public_objref_signature_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

type @pair = { i256, i256 };

func public %entry(v0.objref<@pair>) -> i256 {
    block0:
        v1.objref<i256> = obj.proj v0 0.i8;
        v2.i256 = obj.load v1;
        return v2;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        report.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("must not expose object references")),
        "expected objref signature rejection, got {report}"
    );
}

#[test]
fn private_section_entry_objref_signature_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

type @pair = { i256, i256 };

func private %entry(v0.objref<@pair>) -> i256 {
    block0:
        v1.objref<i256> = obj.proj v0 0.i8;
        v2.i256 = obj.load v1;
        return v2;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        report.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("section entry signatures must not expose object references")),
        "expected section-entry objref rejection, got {report}"
    );
}

#[test]
fn declaration_only_section_entry_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

declare external %entry();

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        report.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("section entry must reference a defined function body")),
        "expected declaration-only section entry rejection, got {report}"
    );
}

#[test]
fn bitcast_objref_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

type @pair = { i256, i256 };

func private %f(v0.objref<@pair>) -> *@pair {
    block0:
        v1.*@pair = bitcast v0 *@pair;
        return v1;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        report.diagnostics.iter().any(|diagnostic| diagnostic
            .message
            .contains("bitcast does not allow object-reference types")),
        "expected objref bitcast rejection, got {report}"
    );
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
fn cmp_result_type_is_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_cmp_result() -> unit {
    block0:
        v0.i256 = lt 1.i256 2.i256;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn uaddo_result_types_are_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_uaddo(v0.i32, v1.i32) -> unit {
    block0:
        (v2.i32, v3.i32) = uaddo v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn other_overflow_ops_result_types_are_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_ssubo(v0.i32, v1.i32) -> unit {
    block0:
        (v2.i32, v3.i32) = ssubo v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn saturating_result_types_are_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_uaddsat(v0.i32, v1.i32) -> unit {
    block0:
        v2.i1 = uaddsat v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn saturating_ops_reject_i1_operands() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_i1(v0.i1, v1.i1) -> unit {
    block0:
        v2.i1 = uaddsat v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0600"), "expected IR0600, got {report}");
}

#[test]
fn evm_checked_divmod_result_types_are_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_evm_sdivo(v0.i32, v1.i32) -> unit {
    block0:
        (v2.i32, v3.i32) = evm_sdivo v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn evm_saturating_ops_reject_i256_width_type() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_evm_uaddsat(v0.i256, v1.i256) -> unit {
    block0:
        v2.i256 = evm_uaddsat v0 v1 i256;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0600"), "expected IR0600, got {report}");
}

#[test]
fn uaddo_missing_results_are_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_uaddo(v0.i32, v1.i32) -> unit {
    block0:
        uaddo v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn uaddo_extra_results_are_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_uaddo(v0.i32, v1.i32) -> unit {
    block0:
        (v2.i32, v3.i1, v4.i1) = uaddo v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn multi_result_metadata_mismatch_is_reported() {
    let src = r#"
target = "evm-ethereum-london"

func public %ok_uaddo(v0.i32, v1.i32) -> unit {
    block0:
        (v2.i32, v3.i1) = uaddo v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];

    module.func_store.modify(func_ref, |func| {
        let entry = func.layout.entry_block().expect("entry block must exist");
        let inst = func
            .layout
            .first_inst_of(entry)
            .expect("uaddo must be first inst");
        let results = func.dfg.inst_results(inst).to_vec();
        let bad = results[1];
        let Value::Inst { result_idx, .. } = &mut func.dfg.values[bad] else {
            panic!("expected instruction result");
        };
        *result_idx = 0;
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&module, &cfg);

    assert!(has_code(&report, "IR0701"), "expected IR0701, got {report}");
}

#[test]
fn multi_result_metadata_mismatch_is_reported_in_fast_mode() {
    let src = r#"
target = "evm-ethereum-london"

func public %ok_uaddo(v0.i32, v1.i32) -> unit {
    block0:
        (v2.i32, v3.i1) = uaddo v0 v1;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];

    module.func_store.modify(func_ref, |func| {
        let entry = func.layout.entry_block().expect("entry block must exist");
        let inst = func
            .layout
            .first_inst_of(entry)
            .expect("uaddo must be first inst");
        let results = func.dfg.inst_results(inst).to_vec();
        let bad = results[1];
        let Value::Inst { result_idx, .. } = &mut func.dfg.values[bad] else {
            panic!("expected instruction result");
        };
        *result_idx = 0;
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Fast);
    let report = verify_module(&module, &cfg);

    assert!(has_code(&report, "IR0701"), "expected IR0701, got {report}");
}

#[test]
fn branch_table_without_destinations_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_brt(v0.i32) -> unit {
    block0:
        br_table v0 block1;

    block1:
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];

    module.func_store.modify(func_ref, |func| {
        let entry = func.layout.entry_block().expect("entry block must exist");
        let term = func
            .layout
            .last_inst_of(entry)
            .expect("entry terminator must exist");
        let inst_set = func.inst_set();
        let inst = func.dfg.inst_mut(term);
        let br_table =
            <&mut BrTable as InstDowncastMut>::downcast_mut(inst_set, inst).expect("br_table");

        *br_table.default_mut() = None;
        br_table.table_mut().clear();
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&module, &cfg);

    assert!(has_code(&report, "IR0302"), "expected IR0302, got {report}");
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
fn declared_inst_arity_is_checked() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_gep(v0.*i32) -> *i32 {
    block0:
        v1.*i32 = gep v0 0.i32;
        return v1;
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
        let inst_set = func.inst_set();
        let inst_data = func.dfg.inst_mut(inst);
        let gep = <&mut Gep as InstDowncastMut>::downcast_mut(inst_set, inst_data).expect("gep");
        gep.values_mut().truncate(1);
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&module, &cfg);

    assert!(has_code(&report, "IR0600"), "expected IR0600, got {report}");
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
fn negative_const_and_object_indices_are_rejected() {
    let src = r#"
target = "evm-ethereum-london"

global private const [i32; 2] $arr = [1, 2];

func private %bad_const() -> unit {
    block0:
        v0.constref<[i32; 2]> = const.ref $arr;
        v1.constref<i32> = const.index v0 -1.i32;
        return;
}

func private %bad_obj() -> unit {
    block0:
        v0.objref<[i32; 2]> = obj.alloc [i32; 2];
        v1.objref<i32> = obj.index v0 -1.i32;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        has_message(&report, "const.index index must be non-negative"),
        "expected const.index negativity error, got {report}"
    );
    assert!(
        has_message(&report, "obj.index index must be non-negative"),
        "expected obj.index negativity error, got {report}"
    );
}

#[test]
fn constant_oob_const_and_object_indices_are_rejected() {
    let src = r#"
target = "evm-ethereum-london"

global private const [i32; 2] $arr = [1, 2];

func private %bad_const() -> unit {
    block0:
        v0.constref<[i32; 2]> = const.ref $arr;
        v1.constref<i32> = const.index v0 2.i32;
        return;
}

func private %bad_obj() -> unit {
    block0:
        v0.objref<[i32; 2]> = obj.alloc [i32; 2];
        v1.objref<i32> = obj.index v0 2.i32;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        has_message(&report, "const.index index is out of bounds"),
        "expected const.index bounds error, got {report}"
    );
    assert!(
        has_message(&report, "obj.index index is out of bounds"),
        "expected obj.index bounds error, got {report}"
    );
}

#[test]
fn array_projection_ops_are_rejected() {
    let src = r#"
target = "evm-ethereum-london"

global private const [i32; 2] $arr = [1, 2];

func private %bad_const() -> unit {
    block0:
        v0.constref<[i32; 2]> = const.ref $arr;
        v1.constref<i32> = const.proj v0 0.i32;
        return;
}

func private %bad_obj() -> unit {
    block0:
        v0.objref<[i32; 2]> = obj.alloc [i32; 2];
        v1.objref<i32> = obj.proj v0 0.i32;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        has_message(
            &report,
            "const.proj does not support array indexing; use const.index"
        ),
        "expected const.proj array rejection, got {report}"
    );
    assert!(
        has_message(
            &report,
            "obj.proj does not support array indexing; use obj.index"
        ),
        "expected obj.proj array rejection, got {report}"
    );
}

#[test]
fn oversized_positive_indices_are_rejected() {
    let src = r#"
target = "evm-ethereum-osaka"

type @s = {i32, i64};
type @OptionI32 = enum {
    #None,
    #Some(i32),
};

func private %bad_gep(v0.*@s) -> unit {
    block0:
        v1.*i64 = gep v0 0.i32 1606938044258990275541962092341162602522202993782792835301376.i256;
        return;
}

func private %bad_insert() -> unit {
    block0:
        v0.[i32; 2] = insert_value undef.[i32; 2] 1606938044258990275541962092341162602522202993782792835301376.i256 1.i32;
        return;
}

func private %bad_extract() -> unit {
    block0:
        v0.i32 = extract_value undef.[i32; 2] 1606938044258990275541962092341162602522202993782792835301376.i256;
        return;
}

func private %bad_proj(v0.objref<@s>) -> unit {
    block0:
        v1.objref<i64> = obj.proj v0 1606938044258990275541962092341162602522202993782792835301376.i256;
        return;
}

func private %bad_enum(v0.objref<@OptionI32>) -> unit {
    block0:
        v1.objref<@OptionI32> = enum.assert_variant_ref v0 #Some;
        v2.objref<i32> = enum.proj v1 #Some 1606938044258990275541962092341162602522202993782792835301376.i256;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        has_message(
            &report,
            "struct gep indices must be non-negative immediate values"
        ),
        "expected oversized gep rejection, got {report}"
    );
    assert!(
        has_message(&report, "aggregate index is out of bounds"),
        "expected oversized aggregate index rejection, got {report}"
    );
    assert!(
        has_message(
            &report,
            "obj.proj index must be a non-negative immediate value"
        ),
        "expected oversized obj.proj rejection, got {report}"
    );
    assert!(
        has_message(
            &report,
            "enum.proj field index is out of bounds for the selected variant"
        ),
        "expected oversized enum.proj rejection, got {report}"
    );
}

#[test]
fn dynamic_const_and_object_indices_still_verify() {
    let src = r#"
target = "evm-ethereum-london"

global private const [i32; 2] $arr = [1, 2];

func private %ok_const(v0.i32) -> i32 {
    block0:
        v1.constref<[i32; 2]> = const.ref $arr;
        v2.constref<i32> = const.index v1 v0;
        v3.i32 = const.load v2;
        return v3;
}

func private %ok_obj(v0.i32) -> unit {
    block0:
        v1.objref<[i32; 2]> = obj.alloc [i32; 2];
        v2.objref<i32> = obj.index v1 v0;
        obj.store v2 1.i32;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(
        report.is_ok(),
        "expected dynamic indices to verify, got {report}"
    );
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
fn function_pointer_return_type_list_mismatch_is_rejected() {
    let src = r#"
target = "evm-ethereum-london"

func public %callee(v0.i32) -> (i32, i1) {
    block0:
        return (v0, 0.i1);
}

func public %caller() -> unit {
    block0:
        v0.*(i32) -> i32 = get_function_ptr %callee;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
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
fn current_section_symbols_are_accepted_without_embed_declaration() {
    let src = r#"
target = "evm-ethereum-london"

func public %entry() -> unit {
    block0:
        v0.i256 = sym_addr .;
        v1.i256 = sym_size .;
        return;
}

object @Contract {
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
fn undeclared_embed_symbols_are_rejected_even_without_objects() {
    let src = r#"
target = "evm-ethereum-london"

func public %entry() -> unit {
    block0:
        v0.i256 = sym_addr &missing_embed;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0611"), "expected IR0611, got {report}");
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
fn dangling_enum_tag_in_public_signature_is_still_rejected() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

declare external %bad(enumtag(@OptionI256)) -> unit;
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];
    let missing_enum_ref = next_missing_compound_ref(&module);

    module.ctx.declared_funcs.insert(
        func_ref,
        Signature::new(
            "bad",
            Linkage::External,
            &[Type::EnumTag(missing_enum_ref)],
            &[],
        ),
    );

    let cfg = VerifierConfig::for_level(VerificationLevel::Full);
    let report = verify_module_invariants(&module, &cfg);

    assert!(has_code(&report, "IR0004"), "expected IR0004, got {report}");
    assert!(has_code(&report, "IR0610"), "expected IR0610, got {report}");
}

#[test]
fn dangling_enum_tag_argument_value_is_rejected() {
    let src = r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad(v0.enumtag(@OptionI256)) -> unit {
block0:
    return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];
    let missing_enum_ref = next_missing_compound_ref(&module);
    let arg_value = module.func_store.view(func_ref, |func| func.arg_values[0]);

    module.func_store.modify(func_ref, |func| {
        let Value::Arg { ty, .. } = &mut func.dfg.values[arg_value] else {
            panic!("function argument must remain an arg value");
        };
        *ty = Type::EnumTag(missing_enum_ref);
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

#[test]
fn deleted_result_used_by_live_inst_is_reported() {
    let src = r#"
target = "evm-ethereum-london"

func public %entry(v0.i32, v1.i32) -> i32 {
    block0:
        v2.i32 = add v0 v1;
        return v0;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let module = parsed.module;
    let func_ref = module.funcs()[0];
    let deleted_value = parsed.debug.value(func_ref, "v2").expect("v2 should exist");

    module.func_store.modify(func_ref, |func| {
        let deleted_inst = func
            .dfg
            .value_inst(deleted_value)
            .expect("v2 should be defined by an instruction");
        let block = func.layout.entry_block().expect("entry block should exist");
        let ret_inst = func
            .layout
            .last_inst_of(block)
            .expect("return should exist");

        func.layout.remove_inst(deleted_inst);
        func.erase_inst(deleted_inst);

        func.dfg.untrack_inst(ret_inst);
        func.dfg
            .inst_mut(ret_inst)
            .for_each_value_mut(&mut |value| {
                *value = deleted_value;
            });
        func.dfg.attach_user(ret_inst);
    });

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&module, &cfg);

    assert!(has_code(&report, "IR0001"), "expected IR0001, got {report}");
}

#[test]
fn inst_diagnostic_includes_function_name_and_opcode_context() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_malloc() -> unit {
    block0:
        v0.i256 = evm_malloc 32.i256;
        return;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");

    let diagnostic = report
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code.as_str() == "IR0601")
        .expect("IR0601 diagnostic must exist");
    let context = diagnostic
        .context
        .as_ref()
        .expect("instruction diagnostic should include context");

    assert_eq!(context.function_name.as_deref(), Some("%bad_malloc"));
    assert!(
        context
            .inst_text
            .as_deref()
            .is_some_and(|inst_text| inst_text.contains("evm_malloc")),
        "expected inst text to mention evm_malloc, got {:?}",
        context.inst_text
    );

    let rendered = format!("{report}");
    assert!(
        rendered.contains("%bad_malloc"),
        "expected rendered diagnostic to include function name, got {rendered}"
    );
    assert!(
        rendered.contains("evm_malloc"),
        "expected rendered diagnostic to include opcode text, got {rendered}"
    );
}

#[test]
fn evm_no_result_instruction_rejects_result_value() {
    let src = r#"
target = "evm-ethereum-london"

func public %bad_evm_return_result() -> unit {
    block0:
        v0.i256 = evm_return 0.i256 0.i256;
}
"#;

    let parsed = parse_module(src).expect("module should parse");
    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);

    assert!(has_code(&report, "IR0601"), "expected IR0601, got {report}");
}

#[test]
fn enum_proofs_invalidate_raw_writes_and_saved_tags() {
    for materialize in ["stack", "heap"] {
        for (operation, preserves) in [
            ("", true),
            ("v8.i256 = mload v3 i256;", true),
            ("evm_sstore 0.i256 42.i256;", true),
            ("mstore v3 0.i256 i256;", false),
            ("memzero v3 64.i256;", false),
            (
                "v8.i256 = ptr_to_int v3 i256;\n    evm_mstore v8 0.i256;",
                false,
            ),
            (
                "v8.i256 = ptr_to_int v3 i256;\n    evm_mcopy v8 0.i256 64.i256;",
                false,
            ),
        ] {
            for mode in ["direct", "saved_tag", "fresh_tag", "reassert"] {
                let continuation = match mode {
                    "direct" => "v6.i256 = obj.load v2;\n    return v6;".to_owned(),
                    "reassert" => "v5.objref<@Choice> = enum.assert_variant_ref v0 #Some;\n    v6.i256 = obj.load v2;\n    return v6;".to_owned(),
                    _ => {
                        let refresh = if mode == "fresh_tag" { "v5.enumtag(@Choice) = enum.get_tag v0;" } else { "" };
                        let tag = if mode == "fresh_tag" { "v5" } else { "v4" };
                        format!("obj.store v2 17.i256;\n    {refresh}\n    br_table {tag} block2 (1.enumtag(@Choice) block1);\nblock1:\n    v6.i256 = obj.load v2;\n    return v6;\nblock2:\n    return 0.i256;")
                    }
                };
                let source = format!(
                    r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256) }};
func private %entry(v0.objref<@Choice>) -> i256 {{
block0:
    v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.*@Choice = obj.materialize.{materialize} v0;
    v4.enumtag(@Choice) = enum.get_tag v0;
    {operation}
    {continuation}
}}
"#
                );
                let parsed = parse_module(&source).expect("parse");
                let report = verify_module(
                    &parsed.module,
                    &VerifierConfig::for_level(VerificationLevel::Full),
                );
                let valid = preserves || matches!(mode, "fresh_tag" | "reassert");
                assert_eq!(
                    !report.has_errors(),
                    valid,
                    "{materialize}, {operation}, {mode}: {report}"
                );
                if !valid {
                    assert_eq!(report.errors().count(), 1, "{report}");
                    assert!(has_code(&report, "IR0600"), "{report}");
                }
            }
        }
    }
}

#[test]
fn enum_complete_nested_writes_preserve_outer_initialization() {
    for (field_ty, projection, write, whole) in [
        ("@Inner", "", "enum.write_variant v2 #Some (22.i256);", true),
        (
            "@Pair",
            "v3.objref<@Inner> = obj.proj v2 0.i8;",
            "enum.write_variant v3 #Some (22.i256);",
            false,
        ),
        (
            "@Pair",
            "v3.objref<i256> = obj.proj v2 1.i8;",
            "obj.store v3 22.i256;",
            false,
        ),
    ] {
        for initialized in [true, false] {
            let init = if initialized {
                "v1.objref<@Outer> = enum.assert_variant_ref v0 #Some;"
            } else {
                "enum.set_tag v0 #Some;"
            };
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @Inner = enum {{ #None, #Some(i256) }};
type @Pair = {{ @Inner, i256 }};
type @Outer = enum {{ #None, #Some({field_ty}) }};
func private %entry(v0.objref<@Outer>) -> {field_ty} {{
block0:
    {init}
    v2.objref<{field_ty}> = enum.proj v0 #Some 0.i8;
    {projection}
    {write}
    jump block1;
block1:
    v4.{field_ty} = obj.load v2;
    return v4;
}}
"#
            );
            let parsed = parse_module(&source).expect("parse");
            let report = verify_module(
                &parsed.module,
                &VerifierConfig::for_level(VerificationLevel::Full),
            );
            assert_eq!(
                !report.has_errors(),
                initialized || whole,
                "{field_ty}, {initialized}: {report}"
            );
            if report.has_errors() {
                assert_eq!(report.errors().count(), 1, "{report}");
                assert!(has_code(&report, "IR0600"), "{report}");
            }
        }
    }
}

#[test]
fn enum_proofs_analyze_disconnected_components_from_empty_entries() {
    for (body, valid) in [
        (
            "block1:\n    v2.objref<@Choice> = enum.assert_variant_ref v0 #Some;\n    v3.objref<i256> = enum.proj v2 #Some 0.i8;\n    v4.i256 = obj.load v3;\n    return v4;",
            true,
        ),
        (
            "block1:\n    v2.objref<@Choice> = enum.assert_variant_ref v0 #Some;\n    v3.objref<i256> = enum.proj v2 #Some 0.i8;\n    jump block2;\nblock2:\n    v4.i256 = obj.load v3;\n    br v1 block2 block3;\nblock3:\n    return v4;",
            true,
        ),
        (
            "block1:\n    v3.objref<i256> = enum.proj v0 #Some 0.i8;\n    v4.i256 = obj.load v3;\n    jump block1;",
            false,
        ),
        (
            "block1:\n    enum.set_tag v0 #Some;\n    v3.objref<i256> = enum.proj v0 #Some 0.i8;\n    obj.store v3 17.i256;\n    v5.enumtag(@Choice) = enum.get_tag v0;\n    br_table v5 block3 (1.enumtag(@Choice) block2);\nblock2:\n    v4.i256 = obj.load v3;\n    return v4;\nblock3:\n    return 0.i256;",
            true,
        ),
        (
            "block1:\n    v2.objref<@Choice> = enum.assert_variant_ref v0 #Some;\n    v3.objref<i256> = enum.proj v2 #Some 0.i8;\n    enum.set_tag v0 #None;\n    v4.i256 = obj.load v3;\n    return v4;",
            false,
        ),
    ] {
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256) }};
func private %entry(v0.objref<@Choice>, v1.i1) -> i256 {{
block0:
    return 0.i256;
{body}
}}
"#
        );
        let parsed = parse_module(&source).expect("parse");
        for level in [VerificationLevel::Standard, VerificationLevel::Full] {
            let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
            assert_eq!(!report.has_errors(), valid, "{body}: {report}");
            if !valid {
                assert_eq!(report.errors().count(), 1, "{report}");
                assert!(has_code(&report, "IR0600"), "{report}");
            }
        }
    }
}

#[test]
fn enum_field_proofs_preserve_disjoint_payload_writes() {
    for write in [
        "obj.store v3 42.i256;",
        "v5.constref<i256> = const.ref $word;\n    obj.init.const v3 v5;",
        "v5.objref<@Choice> = enum.assert_variant_ref v1 #Some;\n    v6.objref<i256> = enum.proj v5 #Some 1.i256;\n    obj.store v6 42.i256;",
    ] {
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256,i256) }};
global private const i256 $word = 42;
func private %entry(v0.objref<@Choice>) -> i256 {{
block0:
    v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.objref<i256> = enum.proj v1 #Some 1.i8;
    {write}
    jump block1;
block1:
    v4.i256 = obj.load v2;
    return v4;
}}
"#
        );
        let parsed = parse_module(&source).expect("parse");
        let report = verify_module(
            &parsed.module,
            &VerifierConfig::for_level(VerificationLevel::Full),
        );
        assert!(!report.has_errors(), "{write}: {report}");
    }
}

#[test]
fn enum_field_proofs_preserve_nested_sibling_writes() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
type @Choice = enum { #None, #Some(i256,@Pair) };
func private %entry(v0.objref<@Choice>) -> i256 {
block0:
    v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.objref<@Pair> = enum.proj v1 #Some 1.i8;
    v4.objref<i256> = obj.proj v3 0.i8;
    obj.store v4 42.i256;
    v5.i256 = obj.load v2;
    return v5;
}
"#;
    let parsed = parse_module(source).expect("parse");
    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Full),
    );
    assert!(!report.has_errors(), "{report}");
}

#[test]
fn enum_initialization_proofs_distinguish_objects_and_fields() {
    for (object, field, proven) in [(0, 0, true), (0, 1, false), (1, 0, false), (1, 1, false)] {
        for initialize in [
            "obj.store v2 42.i256;",
            "v6.constref<i256> = const.ref $word;\n    obj.init.const v2 v6;",
        ] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256,i256) }};
global private const i256 $word = 42;
func private %entry() -> i256 {{
block0:
    v0.objref<@Choice> = obj.alloc @Choice;
    v1.objref<@Choice> = obj.alloc @Choice;
    enum.set_tag v0 #Some;
    enum.set_tag v1 #Some;
    v2.objref<i256> = enum.proj v0 #Some 0.i8;
    {initialize}
    v3.i256 = obj.load v2;
    v4.objref<i256> = enum.proj v{object} #Some {field}.i256;
    v5.i256 = obj.load v4;
    return v5;
}}
"#
            );
            let parsed = parse_module(&source).expect("parse");
            let report = verify_module(
                &parsed.module,
                &VerifierConfig::for_level(VerificationLevel::Full),
            );
            assert_eq!(
                !report.has_errors(),
                proven,
                "object {object}, field {field}, {initialize}: {report}"
            );
            if !proven {
                assert!(has_code(&report, "IR0600"), "{report}");
            }
        }
    }
}

#[test]
fn enum_field_proofs_follow_non_topological_block_layout() {
    for write in ["obj.store v3 42.i256;", "enum.set_tag v0 #None;"] {
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256,i256) }};
func private %entry(v0.objref<@Choice>) -> i256 {{
block0:
    jump block2;
block1:
    v4.i256 = obj.load v2;
    return v4;
block2:
    v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.objref<i256> = enum.proj v1 #Some 1.i8;
    {write}
    jump block1;
}}
"#
        );
        let parsed = parse_module(&source).expect("parse");
        let report = verify_module(
            &parsed.module,
            &VerifierConfig::for_level(VerificationLevel::Full),
        );
        assert_eq!(
            !report.has_errors(),
            write.starts_with("obj.store"),
            "{write}: {report}"
        );
    }
}

#[test]
fn shared_enum_field_analysis_keeps_program_points_distinct() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Choice = enum { #None, #Some(i256) };
func private %entry(v0.objref<@Choice>) -> i256 {
block0:
    v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.i256 = obj.load v2;
    enum.set_tag v0 #None;
    v4.i256 = obj.load v2;
    v5.objref<@Choice> = enum.assert_variant_ref v0 #Some;
    v6.objref<i256> = enum.proj v5 #Some 0.i256;
    v7.i256 = obj.load v6;
    return v7;
}
"#;
    let parsed = parse_module(source).expect("parse");
    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Full),
    );
    assert_eq!(report.errors().count(), 1, "{report}");
    assert!(has_code(&report, "IR0600"), "{report}");
}

#[test]
fn enum_field_load_proofs_follow_all_control_flow_paths() {
    let cases = [
        (
            "unconditional edge",
            true,
            r#"
block0:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    jump block1;
block1:
    v4.i256 = obj.load v3;
    return v4;
"#,
        ),
        (
            "diamond preserves dominating assertion",
            true,
            r#"
block0:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    br v1 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v4.i256 = obj.load v3;
    return v4;
"#,
        ),
        (
            "each incoming path proves initialization",
            true,
            r#"
block0:
    v3.objref<i256> = enum.proj v0 #Some 0.i8;
    br v1 block1 block2;
block1:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    jump block3;
block2:
    enum.write_variant v0 #Some (17.i256);
    jump block3;
block3:
    v4.i256 = obj.load v3;
    return v4;
"#,
        ),
        (
            "one incoming path lacks initialization",
            false,
            r#"
block0:
    v3.objref<i256> = enum.proj v0 #Some 0.i8;
    br v1 block1 block2;
block1:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    jump block3;
block2:
    enum.set_tag v0 #Some;
    jump block3;
block3:
    v4.i256 = obj.load v3;
    return v4;
"#,
        ),
        (
            "tag and field initialization in separate blocks",
            true,
            r#"
block0:
    enum.set_tag v0 #Some;
    v3.objref<i256> = enum.proj v0 #Some 0.i8;
    jump block1;
block1:
    obj.store v3 17.i256;
    jump block2;
block2:
    v4.i256 = obj.load v3;
    return v4;
"#,
        ),
        (
            "loop preserves preheader proof",
            true,
            r#"
block0:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    jump block1;
block1:
    v4.i256 = obj.load v3;
    br v1 block1 block2;
block2:
    return v4;
"#,
        ),
        (
            "loop cannot invent initialization",
            false,
            r#"
block0:
    v3.objref<i256> = enum.proj v0 #Some 0.i8;
    jump block1;
block1:
    v4.i256 = obj.load v3;
    br v1 block1 block2;
block2:
    return v4;
"#,
        ),
        (
            "backedge invalidates preheader proof",
            false,
            r#"
block0:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    jump block1;
block1:
    v4.i256 = obj.load v3;
    br v1 block2 block3;
block2:
    enum.set_tag v0 #None;
    jump block1;
block3:
    return v4;
"#,
        ),
        (
            "write through asserted alias invalidates proof",
            false,
            r#"
block0:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    jump block1;
block1:
    enum.set_tag v2 #None;
    jump block2;
block2:
    v4.i256 = obj.load v3;
    return v4;
"#,
        ),
        (
            "call on one incoming path invalidates proof",
            false,
            r#"
block0:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    br v1 block1 block2;
block1:
    call %retag v0;
    jump block3;
block2:
    jump block3;
block3:
    v4.i256 = obj.load v3;
    return v4;
"#,
        ),
        (
            "reassertion after mutation restores proof",
            true,
            r#"
block0:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    jump block1;
block1:
    call %retag v0;
    v5.objref<@OptionI256> = enum.assert_variant_ref v2 #Some;
    jump block2;
block2:
    v4.i256 = obj.load v3;
    return v4;
"#,
        ),
    ];
    for (name, valid, blocks) in cases {
        let src = format!(
            r#"
target = "evm-ethereum-osaka"
type @OptionI256 = enum {{ #None, #Some(i256), }};
func private %retag(v0.objref<@OptionI256>) -> unit {{
block0:
    enum.set_tag v0 #None;
    return;
}}
func private %check(v0.objref<@OptionI256>, v1.i1) -> i256 {{
{blocks}
}}
"#
        );
        let parsed = parse_module(&src).unwrap_or_else(|err| panic!("{name}: {err:?}"));
        let cfg = VerifierConfig::for_level(VerificationLevel::Full);
        let report = verify_module(&parsed.module, &cfg);
        if valid {
            assert!(report.is_ok(), "{name}: expected valid IR, got {report}");
        } else {
            assert!(
                has_code(&report, "IR0600"),
                "{name}: expected missing enum field proof, got {report}"
            );
        }
    }
}

#[test]
fn enum_branch_proof_includes_every_case_and_default_reaching_a_destination() {
    let cases = [
        (
            "shared case and default",
            "block1 (1.enumtag(@OptionI256) block1)",
            false,
        ),
        (
            "distinct case and default",
            "block2 (1.enumtag(@OptionI256) block1)",
            true,
        ),
        (
            "single remaining default variant",
            "block1 (0.enumtag(@OptionI256) block2)",
            true,
        ),
        (
            "two cases share destination",
            "block2 (0.enumtag(@OptionI256) block1) (1.enumtag(@OptionI256) block1)",
            false,
        ),
        (
            "exhaustive cases leave default unreachable",
            "block1 (0.enumtag(@OptionI256) block2) (1.enumtag(@OptionI256) block1)",
            true,
        ),
    ];
    for (name, targets, valid) in cases {
        let src = format!(
            r#"
target = "evm-ethereum-osaka"
type @OptionI256 = enum {{ #None, #Some(i256), }};
func private %check(v0.objref<@OptionI256>) -> i256 {{
block0:
    v1.objref<i256> = enum.proj v0 #Some 0.i8;
    obj.store v1 17.i256;
    v2.enumtag(@OptionI256) = enum.get_tag v0;
    br_table v2 {targets};
block1:
    v3.i256 = obj.load v1;
    return v3;
block2:
    return 0.i256;
}}
"#
        );
        let parsed = parse_module(&src).unwrap_or_else(|err| panic!("{name}: {err:?}"));
        let cfg = VerifierConfig::for_level(VerificationLevel::Full);
        let report = verify_module(&parsed.module, &cfg);
        if valid {
            assert!(report.is_ok(), "{name}: expected valid IR, got {report}");
        } else {
            assert!(
                has_code(&report, "IR0600"),
                "{name}: expected missing enum variant proof, got {report}"
            );
        }
    }
}

#[test]
fn enum_branch_proofs_require_a_current_tag_observation() {
    let cases = [
        ("payload store preserves tag", true, "", "v4"),
        (
            "retag invalidates observation",
            false,
            "enum.set_tag v0 #None;",
            "v4",
        ),
        (
            "asserted alias retag invalidates observation",
            false,
            r#"
    v5.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    enum.set_tag v5 #None;
"#,
            "v4",
        ),
        (
            "unknown parameter alias invalidates observation",
            false,
            "enum.set_tag v2 #None;",
            "v4",
        ),
        (
            "call invalidates observation",
            false,
            "call %retag v0;",
            "v4",
        ),
        (
            "whole object store invalidates observation",
            false,
            r#"
    v5.@OptionI256 = enum.make @OptionI256 #None;
    obj.store v0 v5;
"#,
            "v4",
        ),
        (
            "variant write invalidates observation",
            false,
            "enum.write_variant v0 #None;",
            "v4",
        ),
        (
            "unconditional edge preserves observation",
            true,
            r#"
    jump block1;
block1:
"#,
            "v4",
        ),
        (
            "diamond preserves observation",
            true,
            r#"
    br v1 block4 block5;
block4:
    jump block1;
block5:
    jump block1;
block1:
"#,
            "v4",
        ),
        (
            "mutation on one incoming path invalidates observation",
            false,
            r#"
    br v1 block4 block5;
block4:
    enum.set_tag v0 #None;
    jump block1;
block5:
    jump block1;
block1:
"#,
            "v4",
        ),
        (
            "phi alias mutation invalidates observation",
            false,
            r#"
    br v1 block4 block5;
block4:
    jump block1;
block5:
    jump block1;
block1:
    v5.objref<@OptionI256> = phi (v0 block4) (v0 block5);
    enum.set_tag v5 #None;
"#,
            "v4",
        ),
        (
            "read-only loop preserves observation",
            true,
            r#"
    jump block4;
block4:
    br v1 block4 block1;
block1:
"#,
            "v4",
        ),
        (
            "loop mutation invalidates observation",
            false,
            r#"
    jump block4;
block4:
    enum.set_tag v0 #None;
    br v1 block4 block1;
block1:
"#,
            "v4",
        ),
        (
            "loop rereads after mutation",
            true,
            r#"
    jump block4;
block4:
    enum.set_tag v0 #None;
    v9.enumtag(@OptionI256) = enum.get_tag v0;
    br v1 block4 block1;
block1:
"#,
            "v9",
        ),
        (
            "fresh observation after retag",
            true,
            r#"
    enum.set_tag v0 #None;
    v9.enumtag(@OptionI256) = enum.get_tag v0;
"#,
            "v9",
        ),
        (
            "fresh observation after call",
            true,
            r#"
    call %retag v0;
    v9.enumtag(@OptionI256) = enum.get_tag v0;
"#,
            "v9",
        ),
        (
            "explicit current variant needs no saved observation",
            true,
            "enum.set_tag v0 #Some;",
            "v4",
        ),
    ];
    for (name, valid, transition, scrutinee) in cases {
        let unused_block = if transition.contains("block1:") {
            ""
        } else {
            "block1:\n    unreachable;"
        };
        let src = format!(
            r#"
target = "evm-ethereum-osaka"
type @OptionI256 = enum {{ #None, #Some(i256), }};
func private %retag(v0.objref<@OptionI256>) -> unit {{
block0:
    enum.set_tag v0 #None;
    return;
}}
func private %check(v0.objref<@OptionI256>, v1.i1, v2.objref<@OptionI256>) -> i256 {{
block0:
    v3.objref<i256> = enum.proj v0 #Some 0.i8;
    v4.enumtag(@OptionI256) = enum.get_tag v0;
    {transition}
    obj.store v3 17.i256;
    br_table {scrutinee} block3 (1.enumtag(@OptionI256) block2);
block2:
    v6.i256 = obj.load v3;
    return v6;
block3:
    return 0.i256;
{unused_block}
}}
"#
        );
        let parsed = parse_module(&src).unwrap_or_else(|err| panic!("{name}: {err:?}"));
        let cfg = VerifierConfig::for_level(VerificationLevel::Full);
        let report = verify_module(&parsed.module, &cfg);
        if valid {
            assert!(report.is_ok(), "{name}: expected valid IR, got {report}");
        } else {
            assert!(
                has_code(&report, "IR0600"),
                "{name}: expected missing current variant proof, got {report}"
            );
        }
    }
}
