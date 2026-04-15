use sonatina_codegen::{
    isa::evm::{EvmBackend, PushWidthPolicy, test_util::prepare_root},
    object::{CompileOptions, compile_object},
};
use sonatina_ir::{Module, ir_writer::ModuleWriter, isa::evm::Evm, module::FuncRef};
use sonatina_parser::parse_module;
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

fn evm_backend() -> EvmBackend {
    EvmBackend::new(Evm::new(TargetTriple {
        architecture: Architecture::Evm,
        vendor: Vendor::Ethereum,
        operating_system: OperatingSystem::Evm(sonatina_triple::EvmVersion::Osaka),
    }))
}

fn find_func(module: &Module, name: &str) -> FuncRef {
    module
        .ctx
        .declared_funcs
        .iter()
        .find_map(|entry| (entry.value().name() == name).then(|| *entry.key()))
        .unwrap_or_else(|| panic!("missing function %{name}"))
}

#[test]
fn prepare_section_legalizes_width_sensitive_ops() {
    let source = r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i8, v1.i8) -> (i8, i1) {
    block0:
        (v2.i8, v3.i1) = evm_sdivo v0 v1;
        return (v2, v3);
}

func public %main(v0.i8, v1.i8) -> i8 {
    block0:
        (v2.i8, v3.i1) = usubo v0 v1;
        v4.i16 = sext v2 i16;
        v5.i8 = trunc v4 i8;
        (v6.i8, v7.i1) = call %helper v5 v1;
        v8.i8 = sdiv v6 v1;
        v9.i1 = not v3;
        br v9 block1 block2;

    block1:
        return v8;

    block2:
        return v6;
}
"#;

    let parsed = parse_module(source).expect("module should parse");
    let backend = evm_backend();
    let prepared = prepare_root(&parsed.module, &backend, find_func(&parsed.module, "main"))
        .expect("prepare should succeed");

    let mut writer = ModuleWriter::new(prepared.module());
    let dumped = writer.dump_string();
    let original = ModuleWriter::new(&parsed.module).dump_string();

    for illegal in [
        "i8",
        "i16",
        "usubo",
        "evm_sdivo",
        "sext",
        "trunc",
        " = sdiv ",
        " = not ",
    ] {
        assert!(
            !dumped.contains(illegal),
            "legalized EVM IR should not contain `{illegal}`:\n{dumped}"
        );
    }
    assert!(
        dumped.contains("evm_sdiv"),
        "signed division should be rewritten to evm_sdiv:\n{dumped}"
    );
    assert!(
        !dumped.contains(" = not "),
        "late cleanup may fold the legalized form further, but `not` must be eliminated:\n{dumped}"
    );
    assert!(
        original.contains("usubo") && original.contains("evm_sdivo"),
        "prepare should not mutate the original module:\n{original}"
    );

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(prepared.module(), &cfg);
    assert!(
        !report.has_errors(),
        "legalized module must verify:\n{report}"
    );
}

#[test]
fn lower_function_legalizes_call_closure_after_prepare_section() {
    let source = r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i8) -> i8 {
    block0:
        v1.i8 = add v0 1.i8;
        return v1;
}

func public %main(v0.i8) -> i8 {
    block0:
        v1.i8 = call %helper v0;
        return v1;
}
"#;

    let parsed = parse_module(source).expect("module should parse");
    let backend = evm_backend();
    let prepared = prepare_root(&parsed.module, &backend, find_func(&parsed.module, "main"))
        .expect("prepare should legalize the full call closure");
    backend
        .lower_function(&prepared, find_func(prepared.module(), "main"))
        .expect("lowering should consume the prepared call closure");

    for func_name in ["main", "helper"] {
        let sig = prepared
            .module()
            .ctx
            .get_sig(find_func(prepared.module(), func_name))
            .unwrap_or_else(|| panic!("missing signature for %{func_name}"));
        assert_eq!(sig.args(), &[sonatina_ir::Type::I256]);
        assert_eq!(sig.ret_tys(), &[sonatina_ir::Type::I256]);
    }
    let original_sig = parsed
        .module
        .ctx
        .get_sig(find_func(&parsed.module, "main"))
        .expect("missing original main signature");
    assert_eq!(original_sig.args(), &[sonatina_ir::Type::I8]);
}

#[test]
fn prepare_section_rejects_external_calls() {
    let source = r#"
target = "evm-ethereum-osaka"

declare external %pair_add(i32, i32) -> i32;

func public %main() -> i32 {
    block0:
        v0.i32 = call %pair_add 1.i32 2.i32;
        return v0;
}
"#;

    let parsed = parse_module(source).expect("module should parse");
    let backend = evm_backend();
    let err = match prepare_root(&parsed.module, &backend, find_func(&parsed.module, "main")) {
        Ok(_) => panic!("prepare should reject external calls"),
        Err(err) => err,
    };
    assert!(err.contains("calls to external or declaration-only function %pair_add"));
}

#[test]
fn prepare_section_rejects_call_arity_above_16() {
    let ret_tys = std::iter::repeat_n("i32", 17)
        .collect::<Vec<_>>()
        .join(", ");
    let ret_values = (0..17)
        .map(|idx| format!("{idx}.i32"))
        .collect::<Vec<_>>()
        .join(", ");
    let call_results = (0..17)
        .map(|idx| format!("v{idx}.i32"))
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!(
        r#"
target = "evm-ethereum-osaka"

func public %pair_many() -> ({ret_tys}) {{
    block0:
        return ({ret_values});
}}

func public %main() -> i32 {{
    block0:
        ({call_results}) = call %pair_many;
        return v0;
}}
"#
    );

    let parsed = parse_module(&source).expect("module should parse");
    let backend = evm_backend();
    let err = match prepare_root(&parsed.module, &backend, find_func(&parsed.module, "main")) {
        Ok(_) => panic!("prepare should reject calls with more than 16 results"),
        Err(err) => err,
    };
    assert!(err.contains("supports at most 16"));
}

#[test]
fn compile_object_legalizes_checked_evm_divmod_and_overflow_ops() {
    let source = r#"
target = "evm-ethereum-osaka"

func public %main(v0.i8, v1.i8) -> i8 {
    block0:
        (v2.i8, v3.i1) = evm_udivo v0 v1;
        (v4.i8, v5.i1) = evm_smodo v2 v1;
        (v6.i8, v7.i1) = smulo v4 v2;
        br v3 block1 block2;

    block1:
        return v6;

    block2:
        return v4;
}

object @O {
  section runtime {
    entry %main;
  }
}
"#;

    let parsed = parse_module(source).expect("module should parse");
    let backend = evm_backend();
    let opts = CompileOptions {
        fixup_policy: PushWidthPolicy::MinimalRelax,
        emit_symtab: false,
        emit_observability: false,
        verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
    };

    compile_object(&parsed.module, &backend, "O", &opts)
        .expect("object compilation should legalize checked EVM div/mod and overflow ops");
}
