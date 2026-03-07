use sonatina_codegen::{
    isa::evm::{EvmBackend, PushWidthPolicy},
    machinst::lower::{LowerBackend, SectionLoweringCtx},
    object::{CompileOptions, compile_object},
};
use sonatina_ir::{
    Module,
    ir_writer::ModuleWriter,
    isa::evm::Evm,
    module::FuncRef,
    object::{EmbedSymbol, ObjectName, SectionName},
};
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

fn defined_funcs(module: &Module) -> Vec<FuncRef> {
    let mut funcs = module.funcs();
    funcs.retain(|func| module.ctx.func_linkage(*func).has_definition());
    funcs
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
    let object_name = ObjectName::from("Contract");
    let section_name = SectionName::from("runtime");
    let embed_symbols: Vec<EmbedSymbol> = Vec::new();
    let section_ctx = SectionLoweringCtx {
        object: &object_name,
        section: &section_name,
        embed_symbols: &embed_symbols,
    };

    let funcs = defined_funcs(&parsed.module);
    backend.prepare_section(&parsed.module, &funcs, &section_ctx);

    let mut writer = ModuleWriter::new(&parsed.module);
    let dumped = writer.dump_string();

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
        dumped.contains("is_zero"),
        "i1 not should be rewritten to is_zero:\n{dumped}"
    );

    let cfg = VerifierConfig::for_level(VerificationLevel::Standard);
    let report = verify_module(&parsed.module, &cfg);
    assert!(
        !report.has_errors(),
        "legalized module must verify:\n{report}"
    );
}

#[test]
fn lower_function_without_prepare_section_legalizes_call_closure() {
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
    let object_name = ObjectName::from("Contract");
    let section_name = SectionName::from("runtime");
    let embed_symbols: Vec<EmbedSymbol> = Vec::new();
    let section_ctx = SectionLoweringCtx {
        object: &object_name,
        section: &section_name,
        embed_symbols: &embed_symbols,
    };

    backend
        .lower_function(
            &parsed.module,
            find_func(&parsed.module, "main"),
            &section_ctx,
        )
        .expect("standalone lowering should legalize the full call closure");

    for func_name in ["main", "helper"] {
        let sig = parsed
            .module
            .ctx
            .get_sig(find_func(&parsed.module, func_name))
            .unwrap_or_else(|| panic!("missing signature for %{func_name}"));
        assert_eq!(sig.args(), &[sonatina_ir::Type::I256]);
        assert_eq!(sig.ret_tys(), &[sonatina_ir::Type::I256]);
    }
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
