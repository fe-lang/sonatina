mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::{
    isa::evm::{EvmBackend, PushWidthPolicy},
    machinst::lower::SectionWorkModule,
    object::{CompileOptions, compile_all_objects},
    optim::Pipeline,
    transform::aggregate::EnumLowerToProduct,
};
use sonatina_ir::{
    I256, Immediate, Linkage, Module, Signature, Type,
    builder::{ModuleBuilder, ObjectBuilder},
    func_cursor::InstInserter,
    inst::{
        control_flow::BrTable,
        data::{EnumAssertVariantRef, EnumGetTag, EnumProj, EnumSetTag, ObjAlloc, ObjLoad},
        downcast, evm,
    },
    ir_writer::ModuleWriter,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
    types::{CompoundType, EnumReprHint, EnumVariantRef, VariantData},
};
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

#[dir_test(dir: "$CARGO_MANIFEST_DIR/test_files/enum_lowering/", glob: "*.sntn")]
fn test_enum_lowering(fixture: Fixture<&str>) {
    let parsed = common::parse_module(fixture.path());

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Standard),
    );
    assert!(
        !report.has_errors(),
        "enum IR should verify before lowering:\n{report}"
    );

    EnumLowerToProduct.run(&parsed.module);

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Standard),
    );
    assert!(
        !report.has_errors(),
        "enum lowering should preserve verifier invariants:\n{report}"
    );

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    snap_test!(writer.dump_string(), fixture.path());
}

#[test]
fn enum_helpers_compile_through_evm_pipeline() {
    let parsed = sonatina_parser::parse_module(
        r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %make_some(v0.i256) -> objref<@OptionI256> {
block0:
    v1.objref<@OptionI256> = obj.alloc @OptionI256;
    enum.write_variant v1 #Some (v0);
    return v1;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.objref<@OptionI256> = call %make_some v0;
    v2.objref<@OptionI256> = enum.assert_variant_ref v1 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    v4.i256 = obj.load v3;
    return v4;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .expect("module should parse");

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Standard),
    );
    assert!(
        !report.has_errors(),
        "enum IR should verify before codegen:\n{report}"
    );

    let opts = CompileOptions {
        fixup_policy: PushWidthPolicy::MinimalRelax,
        emit_symtab: false,
        emit_observability: false,
        verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
    };
    let backend = test_backend();
    compile_all_objects(&parsed.module, &backend, &opts).expect("compile should succeed");

    let prepared = backend
        .prepare_section(SectionWorkModule::from_roots(
            &parsed.module,
            lookup_func(&parsed.module, "entry"),
            &[],
            &[],
        ))
        .expect("prepare should succeed");
    assert_no_live_enum_ir(prepared.module());
    let entry = lookup_func(prepared.module(), "entry");
    let make_some = lookup_func(prepared.module(), "make_some");
    for func_ref in [entry, make_some] {
        prepared.module().func_store.view(func_ref, |func| {
            assert!(
                func.layout
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .all(|inst| {
                        downcast::<&evm::EvmMalloc>(func.inst_set(), func.dfg.inst(inst)).is_none()
                    }),
                "enum helper chain should not force heap materialization",
            );
        });
    }
}

#[test]
fn optimization_pipeline_preserves_enum_assert_variant_ref_proofs() {
    let mut parsed = sonatina_parser::parse_module(
        r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %entry(v0.i256) -> i256 {
block0:
    v1.objref<@OptionI256> = obj.alloc @OptionI256;
    enum.write_variant v1 #Some (v0);
    v2.objref<@OptionI256> = enum.assert_variant_ref v1 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    v4.i256 = obj.load v3;
    return v4;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
    )
    .expect("module should parse");

    Pipeline::speed().run(&mut parsed.module);

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Full),
    );
    assert!(
        !report.has_errors(),
        "optimization pipeline must preserve enum assert proofs:\n{report}"
    );
}

#[test]
fn optimization_pipeline_preserves_branch_proven_nested_enum_payload_loads() {
    let mut parsed = sonatina_parser::parse_module(
        r#"
target = "evm-ethereum-osaka"

type @Inner = enum {
    #None,
    #Some(i256),
};

type @Outer = enum {
    #None,
    #Some(@Inner),
};

func private %entry(v0.objref<@Outer>) -> i256 {
block0:
    v1.enumtag(@Outer) = enum.get_tag v0;
    br_table v1 block2 (1.enumtag(@Outer) block1) (0.enumtag(@Outer) block2);

block1:
    v2.objref<@Outer> = enum.assert_variant_ref v0 #Some;
    v3.objref<@Inner> = enum.proj v2 #Some 0.i8;
    v4.@Inner = obj.load v3;
    return 0.i256;

block2:
    return 0.i256;
}
"#,
    )
    .expect("module should parse");

    Pipeline::speed().run(&mut parsed.module);

    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Full),
    );
    assert!(
        !report.has_errors(),
        "optimization pipeline must preserve branch-proven nested enum payload loads:\n{report}"
    );
}

#[test]
fn enum_tag_br_table_cases_compile_through_evm_codegen() {
    let triple = TargetTriple::new(
        Architecture::Evm,
        Vendor::Ethereum,
        OperatingSystem::Evm(EvmVersion::Osaka),
    );
    let isa = Evm::new(triple);
    let mut builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let is = isa.inst_set();
    let option_ty = builder.declare_enum_type(
        "OptionI256",
        &[
            VariantData {
                name: "None".to_string(),
                explicit_discriminant: Some(0),
                fields: vec![],
            },
            VariantData {
                name: "Some".to_string(),
                explicit_discriminant: Some(1),
                fields: vec![Type::I256],
            },
        ],
        EnumReprHint::Default,
    );
    let Type::Compound(option_enum_ty) = option_ty else {
        panic!("enum type must be compound");
    };
    let option_objref_ty = builder.objref_type(option_ty);
    let some_variant = EnumVariantRef::new(option_enum_ty, 1);
    let none_variant = EnumVariantRef::new(option_enum_ty, 0);
    let func_ref = builder
        .declare_function(Signature::new_single(
            "entry",
            Linkage::Public,
            &[],
            Type::I256,
        ))
        .expect("function declaration should succeed");

    {
        let mut fb = builder.func_builder::<InstInserter>(func_ref);
        let entry = fb.append_block();
        let some_block = fb.append_block();
        let none_block = fb.append_block();
        let default_block = fb.append_block();
        let some_case = fb.make_imm_value(Immediate::EnumTag {
            enum_ty: option_enum_ty,
            value: I256::from(1),
        });
        let none_case = fb.make_imm_value(Immediate::EnumTag {
            enum_ty: option_enum_ty,
            value: I256::from(0),
        });
        let field_idx = fb.make_imm_value(0i8);
        let zero = fb.make_imm_value(I256::zero());
        let fallback = fb.make_imm_value(I256::from(7));

        fb.switch_to_block(entry);
        let option = fb.insert_inst(ObjAlloc::new(is, option_ty), option_objref_ty);
        fb.insert_inst_no_result(EnumSetTag::new(is, option, none_variant));
        let tag = fb.insert_inst(EnumGetTag::new(is, option), Type::EnumTag(option_enum_ty));
        fb.insert_inst_no_result(BrTable::new(
            is,
            tag,
            Some(default_block),
            vec![(some_case, some_block), (none_case, none_block)],
        ));

        fb.switch_to_block(some_block);
        let asserted = fb.insert_inst(
            EnumAssertVariantRef::new(is, option, some_variant),
            option_objref_ty,
        );
        let field = fb.insert_inst(
            EnumProj::new(is, asserted, some_variant, field_idx),
            builder.objref_type(Type::I256),
        );
        let loaded = fb.insert_inst(ObjLoad::new(is, field), Type::I256);
        fb.insert_return(loaded);

        fb.switch_to_block(none_block);
        fb.insert_return(zero);

        fb.switch_to_block(default_block);
        fb.insert_return(fallback);

        fb.seal_all();
        fb.finish();
    }

    let mut object = ObjectBuilder::new("Contract");
    object.section("runtime").entry(func_ref);
    object
        .declare(&mut builder)
        .expect("object declaration should succeed");
    let module = builder.build();

    let opts = CompileOptions {
        fixup_policy: PushWidthPolicy::MinimalRelax,
        emit_symtab: false,
        emit_observability: false,
        verifier_cfg: VerifierConfig::for_level(VerificationLevel::Full),
    };
    let backend = test_backend();
    compile_all_objects(&module, &backend, &opts).expect("compile should succeed");
    let prepared = backend
        .prepare_section(SectionWorkModule::from_roots(&module, func_ref, &[], &[]))
        .expect("prepare should succeed");
    assert_no_live_enum_ir(prepared.module());
}

fn lookup_func(module: &Module, name: &str) -> FuncRef {
    module
        .funcs()
        .into_iter()
        .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
        .expect("function should exist")
}

fn assert_no_live_enum_ir(module: &Module) {
    for func_ref in module.funcs() {
        let sig = module
            .ctx
            .get_sig(func_ref)
            .expect("signature should exist");
        for &ty in sig.args().iter().chain(sig.ret_tys().iter()) {
            assert!(
                !type_contains_live_enum(module, ty),
                "signature still contains enum type"
            );
        }

        module.func_store.view(func_ref, |func| {
            for value in func.dfg.value_ids() {
                assert!(
                    !type_contains_live_enum(module, func.dfg.value_ty(value)),
                    "value {:?} still contains enum type",
                    value
                );
                if let sonatina_ir::Value::Immediate { imm, .. } = func.dfg.value(value) {
                    assert!(
                        !type_contains_live_enum(module, imm.ty()),
                        "immediate {:?} still contains enum type",
                        value
                    );
                }
            }

            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    assert!(
                        downcast::<&sonatina_ir::inst::data::EnumMake>(
                            func.inst_set(),
                            func.dfg.inst(inst)
                        )
                        .is_none()
                            && downcast::<&sonatina_ir::inst::data::EnumTag>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none()
                            && downcast::<&sonatina_ir::inst::data::EnumIsVariant>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none()
                            && downcast::<&sonatina_ir::inst::data::EnumAssertVariant>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none()
                            && downcast::<&sonatina_ir::inst::data::EnumAssertVariantRef>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none()
                            && downcast::<&sonatina_ir::inst::data::EnumExtract>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none()
                            && downcast::<&sonatina_ir::inst::data::EnumSetTag>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none()
                            && downcast::<&sonatina_ir::inst::data::EnumWriteVariant>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none()
                            && downcast::<&sonatina_ir::inst::data::EnumGetTag>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none()
                            && downcast::<&sonatina_ir::inst::data::EnumProj>(
                                func.inst_set(),
                                func.dfg.inst(inst)
                            )
                            .is_none(),
                        "live enum instruction remained after codegen preparation"
                    );
                }
            }
        });
    }
}

fn type_contains_live_enum(module: &Module, ty: Type) -> bool {
    match ty {
        Type::EnumTag(_) => true,
        Type::Compound(cmpd_ref) => match module
            .ctx
            .with_ty_store(|store| store.resolve_compound(cmpd_ref).clone())
        {
            CompoundType::Enum(_) => true,
            CompoundType::Array { elem, .. }
            | CompoundType::Ptr(elem)
            | CompoundType::ObjRef(elem)
            | CompoundType::ConstRef(elem) => type_contains_live_enum(module, elem),
            CompoundType::Struct(data) => data
                .fields
                .iter()
                .copied()
                .any(|field| type_contains_live_enum(module, field)),
            CompoundType::Func { args, ret_tys } => args
                .iter()
                .chain(ret_tys.iter())
                .copied()
                .any(|nested| type_contains_live_enum(module, nested)),
        },
        _ => false,
    }
}

fn test_backend() -> EvmBackend {
    let triple = TargetTriple::new(
        Architecture::Evm,
        Vendor::Ethereum,
        OperatingSystem::Evm(EvmVersion::Osaka),
    );
    EvmBackend::new(Evm::new(triple))
}
