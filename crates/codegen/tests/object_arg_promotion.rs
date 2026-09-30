use sonatina_codegen::transform::aggregate::ObjectArgPromotion;
use sonatina_ir::{Module, Type, ir_writer::ModuleWriter, types::CompoundType};
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module_or_panic};

fn checked(source: &str) -> Module {
    let module = parse_module(source).unwrap().module;
    verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    module
}

fn argument_types(module: &Module, name: &str) -> Vec<Type> {
    let function = module
        .funcs()
        .into_iter()
        .find(|&function| module.ctx.func_sig(function, |sig| sig.name() == name))
        .unwrap();
    module.ctx.func_sig(function, |sig| sig.args().to_vec())
}

const PAIR: &str = r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
func private %sum(v0.objref<@Pair>) -> i256 {
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
    v2.objref<@Pair> = obj.alloc @Pair;
    v3.objref<i256> = obj.proj v2 0.i8;
    obj.store v3 v0;
    v4.objref<i256> = obj.proj v2 1.i8;
    obj.store v4 v1;
    v5.i256 = call %sum v2;
    return v5;
}
"#;

#[test]
fn promotes_entry_fields_and_rewrites_every_call() {
    let module = checked(PAIR);
    let stats = ObjectArgPromotion::default().run(&module);
    assert_eq!((stats.promoted_args, stats.rewritten_calls), (1, 1));
    verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    let text = ModuleWriter::new(&module).dump_string();
    assert_eq!(argument_types(&module, "sum"), [Type::I256, Type::I256]);
    assert_eq!(text.matches("obj.load").count(), 2, "{text}");
    assert_eq!(ObjectArgPromotion::default().run(&module).promoted_args, 0);
}

#[test]
fn keeps_conditional_reads_writes_and_escaped_objects() {
    for body in [
        "v1.objref<i256> = obj.proj v0 0.i8;\n    obj.store v1 7.i256;\n    v2.i256 = obj.load v1;\n    return v2;",
        "v1.objref<i256> = obj.proj v0 0.i8;\n    evm_sstore 0.i256 7.i256;\n    v2.i256 = obj.load v1;\n    return v2;",
        "v1.objref<i256> = obj.proj v0 0.i8;\n    br 0.i1 block1 block2;\nblock1:\n    v2.i256 = obj.load v1;\n    return v2;\nblock2:\n    return 42.i256;",
        "v1.objref<i256> = obj.proj v0 0.i8;\n    v2.i256 = obj.load v1;\n    v3.*@Pair = obj.materialize.stack v0;\n    return v2;",
    ] {
        let start = PAIR.find("    v1.objref<i256>").unwrap();
        let end = PAIR[start..].find("\n}").unwrap() + start;
        let mut source = PAIR.to_owned();
        source.replace_range(start..end, body);
        let module = checked(&source);
        let before = ModuleWriter::new(&module).dump_string();
        assert_eq!(ObjectArgPromotion::default().run(&module).promoted_args, 0);
        assert_eq!(before, ModuleWriter::new(&module).dump_string());
    }
}

#[test]
fn alias_writes_before_any_demanded_read_block_promotion() {
    let source = PAIR
        .replace(
            "%sum(v0.objref<@Pair>)",
            "%sum(v0.objref<@Pair>, v6.objref<i256>)",
        )
        .replace("call %sum v2;", "call %sum v2 v3;");
    for load in ["v2.i256 = obj.load v1;", "v4.i256 = obj.load v3;"] {
        let source = source.replace(load, &format!("obj.store v6 22.i256;\n    {load}"));
        let module = checked(&source);
        assert_eq!(ObjectArgPromotion::default().run(&module).promoted_args, 0);
        verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    }
}

#[test]
fn promotion_reaches_callers_after_complete_signature_cutover() {
    let mut source = PAIR.replace("call %sum v2;", "call %wrapper v2;");
    source.push_str(
        r#"
func private %wrapper(v0.objref<@Pair>) -> i256 {
block0:
    v1.i256 = call %sum v0;
    return v1;
}
"#,
    );
    let module = checked(&source);
    let stats = ObjectArgPromotion::default().run(&module);
    assert_eq!((stats.promoted_args, stats.rewritten_calls), (2, 2));
    verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    assert_eq!(argument_types(&module, "sum"), [Type::I256, Type::I256]);
    assert_eq!(argument_types(&module, "wrapper"), [Type::I256, Type::I256]);
}

#[test]
fn keeps_address_taken_functions_and_object_includes() {
    let pointer = PAIR.replace(
        "    v5.i256 = call %sum v2;",
        "    v6.*(objref<@Pair>) -> i256 = get_function_ptr %sum;\n    v5.i256 = call %sum v2;",
    );
    let object_entry = format!(
        "{PAIR}\nobject @Contract {{ section runtime {{ entry %entry; include %sum; }} }}\n"
    );
    for source in [pointer, object_entry] {
        let module = checked(&source);
        assert_eq!(ObjectArgPromotion::default().run(&module).promoted_args, 0);
        verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    }
}

#[test]
fn promotes_nested_demanded_fields_and_preserves_alias_write_order() {
    let source = r#"
target = "evm-ethereum-osaka"
type @Nested = { [i256; 2], i256 };
func private %read_then_write(v0.objref<@Nested>, v1.objref<i256>) -> i256 {
block0:
    v2.objref<[i256; 2]> = obj.proj v0 0.i8;
    v3.objref<i256> = obj.index v2 1.i256;
    v4.i256 = obj.load v3;
    obj.store v1 22.i256;
    return v4;
}
func public %entry() -> i256 {
block0:
    v0.objref<@Nested> = obj.alloc @Nested;
    v1.objref<[i256; 2]> = obj.proj v0 0.i8;
    v2.objref<i256> = obj.index v1 1.i8;
    obj.store v2 11.i256;
    v3.i256 = call %read_then_write v0 v2;
    return v3;
}
"#;
    let module = checked(source);
    let stats = ObjectArgPromotion::default().run(&module);
    assert_eq!((stats.promoted_args, stats.rewritten_calls), (1, 1));
    verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    let text = ModuleWriter::new(&module).dump_string();
    let arguments = argument_types(&module, "read_then_write");
    assert_eq!(arguments.len(), 2);
    assert_eq!(arguments[0], Type::I256);
    assert!(matches!(
        arguments[1].resolve_compound(&module.ctx),
        Some(CompoundType::ObjRef(Type::I256))
    ));
    assert_eq!(text.matches("obj.load").count(), 1, "{text}");
}
