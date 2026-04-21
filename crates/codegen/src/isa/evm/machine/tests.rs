use sonatina_ir::{
    I256, Immediate, Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::{
        control_flow::Return,
        data::Alloca,
        evm::{EvmMload, EvmMstore},
    },
    isa::{
        Isa,
        evm::{Evm, EvmMachine},
    },
    module::ModuleCtx,
};
use sonatina_parser::parse_module;
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

use super::verify::verify_machine_function;

fn evm_triple() -> TargetTriple {
    TargetTriple::new(
        Architecture::Evm,
        Vendor::Ethereum,
        OperatingSystem::Evm(EvmVersion::Osaka),
    )
}

fn machine_builder() -> ModuleBuilder {
    ModuleBuilder::new(ModuleCtx::new(&EvmMachine::new(evm_triple())))
}

fn expect_machine_rejects(src: &str) {
    let parsed = parse_module(src).expect("module parses");
    let func = parsed.module.funcs()[0];
    parsed.module.func_store.view(func, |function| {
        let err = verify_machine_function(func, function)
            .expect_err("high-level IR should be rejected by machine verifier");
        assert!(
            err.contains("unsupported instruction") || err.contains("must be i1, i256, or unit"),
            "{err}"
        );
    });
}

#[test]
fn machine_verify_accepts_word_machine_ir() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_ok",
            Linkage::Public,
            &[],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let addr = builder.make_imm_value(Immediate::from_i256(I256::from(0), Type::I256));
    let value = builder.make_imm_value(Immediate::from_i256(I256::from(7), Type::I256));
    builder.insert_inst_no_result(EvmMstore::new(is, addr, value));
    let loaded = builder.insert_inst(EvmMload::new(is, addr), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, loaded));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        verify_machine_function(func_ref, function).expect("valid machine IR should verify");
    });
}

#[test]
fn machine_verify_rejects_high_level_ops_and_pointer_values() {
    let mb = machine_builder();
    let ptr_ty = mb.ptr_type(Type::I256);
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_bad",
            Linkage::Public,
            &[],
            ptr_ty,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let machine_is = machine.inst_set();
    let evm = Evm::new(mb.triple());
    let evm_is = evm.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let ptr = builder.insert_inst(Alloca::new(evm_is, Type::I256), ptr_ty);
    builder.insert_inst_no_result(Return::new_single(machine_is, ptr));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        let err = verify_machine_function(func_ref, function)
            .expect_err("pointer-typed high-level IR should be rejected");
        assert!(
            err.contains("must be i1, i256, or unit") || err.contains("unsupported instruction"),
            "{err}"
        );
    });
}

#[test]
fn machine_verify_rejects_high_level_instruction_families() {
    let cases = [
        r#"
target = "evm-ethereum-osaka"

func public %bad() -> *i8 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    return v0;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad() -> *i256 {
block0:
    v0.*i256 = alloca i256;
    return v0;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.*i256) -> *i256 {
block0:
    v1.*i256 = gep v0 1.i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i256) -> i256 {
block0:
    v1.i256 = bitcast v0 i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i256) -> *i256 {
block0:
    v1.*i256 = int_to_ptr v0 *i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.*i256) -> i256 {
block0:
    v1.i256 = ptr_to_int v0 i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i1) -> i256 {
block0:
    v1.i256 = zext v0 i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i1) -> i256 {
block0:
    v1.i256 = sext v0 i256;
    return v1;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func public %bad(v0.i256) -> i256 {
block0:
    v1.i8 = trunc v0 i8;
    v2.i256 = zext v1 i256;
    return v2;
}
"#,
        r#"
target = "evm-ethereum-osaka"

func private %bad() -> objref<i256> {
block0:
    v0.objref<i256> = obj.alloc i256;
    return v0;
}
"#,
        r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %bad() -> @OptionI256 {
block0:
    v0.@OptionI256 = enum.make @OptionI256 #Some (1.i256);
    return v0;
}
"#,
    ];

    for src in cases {
        expect_machine_rejects(src);
    }
}
