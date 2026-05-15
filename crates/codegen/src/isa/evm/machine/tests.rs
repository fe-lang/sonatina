use sonatina_ir::{
    I256, Immediate, Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::{
        arith::Add,
        cmp::{IsZero, Lt},
        control_flow::{Br, BranchKind, Jump, Return},
        data::Alloca,
        evm::{EvmMload, EvmMstore},
        logic::And,
    },
    ir_writer::FuncWriter,
    isa::{
        Isa,
        evm::{Evm, EvmMachine},
    },
    module::ModuleCtx,
};
use sonatina_parser::parse_module;
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

use super::{
    branch::canonicalize_machine_branch_conditions, pipeline::run_machine_opt_pipeline,
    verify::verify_machine_function,
};

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
            err.contains("unsupported instruction") || err.contains("must be i256 or unit"),
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
fn machine_verify_rejects_i1_compare_result() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_i1_cmp",
            Linkage::Public,
            &[Type::I256, Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let lhs = builder.func.arg_values[0];
    let rhs = builder.func.arg_values[1];
    let cmp = builder.insert_inst(Lt::new(is, lhs, rhs), Type::I1);
    let sum = builder.insert_inst(Add::new(is, lhs, cmp), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, sum));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        let err = verify_machine_function(func_ref, function)
            .expect_err("machine IR should reject i1 compare results");
        assert!(err.contains("must be i256 or unit"), "{err}");
    });
}

#[test]
fn machine_verify_rejects_i1_word_operand() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_i1_word",
            Linkage::Public,
            &[Type::I256, Type::I1],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let lhs = builder.func.arg_values[0];
    let rhs = builder.func.arg_values[1];
    let sum = builder.insert_inst(Add::new(is, lhs, rhs), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, sum));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        let err = verify_machine_function(func_ref, function)
            .expect_err("machine IR should reject i1 operands");
        assert!(err.contains("must be i256 or unit"), "{err}");
    });
}

#[test]
fn machine_verify_accepts_word_typed_comparison() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_word_cmp",
            Linkage::Public,
            &[Type::I256, Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let block = builder.append_block();
    builder.switch_to_block(block);
    let lhs = builder.func.arg_values[0];
    let rhs = builder.func.arg_values[1];
    let cmp = builder.insert_inst(Lt::new(is, lhs, rhs), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, cmp));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        verify_machine_function(func_ref, function)
            .expect("word-typed compare result is the machine zext-free form");
    });
}

#[test]
fn machine_gvn_folds_word_bool_constant_without_zext() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_gvn_word_bool_const",
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
    let lhs = builder.make_imm_value(Immediate::from_i256(I256::from(1), Type::I256));
    let rhs = builder.make_imm_value(Immediate::from_i256(I256::from(1), Type::I256));
    let masked = builder.insert_inst(And::new(is, lhs, rhs), Type::I256);
    builder.insert_inst_no_result(Return::new_single(is, masked));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    run_machine_opt_pipeline(&module, &[func_ref], false)
        .expect("GVN should fold word bool constants without panicking");
    module.func_store.view(func_ref, |function| {
        let dumped = FuncWriter::new(func_ref, function).dump_string();
        assert!(dumped.contains("return 1.i256;"), "{dumped}");
        assert!(!dumped.contains(" and "), "{dumped}");
    });
}

#[test]
fn machine_verify_accepts_word_branch_condition() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_word_branch",
            Linkage::Public,
            &[Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let nz = builder.append_block();
    let z = builder.append_block();
    builder.switch_to_block(entry);
    let cond = builder.func.arg_values[0];
    builder.insert_inst_no_result(Br::new(is, cond, nz, z));
    builder.switch_to_block(nz);
    builder.insert_inst_no_result(Return::new_single(is, cond));
    builder.switch_to_block(z);
    builder.insert_inst_no_result(Return::new_single(is, cond));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.view(func_ref, |function| {
        verify_machine_function(func_ref, function)
            .expect("machine branches can test any word-shaped EVM stack value");
    });
}

#[test]
fn machine_gvn_accepts_truthy_word_branch_condition() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_gvn_word_branch",
            Linkage::Public,
            &[Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let nz = builder.append_block();
    let z = builder.append_block();
    builder.switch_to_block(entry);
    let cond = builder.func.arg_values[0];
    builder.insert_inst_no_result(Br::new(is, cond, nz, z));
    builder.switch_to_block(nz);
    builder.insert_inst_no_result(Return::new_single(is, cond));
    builder.switch_to_block(z);
    let zero = builder.make_imm_value(Immediate::zero(Type::I256));
    builder.insert_inst_no_result(Return::new_single(is, zero));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    run_machine_opt_pipeline(&module, &[func_ref], false)
        .expect("GVN should accept truthy word branch conditions");
}

#[test]
fn machine_branch_canonicalize_folds_is_zero_into_branch_polarity() {
    let mb = machine_builder();
    let func_ref = mb
        .declare_function(Signature::new_single(
            "machine_branch_is_zero",
            Linkage::Public,
            &[Type::I256],
            Type::I256,
        ))
        .unwrap();
    let machine = EvmMachine::new(mb.triple());
    let is = machine.inst_set();
    let mut builder = mb.func_builder::<InstInserter>(func_ref);

    let entry = builder.append_block();
    let nz = builder.append_block();
    let z = builder.append_block();
    builder.switch_to_block(entry);
    let arg = builder.func.arg_values[0];
    let cond = builder.insert_inst(IsZero::new(is, arg), Type::I256);
    builder.insert_inst_no_result(Br::new(is, cond, nz, z));
    builder.switch_to_block(nz);
    builder.insert_inst_no_result(Jump::new(is, z));
    builder.switch_to_block(z);
    builder.insert_inst_no_result(Return::new_single(is, arg));
    builder.seal_all();
    builder.finish();

    let module = mb.build();
    module.func_store.modify(func_ref, |function| {
        assert!(canonicalize_machine_branch_conditions(function));
        let term = function
            .layout
            .last_inst_of(entry)
            .expect("entry has terminator");
        let branch = function
            .dfg
            .branch_info(term)
            .expect("entry terminator is branch");
        let BranchKind::Br(br) = branch.branch_kind() else {
            panic!("expected branch terminator");
        };
        assert_eq!(*br.cond(), arg);
        assert_eq!(*br.nz_dest(), z);
        assert_eq!(*br.z_dest(), nz);
        assert!(
            function.layout.iter_inst(entry).all(|inst| !matches!(
                function.dfg.inst(inst).kind(),
                sonatina_ir::inst::InstClassKind::Unary(sonatina_ir::inst::UnaryInstKind::IsZero)
            )),
            "dead is_zero should be removed"
        );
        verify_machine_function(func_ref, function).expect("rewritten machine IR should verify");
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
            err.contains("must be i256 or unit") || err.contains("unsupported instruction"),
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
