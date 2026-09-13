#![allow(clippy::crosspointer_transmute)]

#[path = "cranelift/casts.rs"]
mod casts;
#[path = "cranelift/memory.rs"]
mod memory;
#[path = "cranelift/scalar.rs"]
mod scalar;
#[path = "cranelift/control_flow.rs"]
mod wide_control_flow;

use sonatina_codegen::{
    Compile,
    isa::cranelift::{CraneliftError, CraneliftJitArtifact, CraneliftJitBackend},
};
use sonatina_ir::{
    I256, Immediate, Linkage, Signature, Type, U256,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    global_variable::{GlobalVariableData, GvInitializer},
    inst::{arith, cast, cmp, control_flow, data, logic},
    isa::{Isa, native::Native},
    module::ModuleCtx,
    types::{EnumReprHint, EnumVariantRef, VariantData},
};
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

fn native_isa() -> Native {
    let architecture = if cfg!(target_arch = "x86_64") {
        Architecture::X86_64
    } else if cfg!(target_arch = "aarch64") {
        Architecture::Aarch64
    } else {
        panic!("Cranelift tests require an x86_64 or aarch64 host")
    };
    Native::new(TargetTriple::new(
        architecture,
        Vendor::Unknown,
        OperatingSystem::Native,
    ))
}

fn parse_native_module(source: &str) -> sonatina_ir::Module {
    sonatina_parser::parse_module(&format!("target = \"{}\"\n{source}", native_isa().triple()))
        .expect("native IR should parse")
        .module
}

fn compile_add() -> CraneliftJitArtifact {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "add_i64",
            Linkage::Public,
            &[Type::I64, Type::I64],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let sum = function_builder.insert_inst(
        arith::Add::new(
            instructions,
            function_builder.args()[0],
            function_builder.args()[1],
        ),
        Type::I64,
    );
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, sum));
    function_builder.seal_all();
    function_builder.finish();

    Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("JIT compilation should succeed")
}

#[test]
fn jit_executes_a_native_c_abi_function() {
    let artifact = compile_add();
    let address = artifact
        .function_address("add_i64")
        .expect("compiled function should be addressable");
    let add: unsafe extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(address) };

    assert_eq!(unsafe { add(3, 4) }, 7);
    assert_eq!(unsafe { add(-10, 25) }, 15);
}

#[test]
fn memzero_uses_i256_addresses_and_lengths() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_unit(
            "zero_memory",
            Linkage::Public,
            &[Type::I256, Type::I256],
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    function_builder.insert_inst_no_result(data::Memzero::new(
        instructions,
        function_builder.args()[0],
        function_builder.args()[1],
    ));
    function_builder.insert_inst_no_result(control_flow::Return::new_unit(instructions));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("memzero should compile");
    let address = artifact.function_address("zero_memory").unwrap();
    let zero_memory: unsafe extern "C" fn(*const u64, *const u64) =
        unsafe { std::mem::transmute(address) };

    let mut bytes = [0xa5u8; 8];
    let dest = [bytes[2..].as_mut_ptr() as usize as u64, 0, 0, 0];
    let len = [3, 0, 0, 0];
    unsafe { zero_memory(dest.as_ptr(), len.as_ptr()) };
    assert_eq!(bytes, [0xa5, 0xa5, 0, 0, 0, 0xa5, 0xa5, 0xa5]);
}

#[test]
fn memzero_accepts_pointer_destinations() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let pointer_type = builder.ptr_type(Type::I8);
    let function = builder
        .declare_function(Signature::new_unit(
            "zero_memory",
            Linkage::Public,
            &[pointer_type, Type::I64],
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    function_builder.insert_inst_no_result(data::Memzero::new(
        instructions,
        function_builder.args()[0],
        function_builder.args()[1],
    ));
    function_builder.insert_inst_no_result(control_flow::Return::new_unit(instructions));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("memzero should compile");
    let address = artifact.function_address("zero_memory").unwrap();
    let zero_memory: unsafe extern "C" fn(*mut u8, u64) = unsafe { std::mem::transmute(address) };

    let mut bytes = [0xa5u8; 4];
    unsafe { zero_memory(bytes[1..].as_mut_ptr(), 2) };
    assert_eq!(bytes, [0xa5, 0, 0, 0xa5]);
}

#[test]
fn function_address_is_scoped_to_the_artifact() {
    let isa = native_isa();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    builder
        .declare_function(Signature::new_single(
            "external_function",
            Linkage::External,
            &[],
            Type::I64,
        ))
        .unwrap();
    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("external declaration should compile");
    assert!(artifact.function_address("missing").is_none());
    assert!(artifact.function_address("external_function").is_none());

    let artifact = compile_add();
    assert!(artifact.function_address("add_i64").is_some());
}

#[test]
fn enum_tag_constant_initializers_are_legalized_before_emission() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let enum_ty = builder.declare_enum_type(
        "Flag",
        &[
            VariantData {
                name: "Off".to_string(),
                explicit_discriminant: Some(0),
                fields: vec![],
            },
            VariantData {
                name: "On".to_string(),
                explicit_discriminant: Some(1),
                fields: vec![],
            },
        ],
        EnumReprHint::Default,
    );
    let Type::Compound(enum_ty) = enum_ty else {
        unreachable!();
    };
    let tag_ty = Type::EnumTag(enum_ty);
    let tags_ty = builder.declare_array_type(tag_ty, 2);
    let global = builder.declare_gv(GlobalVariableData::constant(
        "FLAGS".to_string(),
        tags_ty,
        Linkage::Private,
        GvInitializer::make_array(vec![
            GvInitializer::Immediate(Immediate::EnumTag {
                enum_ty,
                value: I256::zero(),
            }),
            GvInitializer::Immediate(Immediate::EnumTag {
                enum_ty,
                value: I256::from(1),
            }),
        ]),
    ));
    let function = builder
        .declare_function(Signature::new_single(
            "read_flag",
            Linkage::Public,
            &[],
            tag_ty,
        ))
        .unwrap();
    let tags_ref_ty = builder.constref_type(tags_ty);
    let tag_ref_ty = builder.constref_type(tag_ty);
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let index = function_builder.make_imm_value(1i64);
    let tags = function_builder.insert_inst(
        data::ConstRef::new(instructions, global.into()),
        tags_ref_ty,
    );
    let tag =
        function_builder.insert_inst(data::ConstIndex::new(instructions, tags, index), tag_ref_ty);
    let tag = function_builder.insert_inst(data::ConstLoad::new(instructions, tag), tag_ty);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, tag));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("enum-tag constant should compile");
    let address = artifact.function_address("read_flag").unwrap();
    let read_flag: unsafe extern "C" fn() -> u8 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { read_flag() }, 1);
}

#[test]
fn enum_instructions_are_legalized_before_translation() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let option_type = builder.declare_enum_type(
        "OptionI64",
        &[
            VariantData {
                name: "None".to_string(),
                explicit_discriminant: Some(0),
                fields: vec![],
            },
            VariantData {
                name: "Some".to_string(),
                explicit_discriminant: Some(1),
                fields: vec![],
            },
        ],
        EnumReprHint::Default,
    );
    let option_enum = match option_type {
        Type::Compound(option_enum) => option_enum,
        _ => panic!("enum type should be compound"),
    };
    let option_ref_type = builder.objref_type(option_type);
    let none_variant = EnumVariantRef::new(option_enum, 0);
    let function = builder
        .declare_function(Signature::new_single(
            "enum_branch",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    let some_block = function_builder.append_block();
    let none_block = function_builder.append_block();
    let default_block = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let option = function_builder.insert_inst(
        data::ObjAlloc::new(instructions, option_type),
        option_ref_type,
    );
    function_builder.insert_inst_no_result(data::EnumSetTag::new(
        instructions,
        option,
        none_variant,
    ));
    let tag = function_builder.insert_inst(
        data::EnumGetTag::new(instructions, option),
        Type::EnumTag(option_enum),
    );
    let none_case = function_builder.make_imm_value(Immediate::EnumTag {
        enum_ty: option_enum,
        value: I256::zero(),
    });
    let some_case = function_builder.make_imm_value(Immediate::EnumTag {
        enum_ty: option_enum,
        value: I256::from(1),
    });
    function_builder.insert_inst_no_result(control_flow::BrTable::new(
        instructions,
        tag,
        Some(default_block),
        vec![(some_case, some_block), (none_case, none_block)],
    ));

    for (block, result) in [
        (some_block, 11i64),
        (none_block, 22i64),
        (default_block, 33i64),
    ] {
        function_builder.switch_to_block(block);
        let result = function_builder.make_imm_value(result);
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, result));
    }
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("enum instructions should be legalized");
    let address = artifact.function_address("enum_branch").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 22);
}

#[test]
fn jit_reports_the_root_translation_error() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "bad_cmp",
            Linkage::Public,
            &[Type::I64],
            Type::I1,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let lhs = function_builder.args()[0];
    let rhs = function_builder.make_imm_value(Immediate::from_i256(I256::from(3u8), Type::I256));
    let result = function_builder.insert_inst(cmp::Lt::new(instructions, lhs, rhs), Type::I1);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, result));
    function_builder.seal_all();
    function_builder.finish();

    let errors = match Compile::new(builder.build(), CraneliftJitBackend::new()).compile() {
        Ok(_) => panic!("mismatched comparison should fail translation"),
        Err(errors) => errors,
    };
    assert!(matches!(
        errors.as_slice(),
        [CraneliftError::Translation(message)]
            if message.contains("failed to translate function bad_cmp")
                && message.contains("cannot compare mismatched i256 and scalar values")
    ));
}

#[test]
fn jit_emits_blocks_in_reverse_postorder() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "late_layout_def",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    let use_block = function_builder.append_block();
    let definition_block = function_builder.append_block();

    function_builder.switch_to_block(definition_block);
    let lhs = function_builder.make_imm_value(37i64);
    let rhs = function_builder.make_imm_value(5i64);
    let value = function_builder.insert_inst(arith::Add::new(instructions, lhs, rhs), Type::I64);
    function_builder.insert_inst_no_result(control_flow::Jump::new(instructions, use_block));

    function_builder.switch_to_block(entry);
    function_builder.insert_inst_no_result(control_flow::Jump::new(instructions, definition_block));

    function_builder.switch_to_block(use_block);
    let one = function_builder.make_imm_value(1i64);
    let result = function_builder.insert_inst(arith::Add::new(instructions, value, one), Type::I64);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, result));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("JIT compilation should follow control-flow order");
    let address = artifact.function_address("late_layout_def").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 43);
}

#[test]
fn jit_predeclares_phi_block_parameters() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "later_phi_target",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    let then_block = function_builder.append_block();
    let else_block = function_builder.append_block();
    let join_block = function_builder.append_block();

    function_builder.switch_to_block(entry);
    let condition = function_builder.make_imm_value(true);
    function_builder.insert_inst_no_result(control_flow::Br::new(
        instructions,
        condition,
        then_block,
        else_block,
    ));

    function_builder.switch_to_block(then_block);
    let then_value = function_builder.make_imm_value(11i64);
    function_builder.insert_inst_no_result(control_flow::Jump::new(instructions, join_block));

    function_builder.switch_to_block(else_block);
    let else_value = function_builder.make_imm_value(22i64);
    function_builder.insert_inst_no_result(control_flow::Jump::new(instructions, join_block));

    function_builder.switch_to_block(join_block);
    let phi = function_builder.insert_inst(
        control_flow::Phi::new(
            instructions,
            vec![(then_value, then_block), (else_value, else_block)],
        ),
        Type::I64,
    );
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, phi));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("JIT compilation should predeclare phi block parameters");
    let address = artifact.function_address("later_phi_target").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 11);
}

#[test]
fn empty_branch_table_jumps_to_its_default() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "empty_branch_table",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    let default = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let scrutinee = function_builder.make_imm_value(0i8);
    function_builder.insert_inst_no_result(control_flow::BrTable::new(
        instructions,
        scrutinee,
        Some(default),
        vec![],
    ));
    function_builder.switch_to_block(default);
    let value = function_builder.make_imm_value(42i64);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, value));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("empty branch table should compile");
    let address = artifact.function_address("empty_branch_table").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 42);
}

#[test]
fn branch_table_compares_i256_values() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "i256_branch_table",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    let matched = function_builder.append_block();
    let default = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let value = function_builder.make_imm_value(Immediate::from_i256(
        I256::from(U256::one() << 128),
        Type::I256,
    ));
    let case = function_builder.make_imm_value(Immediate::from_i256(
        I256::from(U256::one() << 128),
        Type::I256,
    ));
    function_builder.insert_inst_no_result(control_flow::BrTable::new(
        instructions,
        value,
        Some(default),
        vec![(case, matched)],
    ));
    function_builder.switch_to_block(matched);
    let value = function_builder.make_imm_value(42i64);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, value));
    function_builder.switch_to_block(default);
    let value = function_builder.make_imm_value(0i64);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, value));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("i256 branch table should compile");
    let address = artifact.function_address("i256_branch_table").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 42);
}

#[test]
fn i128_immediates_preserve_their_upper_half() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "i128_high_half",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let value = function_builder.make_imm_value(Immediate::I128(
        (0x1234_5678_9abc_def0_i128 << 64) | 0x0fed_cba9_8765_4321_i128,
    ));
    let shift = function_builder.make_imm_value(Immediate::I128(64));
    let high =
        function_builder.insert_inst(arith::Shr::new(instructions, shift, value), Type::I128);
    let high =
        function_builder.insert_inst(cast::Trunc::new(instructions, high, Type::I64), Type::I64);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, high));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("i128 immediate should compile");
    let address = artifact.function_address("i128_high_half").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 0x1234_5678_9abc_def0_i64);
}

#[test]
fn native_pointer_casts_round_trip() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let object_ref_type = builder.objref_type(Type::I64);
    let function = builder
        .declare_function(Signature::new_single(
            "cast_round_trip",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let object = function_builder.insert_inst(
        data::ObjAlloc::new(instructions, Type::I64),
        object_ref_type,
    );
    let address = function_builder.insert_inst(
        cast::PtrToInt::new(instructions, object, Type::I64),
        Type::I64,
    );
    let pointer = function_builder.insert_inst(
        cast::IntToPtr::new(instructions, address, object_ref_type),
        object_ref_type,
    );
    let value = function_builder.make_imm_value(123i64);
    function_builder.insert_inst_no_result(data::ObjStore::new(instructions, pointer, value));
    let loaded = function_builder.insert_inst(data::ObjLoad::new(instructions, pointer), Type::I64);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, loaded));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("pointer casts should compile");
    let address = artifact.function_address("cast_round_trip").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 123);
}

#[test]
fn i256_addresses_and_boolean_extensions_round_trip() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let pointer_type = builder.ptr_type(Type::I256);
    let function = builder
        .declare_function(Signature::new_single(
            "i256_address_round_trip",
            Linkage::Public,
            &[],
            Type::I32,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let slot =
        function_builder.insert_inst(data::Alloca::new(instructions, Type::I256), pointer_type);
    let address = function_builder.insert_inst(
        cast::PtrToInt::new(instructions, slot, Type::I256),
        Type::I256,
    );
    let value = function_builder.make_imm_value(Immediate::from_i256(I256::from(12u8), Type::I256));
    function_builder.insert_inst_no_result(data::Mstore::new(
        instructions,
        address,
        value,
        Type::I256,
    ));
    let loaded =
        function_builder.insert_inst(data::Mload::new(instructions, slot, Type::I256), Type::I256);
    let loaded =
        function_builder.insert_inst(cast::Trunc::new(instructions, loaded, Type::I32), Type::I32);
    let true_value = function_builder.make_imm_value(true);
    let widened = function_builder.insert_inst(
        cast::Sext::new(instructions, true_value, Type::I256),
        Type::I256,
    );
    let widened = function_builder.insert_inst(
        cast::Trunc::new(instructions, widened, Type::I32),
        Type::I32,
    );
    let result =
        function_builder.insert_inst(arith::Add::new(instructions, loaded, widened), Type::I32);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, result));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("i256 address casts should compile");
    let address = artifact
        .function_address("i256_address_round_trip")
        .unwrap();
    let function: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 11);
}

#[test]
fn fresh_object_returns_use_caller_owned_storage() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let object_ref_type = builder.objref_type(Type::I64);
    let make = builder
        .declare_function(Signature::new_single(
            "make_ref",
            Linkage::Private,
            &[],
            object_ref_type,
        ))
        .unwrap();
    let read = builder
        .declare_function(Signature::new_single(
            "load_returned_ref",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let clobber = builder
        .declare_function(Signature::new_unit(
            "clobber_object_stack",
            Linkage::Private,
            &[],
        ))
        .unwrap();

    {
        let mut function_builder = builder.func_builder::<InstInserter>(make);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let object = function_builder.insert_inst(
            data::ObjAlloc::new(instructions, Type::I64),
            object_ref_type,
        );
        let value = function_builder.make_imm_value(123i64);
        function_builder.insert_inst_no_result(data::ObjStore::new(instructions, object, value));
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, object));
        function_builder.seal_all();
        function_builder.finish();
    }

    {
        let mut function_builder = builder.func_builder::<InstInserter>(clobber);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let object = function_builder.insert_inst(
            data::ObjAlloc::new(instructions, Type::I64),
            object_ref_type,
        );
        let value = function_builder.make_imm_value(999i64);
        function_builder.insert_inst_no_result(data::ObjStore::new(instructions, object, value));
        function_builder.insert_inst_no_result(control_flow::Return::new_unit(instructions));
        function_builder.seal_all();
        function_builder.finish();
    }

    {
        let mut function_builder = builder.func_builder::<InstInserter>(read);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let object = function_builder.insert_inst(
            control_flow::Call::new(instructions, make, smallvec::smallvec![]),
            object_ref_type,
        );
        function_builder.insert_inst_no_result(control_flow::Call::new(
            instructions,
            clobber,
            smallvec::smallvec![],
        ));
        let value =
            function_builder.insert_inst(data::ObjLoad::new(instructions, object), Type::I64);
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, value));
        function_builder.seal_all();
        function_builder.finish();
    }

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("fresh object return should compile");
    let address = artifact.function_address("load_returned_ref").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 123);
}

#[test]
fn borrowed_object_references_return_directly() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let object_ref_type = builder.objref_type(Type::I64);
    let identity = builder
        .declare_function(Signature::new_single(
            "identity_ref",
            Linkage::Private,
            &[object_ref_type],
            object_ref_type,
        ))
        .unwrap();
    let read = builder
        .declare_function(Signature::new_single(
            "read_identity_ref",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();

    {
        let mut function_builder = builder.func_builder::<InstInserter>(identity);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let object = function_builder.args()[0];
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, object));
        function_builder.seal_all();
        function_builder.finish();
    }

    {
        let mut function_builder = builder.func_builder::<InstInserter>(read);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let object = function_builder.insert_inst(
            data::ObjAlloc::new(instructions, Type::I64),
            object_ref_type,
        );
        let value = function_builder.make_imm_value(123i64);
        function_builder.insert_inst_no_result(data::ObjStore::new(instructions, object, value));
        let object = function_builder.insert_inst(
            control_flow::Call::new(instructions, identity, smallvec::smallvec![object]),
            object_ref_type,
        );
        let value =
            function_builder.insert_inst(data::ObjLoad::new(instructions, object), Type::I64);
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, value));
        function_builder.seal_all();
        function_builder.finish();
    }

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("borrowed object return should compile");
    let address = artifact.function_address("read_identity_ref").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 123);
}

#[test]
fn i256_integer_ops_preserve_all_limbs() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "i256_integer_ops",
            Linkage::Public,
            &[],
            Type::I32,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);

    macro_rules! word {
        ($value:expr) => {
            function_builder.make_imm_value(Immediate::from_i256($value, Type::I256))
        };
    }

    let three_high = word!(I256::from(U256::from(3u8) << 64));
    let one_high = word!(I256::from(U256::one() << 64));
    let three = word!(I256::from(3u8));
    let product =
        function_builder.insert_inst(arith::Mul::new(instructions, one_high, three), Type::I256);
    let product_ok =
        function_builder.insert_inst(cmp::Eq::new(instructions, product, three_high), Type::I1);

    let five = word!(I256::from(5u8));
    let neg_five = function_builder.insert_inst(arith::Neg::new(instructions, five), Type::I256);
    let neg_five = function_builder.insert_inst(
        cast::Trunc::new(instructions, neg_five, Type::I32),
        Type::I32,
    );

    let zero = word!(I256::zero());
    let not_zero = function_builder.insert_inst(logic::Not::new(instructions, zero), Type::I256);
    let not_zero = function_builder.insert_inst(
        cast::Trunc::new(instructions, not_zero, Type::I32),
        Type::I32,
    );

    let mask_lhs = word!(I256::from(0xf0u16));
    let mask_rhs = word!(I256::from(0xccu16));
    let mask = function_builder.insert_inst(
        logic::And::new(instructions, mask_lhs, mask_rhs),
        Type::I256,
    );
    let or_rhs = word!(I256::from(0x03u8));
    let masked =
        function_builder.insert_inst(logic::Or::new(instructions, mask, or_rhs), Type::I256);
    let xor_rhs = word!(I256::from(0x0fu8));
    let xored =
        function_builder.insert_inst(logic::Xor::new(instructions, masked, xor_rhs), Type::I256);
    let xored =
        function_builder.insert_inst(cast::Trunc::new(instructions, xored, Type::I32), Type::I32);

    let one = word!(I256::one());
    let shift_65 = word!(I256::from(65u8));
    let shift_64 = word!(I256::from(64u8));
    let shifted_left =
        function_builder.insert_inst(arith::Shl::new(instructions, shift_65, one), Type::I256);
    let shifted_right = function_builder.insert_inst(
        arith::Shr::new(instructions, shift_64, shifted_left),
        Type::I256,
    );
    let shifted_right = function_builder.insert_inst(
        cast::Trunc::new(instructions, shifted_right, Type::I32),
        Type::I32,
    );

    let negative_eight = word!(I256::from(-8i8));
    let shift_one = word!(I256::one());
    let shifted_arithmetic = function_builder.insert_inst(
        arith::Sar::new(instructions, shift_one, negative_eight),
        Type::I256,
    );
    let shifted_arithmetic = function_builder.insert_inst(
        cast::Trunc::new(instructions, shifted_arithmetic, Type::I32),
        Type::I32,
    );

    let product_ok = function_builder.insert_inst(
        cast::Zext::new(instructions, product_ok, Type::I32),
        Type::I32,
    );
    let mut accumulator = product_ok;
    for value in [neg_five, not_zero, xored, shifted_right, shifted_arithmetic] {
        accumulator = function_builder
            .insert_inst(arith::Add::new(instructions, accumulator, value), Type::I32);
    }
    function_builder
        .insert_inst_no_result(control_flow::Return::new_single(instructions, accumulator));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("i256 integer operations should compile");
    let address = artifact.function_address("i256_integer_ops").unwrap();
    let function: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 197);
}

#[test]
fn i256_division_overflow_and_saturating_ops_match_semantics() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "i256_checked_ops",
            Linkage::Public,
            &[],
            Type::I32,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);

    macro_rules! word {
        ($value:expr) => {
            function_builder.make_imm_value(Immediate::from_i256($value, Type::I256))
        };
    }
    macro_rules! add_bool {
        ($accumulator:ident, $value:expr) => {{
            let value = function_builder
                .insert_inst(cast::Zext::new(instructions, $value, Type::I32), Type::I32);
            $accumulator = function_builder.insert_inst(
                arith::Add::new(instructions, $accumulator, value),
                Type::I32,
            );
        }};
    }
    macro_rules! add_word_eq {
        ($accumulator:ident, $value:expr, $expected:expr) => {{
            let expected = word!($expected);
            let matches = function_builder
                .insert_inst(cmp::Eq::new(instructions, $value, expected), Type::I1);
            add_bool!($accumulator, matches);
        }};
    }

    let zero_i32 = function_builder.make_imm_value(0i32);
    let mut accumulator = zero_i32;
    let big = (U256::one() << 130) + U256::from(123u8);
    let seven_unsigned = U256::from(7u8);
    let big_word = word!(I256::from(big));
    let seven_word = word!(I256::from(seven_unsigned));
    let quotient = function_builder.insert_inst(
        arith::Udiv::new(instructions, big_word, seven_word),
        Type::I256,
    );
    let remainder = function_builder.insert_inst(
        arith::Umod::new(instructions, big_word, seven_word),
        Type::I256,
    );
    add_word_eq!(accumulator, quotient, I256::from(big / seven_unsigned));
    add_word_eq!(accumulator, remainder, I256::from(big % seven_unsigned));

    let negative_hundred = word!(I256::from(-100i8));
    let seven = word!(I256::from(7u8));
    let quotient = function_builder.insert_inst(
        arith::Sdiv::new(instructions, negative_hundred, seven),
        Type::I256,
    );
    let remainder = function_builder.insert_inst(
        arith::Smod::new(instructions, negative_hundred, seven),
        Type::I256,
    );
    add_word_eq!(accumulator, quotient, I256::from(-14i8));
    add_word_eq!(accumulator, remainder, I256::from(-2i8));

    let signed_min = I256::from(U256::one() << 255);
    let signed_max = I256::from((U256::one() << 255) - U256::one());
    let unsigned_max = I256::all_one();
    let signed_min_word = word!(signed_min);
    let negative_one = word!(I256::from(-1i8));
    let quotient = function_builder.insert_inst(
        arith::Sdiv::new(instructions, signed_min_word, negative_one),
        Type::I256,
    );
    let remainder = function_builder.insert_inst(
        arith::Smod::new(instructions, signed_min_word, negative_one),
        Type::I256,
    );
    add_word_eq!(accumulator, quotient, signed_min);
    add_word_eq!(accumulator, remainder, I256::zero());

    let zero = word!(I256::zero());
    let one = word!(I256::one());
    let two = word!(I256::from(2u8));
    let unsigned_max_word = word!(unsigned_max);
    let signed_max_word = word!(signed_max);
    let signed_min_word = word!(signed_min);

    let [raw, overflow] = function_builder.insert_uaddo(unsigned_max_word, one);
    add_word_eq!(accumulator, raw, I256::zero());
    add_bool!(accumulator, overflow);

    let [raw, overflow] = function_builder.insert_saddo(signed_max_word, one);
    add_word_eq!(accumulator, raw, signed_min);
    add_bool!(accumulator, overflow);

    let [raw, overflow] = function_builder.insert_usubo(zero, one);
    add_word_eq!(accumulator, raw, unsigned_max);
    add_bool!(accumulator, overflow);

    let [raw, overflow] = function_builder.insert_ssubo(signed_min_word, one);
    add_word_eq!(accumulator, raw, signed_max);
    add_bool!(accumulator, overflow);

    let high_a = word!(I256::from(U256::one() << 128));
    let high_b = word!(I256::from(U256::one() << 128));
    let [raw, overflow] = function_builder.insert_umulo(high_a, high_b);
    add_word_eq!(accumulator, raw, I256::zero());
    add_bool!(accumulator, overflow);

    let [raw, overflow] = function_builder.insert_smulo(signed_max_word, two);
    add_word_eq!(accumulator, raw, I256::from(-2i8));
    add_bool!(accumulator, overflow);

    let [raw, overflow] = function_builder.insert_snego(signed_min_word);
    add_word_eq!(accumulator, raw, signed_min);
    add_bool!(accumulator, overflow);

    let saturated = function_builder.insert_uaddsat(unsigned_max_word, one);
    add_word_eq!(accumulator, saturated, unsigned_max);

    let saturated = function_builder.insert_saddsat(signed_max_word, one);
    add_word_eq!(accumulator, saturated, signed_max);

    let saturated = function_builder.insert_usubsat(zero, one);
    add_word_eq!(accumulator, saturated, I256::zero());

    let saturated = function_builder.insert_ssubsat(signed_min_word, one);
    add_word_eq!(accumulator, saturated, signed_min);

    let high_a = word!(I256::from(U256::one() << 128));
    let high_b = word!(I256::from(U256::one() << 128));
    let saturated = function_builder.insert_umulsat(high_a, high_b);
    add_word_eq!(accumulator, saturated, unsigned_max);

    let saturated = function_builder.insert_smulsat(signed_max_word, two);
    add_word_eq!(accumulator, saturated, signed_max);

    let saturated = function_builder.insert_smulsat(signed_min_word, two);
    add_word_eq!(accumulator, saturated, signed_min);

    function_builder
        .insert_inst_no_result(control_flow::Return::new_single(instructions, accumulator));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("i256 checked operations should compile");
    let address = artifact.function_address("i256_checked_ops").unwrap();
    let function: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 27);
}

#[test]
fn scalar_integer_edge_ops_match_semantics() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let function = builder
        .declare_function(Signature::new_single(
            "scalar_integer_edge_ops",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);

    let ten = function_builder.make_imm_value(10i64);
    let three = function_builder.make_imm_value(3i64);
    let negative_ten = function_builder.make_imm_value(-10i64);
    let unsigned_remainder =
        function_builder.insert_inst(arith::Umod::new(instructions, ten, three), Type::I64);
    let signed_remainder = function_builder.insert_inst(
        arith::Smod::new(instructions, negative_ten, three),
        Type::I64,
    );

    let maximum = function_builder.make_imm_value(i32::MAX);
    let minimum = function_builder.make_imm_value(i32::MIN);
    let all_ones = function_builder.make_imm_value(-1i32);
    let one = function_builder.make_imm_value(1i32);
    let two = function_builder.make_imm_value(2i32);
    let zero = function_builder.make_imm_value(0i32);
    let [_, uadd_overflow] = function_builder.insert_uaddo(all_ones, one);
    let [_, sadd_overflow] = function_builder.insert_saddo(maximum, one);
    let [_, usub_overflow] = function_builder.insert_usubo(zero, one);
    let [_, ssub_overflow] = function_builder.insert_ssubo(minimum, one);
    let [_, umul_overflow] = function_builder.insert_umulo(all_ones, two);
    let [_, smul_overflow] = function_builder.insert_smulo(maximum, two);
    let [_, neg_overflow] = function_builder.insert_snego(minimum);

    let negative_six = function_builder.make_imm_value(-6i32);
    let ten = function_builder.make_imm_value(10i32);
    let five = function_builder.make_imm_value(5i32);
    let sixty_five_thousand = function_builder.make_imm_value(65_536i32);
    let unsigned_add = function_builder.insert_uaddsat(negative_six, ten);
    let signed_add = function_builder.insert_saddsat(maximum, one);
    let unsigned_sub = function_builder.insert_usubsat(five, ten);
    let signed_sub = function_builder.insert_ssubsat(minimum, one);
    let unsigned_mul = function_builder.insert_umulsat(sixty_five_thousand, sixty_five_thousand);
    let signed_mul_high = function_builder.insert_smulsat(maximum, two);
    let signed_mul_low = function_builder.insert_smulsat(minimum, two);

    let mut accumulator = function_builder.insert_inst(
        arith::Add::new(instructions, unsigned_remainder, signed_remainder),
        Type::I64,
    );
    for value in [
        uadd_overflow,
        sadd_overflow,
        usub_overflow,
        ssub_overflow,
        umul_overflow,
        smul_overflow,
        neg_overflow,
    ] {
        let value = function_builder
            .insert_inst(cast::Zext::new(instructions, value, Type::I64), Type::I64);
        accumulator = function_builder
            .insert_inst(arith::Add::new(instructions, accumulator, value), Type::I64);
    }
    for value in [unsigned_add, unsigned_sub, unsigned_mul] {
        let value = function_builder
            .insert_inst(cast::Zext::new(instructions, value, Type::I64), Type::I64);
        accumulator = function_builder
            .insert_inst(arith::Add::new(instructions, accumulator, value), Type::I64);
    }
    for value in [signed_add, signed_sub, signed_mul_high, signed_mul_low] {
        let value = function_builder
            .insert_inst(cast::Sext::new(instructions, value, Type::I64), Type::I64);
        accumulator = function_builder
            .insert_inst(arith::Add::new(instructions, accumulator, value), Type::I64);
    }
    function_builder
        .insert_inst_no_result(control_flow::Return::new_single(instructions, accumulator));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("scalar integer edge operations should compile");
    let address = artifact
        .function_address("scalar_integer_edge_ops")
        .unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 8_589_934_595);
}

#[test]
fn i256_allocas_follow_native_alignment() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let pointer_type = builder.ptr_type(Type::I256);
    let function = builder
        .declare_function(Signature::new_single(
            "i256_alloca_alignment",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let pointer =
        function_builder.insert_inst(data::Alloca::new(instructions, Type::I256), pointer_type);
    let address = function_builder.insert_inst(
        cast::PtrToInt::new(instructions, pointer, Type::I64),
        Type::I64,
    );
    let alignment_mask = function_builder.make_imm_value(15i64);
    let remainder = function_builder.insert_inst(
        logic::And::new(instructions, address, alignment_mask),
        Type::I64,
    );
    function_builder
        .insert_inst_no_result(control_flow::Return::new_single(instructions, remainder));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("aligned i256 alloca should compile");
    let address = artifact.function_address("i256_alloca_alignment").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 0);
}

#[test]
fn i256_call_results_do_not_alias_the_callee_stack() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let make = builder
        .declare_function(Signature::new_single(
            "make_i256",
            Linkage::Private,
            &[Type::I32],
            Type::I256,
        ))
        .unwrap();
    let caller = builder
        .declare_function(Signature::new_single(
            "first_i256_result",
            Linkage::Public,
            &[],
            Type::I32,
        ))
        .unwrap();

    {
        let mut function_builder = builder.func_builder::<InstInserter>(make);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let value = function_builder.insert_inst(
            cast::Zext::new(instructions, function_builder.args()[0], Type::I256),
            Type::I256,
        );
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, value));
        function_builder.seal_all();
        function_builder.finish();
    }

    {
        let mut function_builder = builder.func_builder::<InstInserter>(caller);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let first_arg = function_builder.make_imm_value(1i32);
        let first = function_builder.insert_inst(
            control_flow::Call::new(instructions, make, smallvec::smallvec![first_arg]),
            Type::I256,
        );
        for value in [2i32, 3, 4, 5] {
            let argument = function_builder.make_imm_value(value);
            function_builder.insert_inst(
                control_flow::Call::new(instructions, make, smallvec::smallvec![argument]),
                Type::I256,
            );
        }
        let first = function_builder
            .insert_inst(cast::Trunc::new(instructions, first, Type::I32), Type::I32);
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, first));
        function_builder.seal_all();
        function_builder.finish();
    }

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("indirect i256 returns should compile");
    let address = artifact.function_address("first_i256_result").unwrap();
    let function: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 1);
}

#[test]
fn object_load_snapshots_i256_values() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let object_ref_type = builder.objref_type(Type::I256);
    let function = builder
        .declare_function(Signature::new_single(
            "obj_load_i256_snapshot",
            Linkage::Public,
            &[],
            Type::I32,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let object = function_builder.insert_inst(
        data::ObjAlloc::new(instructions, Type::I256),
        object_ref_type,
    );
    let initial =
        function_builder.make_imm_value(Immediate::from_i256(I256::from(123u8), Type::I256));
    function_builder.insert_inst_no_result(data::ObjStore::new(instructions, object, initial));
    let loaded = function_builder.insert_inst(data::ObjLoad::new(instructions, object), Type::I256);
    let replacement =
        function_builder.make_imm_value(Immediate::from_i256(I256::from(45u8), Type::I256));
    function_builder.insert_inst_no_result(data::ObjStore::new(instructions, object, replacement));
    let matches =
        function_builder.insert_inst(cmp::Eq::new(instructions, loaded, initial), Type::I1);
    let result =
        function_builder.insert_inst(cast::Zext::new(instructions, matches, Type::I32), Type::I32);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, result));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("i256 object load should compile");
    let address = artifact.function_address("obj_load_i256_snapshot").unwrap();
    let function: unsafe extern "C" fn() -> i32 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 1);
}

#[test]
fn aggregate_memory_ops_copy_complete_values() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let array_type = builder.declare_array_type(Type::I64, 5);
    let pointer_type = builder.ptr_type(array_type);
    let element_pointer_type = builder.ptr_type(Type::I64);
    let function = builder
        .declare_function(Signature::new_single(
            "aggregate_memory_copy",
            Linkage::Public,
            &[pointer_type],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let target = function_builder.args()[0];
    let loaded = function_builder.insert_inst(
        data::Mload::new(instructions, target, array_type),
        array_type,
    );
    let last_index = function_builder.make_imm_value(4i64);
    let loaded_last = function_builder.insert_inst(
        data::ExtractValue::new(instructions, loaded, last_index),
        Type::I64,
    );
    let zero = function_builder.make_imm_value(0i64);
    let target_last = function_builder.insert_inst(
        data::Gep::new(instructions, smallvec::smallvec![target, zero, last_index]),
        element_pointer_type,
    );
    let ninety_nine = function_builder.make_imm_value(99i64);
    function_builder.insert_inst_no_result(data::Mstore::new(
        instructions,
        target_last,
        ninety_nine,
        Type::I64,
    ));

    let mut value = function_builder.make_undef_value(array_type);
    for (index, element) in [11i64, 22, 33, 44, 55].into_iter().enumerate() {
        let index = function_builder.make_imm_value(index as i64);
        let element = function_builder.make_imm_value(element);
        value = function_builder.insert_inst(
            data::InsertValue::new(instructions, value, index, element),
            array_type,
        );
    }
    function_builder.insert_inst_no_result(data::Mstore::new(
        instructions,
        target,
        value,
        array_type,
    ));
    let stored_last = function_builder.insert_inst(
        data::Mload::new(instructions, target_last, Type::I64),
        Type::I64,
    );
    let result = function_builder.insert_inst(
        arith::Add::new(instructions, loaded_last, stored_last),
        Type::I64,
    );
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, result));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("aggregate memory operations should compile");
    let address = artifact.function_address("aggregate_memory_copy").unwrap();
    let function: unsafe extern "C" fn(*mut i64) -> i64 = unsafe { std::mem::transmute(address) };
    let mut target = [0, 0, 0, 0, 55];
    assert_eq!(unsafe { function(target.as_mut_ptr()) }, 110);
    assert_eq!(target, [11, 22, 33, 44, 55]);
}

#[test]
fn aggregate_returns_copy_the_complete_value() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let aggregate_type = builder.declare_struct_type("WideReturn", &[Type::I256, Type::I64], false);
    let make = builder
        .declare_function(Signature::new_single(
            "make_wide_return",
            Linkage::Private,
            &[],
            aggregate_type,
        ))
        .unwrap();
    let read = builder
        .declare_function(Signature::new_single(
            "read_wide_return_tail",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();

    {
        let mut function_builder = builder.func_builder::<InstInserter>(make);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let mut value = function_builder.make_undef_value(aggregate_type);
        let head_index = function_builder.make_imm_value(0i8);
        let head =
            function_builder.make_imm_value(Immediate::from_i256(I256::from(17u8), Type::I256));
        value = function_builder.insert_inst(
            data::InsertValue::new(instructions, value, head_index, head),
            aggregate_type,
        );
        let tail_index = function_builder.make_imm_value(1i8);
        let tail = function_builder.make_imm_value(29i64);
        value = function_builder.insert_inst(
            data::InsertValue::new(instructions, value, tail_index, tail),
            aggregate_type,
        );
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, value));
        function_builder.seal_all();
        function_builder.finish();
    }

    {
        let mut function_builder = builder.func_builder::<InstInserter>(read);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let value = function_builder.insert_inst(
            control_flow::Call::new(instructions, make, smallvec::smallvec![]),
            aggregate_type,
        );
        let tail_index = function_builder.make_imm_value(1i8);
        let tail = function_builder.insert_inst(
            data::ExtractValue::new(instructions, value, tail_index),
            Type::I64,
        );
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, tail));
        function_builder.seal_all();
        function_builder.finish();
    }

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("aggregate returns should compile");
    let address = artifact.function_address("read_wide_return_tail").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 29);
}

#[test]
fn constant_struct_projection_uses_native_field_offsets() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let struct_type = builder.declare_struct_type("AlignedConstant", &[Type::I8, Type::I64], false);
    let global = builder.declare_gv(GlobalVariableData::constant(
        "ALIGNED_CONSTANT".to_string(),
        struct_type,
        Linkage::Private,
        GvInitializer::make_struct(vec![
            GvInitializer::make_imm(7i8),
            GvInitializer::make_imm(29i64),
        ]),
    ));
    let struct_ref_type = builder.constref_type(struct_type);
    let field_ref_type = builder.constref_type(Type::I64);
    let function = builder
        .declare_function(Signature::new_single(
            "read_aligned_constant",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let value = function_builder.insert_inst(
        data::ConstRef::new(instructions, global.into()),
        struct_ref_type,
    );
    let field_index = function_builder.make_imm_value(1i8);
    let field = function_builder.insert_inst(
        data::ConstProj::new(instructions, smallvec::smallvec![value, field_index]),
        field_ref_type,
    );
    let field = function_builder.insert_inst(data::ConstLoad::new(instructions, field), Type::I64);
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, field));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("constant struct projection should compile");
    let address = artifact.function_address("read_aligned_constant").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 29);
}

#[test]
fn returned_constant_references_use_caller_owned_storage() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let array_type = builder.declare_array_type(Type::I64, 2);
    let array_ref_type = builder.constref_type(array_type);
    let element_ref_type = builder.constref_type(Type::I64);
    let expected = builder.declare_gv(GlobalVariableData::constant(
        "RETURNED_CONSTANT".to_string(),
        array_type,
        Linkage::Private,
        GvInitializer::make_array(vec![
            GvInitializer::make_imm(17i64),
            GvInitializer::make_imm(29i64),
        ]),
    ));
    let replacement = builder.declare_gv(GlobalVariableData::constant(
        "CLOBBER_CONSTANT".to_string(),
        array_type,
        Linkage::Private,
        GvInitializer::make_array(vec![
            GvInitializer::make_imm(998i64),
            GvInitializer::make_imm(999i64),
        ]),
    ));
    let get = builder
        .declare_function(Signature::new_single(
            "get_constant_ref",
            Linkage::Private,
            &[],
            array_ref_type,
        ))
        .unwrap();
    let clobber = builder
        .declare_function(Signature::new_single(
            "clobber_constant_stack",
            Linkage::Private,
            &[],
            Type::I64,
        ))
        .unwrap();
    let read = builder
        .declare_function(Signature::new_single(
            "read_returned_constant",
            Linkage::Public,
            &[],
            Type::I64,
        ))
        .unwrap();

    {
        let mut function_builder = builder.func_builder::<InstInserter>(get);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let value = function_builder.insert_inst(
            data::ConstRef::new(instructions, expected.into()),
            array_ref_type,
        );
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, value));
        function_builder.seal_all();
        function_builder.finish();
    }

    {
        let mut function_builder = builder.func_builder::<InstInserter>(clobber);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let value = function_builder.insert_inst(
            data::ConstRef::new(instructions, replacement.into()),
            array_ref_type,
        );
        let index = function_builder.make_imm_value(1i8);
        let value = function_builder.insert_inst(
            data::ConstIndex::new(instructions, value, index),
            element_ref_type,
        );
        let value =
            function_builder.insert_inst(data::ConstLoad::new(instructions, value), Type::I64);
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, value));
        function_builder.seal_all();
        function_builder.finish();
    }

    {
        let mut function_builder = builder.func_builder::<InstInserter>(read);
        let entry = function_builder.append_block();
        function_builder.switch_to_block(entry);
        let value = function_builder.insert_inst(
            control_flow::Call::new(instructions, get, smallvec::smallvec![]),
            array_ref_type,
        );
        function_builder.insert_inst(
            control_flow::Call::new(instructions, clobber, smallvec::smallvec![]),
            Type::I64,
        );
        let index = function_builder.make_imm_value(1i8);
        let value = function_builder.insert_inst(
            data::ConstIndex::new(instructions, value, index),
            element_ref_type,
        );
        let value =
            function_builder.insert_inst(data::ConstLoad::new(instructions, value), Type::I64);
        function_builder
            .insert_inst_no_result(control_flow::Return::new_single(instructions, value));
        function_builder.seal_all();
        function_builder.finish();
    }

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("returned constant reference should compile");
    let address = artifact.function_address("read_returned_constant").unwrap();
    let function: unsafe extern "C" fn() -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function() }, 29);
}

#[test]
fn object_and_constant_indices_accept_narrow_integers() {
    let isa = native_isa();
    let instructions = isa.inst_set();
    let builder = ModuleBuilder::new(ModuleCtx::new(&isa));
    let array_type = builder.declare_array_type(Type::I64, 2);
    let global = builder.declare_gv(GlobalVariableData::constant(
        "INDEX_VALUES".to_string(),
        array_type,
        Linkage::Private,
        GvInitializer::make_array(vec![
            GvInitializer::make_imm(11i64),
            GvInitializer::make_imm(31i64),
        ]),
    ));
    let const_array_ref_type = builder.constref_type(array_type);
    let const_element_ref_type = builder.constref_type(Type::I64);
    let object_array_ref_type = builder.objref_type(array_type);
    let object_element_ref_type = builder.objref_type(Type::I64);
    let function = builder
        .declare_function(Signature::new_single(
            "index_with_i32",
            Linkage::Public,
            &[Type::I32],
            Type::I64,
        ))
        .unwrap();
    let mut function_builder = builder.func_builder::<InstInserter>(function);
    let entry = function_builder.append_block();
    function_builder.switch_to_block(entry);
    let index = function_builder.args()[0];
    let constant = function_builder.insert_inst(
        data::ConstRef::new(instructions, global.into()),
        const_array_ref_type,
    );
    let constant_element = function_builder.insert_inst(
        data::ConstIndex::new(instructions, constant, index),
        const_element_ref_type,
    );
    let constant_value = function_builder.insert_inst(
        data::ConstLoad::new(instructions, constant_element),
        Type::I64,
    );
    let object = function_builder.insert_inst(
        data::ObjAlloc::new(instructions, array_type),
        object_array_ref_type,
    );
    function_builder.insert_inst_no_result(data::ObjInitConst::new(instructions, object, constant));
    let object_element = function_builder.insert_inst(
        data::ObjIndex::new(instructions, object, index),
        object_element_ref_type,
    );
    let object_value =
        function_builder.insert_inst(data::ObjLoad::new(instructions, object_element), Type::I64);
    let sum = function_builder.insert_inst(
        arith::Add::new(instructions, constant_value, object_value),
        Type::I64,
    );
    function_builder.insert_inst_no_result(control_flow::Return::new_single(instructions, sum));
    function_builder.seal_all();
    function_builder.finish();

    let artifact = Compile::new(builder.build(), CraneliftJitBackend::new())
        .compile()
        .expect("narrow object and constant indices should compile");
    let address = artifact.function_address("index_with_i32").unwrap();
    let function: unsafe extern "C" fn(i32) -> i64 = unsafe { std::mem::transmute(address) };
    assert_eq!(unsafe { function(1) }, 62);
}
