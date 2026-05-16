use sonatina_codegen::{Backend, Compile, OptLevel, isa::cranelift::CraneliftBackend};
use sonatina_ir::{
    Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    global_variable::{GlobalVariableData, GvInitializer},
    inst::{arith, cmp, control_flow, data},
    isa::{Isa, native::Native},
    module::ModuleCtx,
};
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

fn native_triple() -> TargetTriple {
    let arch = if cfg!(target_arch = "x86_64") {
        Architecture::X86_64
    } else if cfg!(target_arch = "aarch64") {
        Architecture::Aarch64
    } else {
        panic!("unsupported host architecture for cranelift tests");
    };
    TargetTriple::new(arch, Vendor::Unknown, OperatingSystem::Native)
}

fn native_isa() -> Native {
    Native::new(native_triple())
}

fn native_module_builder() -> ModuleBuilder {
    let isa = native_isa();
    let ctx = ModuleCtx::new(&isa);
    ModuleBuilder::new(ctx)
}

#[test]
fn cranelift_add_two_i64s() {
    let isa = native_isa();
    let is = isa.inst_set();
    let mb = {
        let ctx = ModuleCtx::new(&isa);
        ModuleBuilder::new(ctx)
    };

    let sig = Signature::new_single(
        "add_i64",
        Linkage::Public,
        &[Type::I64, Type::I64],
        Type::I64,
    );
    let func_ref = mb.declare_function(sig).unwrap();

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    let a = fb.args()[0];
    let b = fb.args()[1];
    let sum = fb.insert_inst(arith::Add::new(is, a, b), Type::I64);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, sum));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = CraneliftBackend::new();
    let artifact = backend.compile_module(&module).expect("compilation failed");

    let add_fn: fn(i64, i64) -> i64 = unsafe {
        let ptr = artifact
            .get_func_ptr::<fn(i64, i64) -> i64>("add_i64")
            .unwrap();
        std::mem::transmute(ptr)
    };

    assert_eq!(add_fn(3, 4), 7);
    assert_eq!(add_fn(-10, 25), 15);
    assert_eq!(add_fn(0, 0), 0);
}

#[test]
fn cranelift_arithmetic_chain() {
    let isa = native_isa();
    let is = isa.inst_set();
    let mb = {
        let ctx = ModuleCtx::new(&isa);
        ModuleBuilder::new(ctx)
    };

    let sig = Signature::new_single("arith", Linkage::Public, &[Type::I32, Type::I32], Type::I32);
    let func_ref = mb.declare_function(sig).unwrap();

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    let a = fb.args()[0];
    let b = fb.args()[1];
    let sum = fb.insert_inst(arith::Add::new(is, a, b), Type::I32);
    let diff = fb.insert_inst(arith::Sub::new(is, a, b), Type::I32);
    let product = fb.insert_inst(arith::Mul::new(is, sum, diff), Type::I32);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, product));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = CraneliftBackend::new();
    let artifact = backend.compile_module(&module).expect("compilation failed");

    let f: fn(i32, i32) -> i32 = unsafe {
        let ptr = artifact
            .get_func_ptr::<fn(i32, i32) -> i32>("arith")
            .unwrap();
        std::mem::transmute(ptr)
    };

    // (5+3) * (5-3) = 8 * 2 = 16
    assert_eq!(f(5, 3), 16);
    // (10+7) * (10-7) = 17 * 3 = 51
    assert_eq!(f(10, 7), 51);
}

#[test]
fn cranelift_through_generic_compile_pipeline() {
    let isa = native_isa();
    let is = isa.inst_set();
    let mb = {
        let ctx = ModuleCtx::new(&isa);
        ModuleBuilder::new(ctx)
    };

    let sig = Signature::new_single("identity", Linkage::Public, &[Type::I64], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);
    let a = fb.args()[0];
    fb.insert_inst_no_result(control_flow::Return::new_single(is, a));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = CraneliftBackend::new();
    let compile = Compile::new(module, backend).with_opt_level(OptLevel::O0);
    let artifact = compile.compile().expect("Compile<CraneliftBackend> failed");

    let f: fn(i64) -> i64 = unsafe {
        let ptr = artifact.get_func_ptr::<fn(i64) -> i64>("identity").unwrap();
        std::mem::transmute(ptr)
    };

    assert_eq!(f(42), 42);
    assert_eq!(f(-1), -1);
}

#[test]
fn cranelift_array_index() {
    let isa = native_isa();
    let is = isa.inst_set();
    let mb = native_module_builder();

    // Build: fn get_elem(idx: i64) -> i64 {
    //   let arr: [i64; 3] = [10, 20, 30]
    //   return arr[idx]
    // }
    let sig = Signature::new_single("get_elem", Linkage::Public, &[Type::I64], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let arr_ty = mb.declare_array_type(Type::I64, 3);
    let arr_objref_ty = mb.objref_type(arr_ty);
    let elem_objref_ty = mb.objref_type(Type::I64);

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    let idx = fb.args()[0];

    // obj.alloc [i64; 3]
    let arr = fb.insert_inst(data::ObjAlloc::new(is, arr_ty), arr_objref_ty);

    // Store elements: arr[0]=10, arr[1]=20, arr[2]=30
    let imm0 = fb.make_imm_value(0i64);
    let imm1 = fb.make_imm_value(1i64);
    let imm2 = fb.make_imm_value(2i64);

    let val10 = fb.make_imm_value(10i64);
    let val20 = fb.make_imm_value(20i64);
    let val30 = fb.make_imm_value(30i64);

    let p0 = fb.insert_inst(data::ObjIndex::new(is, arr, imm0), elem_objref_ty);
    fb.insert_inst_no_result(data::ObjStore::new(is, p0, val10));

    let p1 = fb.insert_inst(data::ObjIndex::new(is, arr, imm1), elem_objref_ty);
    fb.insert_inst_no_result(data::ObjStore::new(is, p1, val20));

    let p2 = fb.insert_inst(data::ObjIndex::new(is, arr, imm2), elem_objref_ty);
    fb.insert_inst_no_result(data::ObjStore::new(is, p2, val30));

    // Dynamic index: val = arr[idx]
    let pi = fb.insert_inst(data::ObjIndex::new(is, arr, idx), elem_objref_ty);
    let val = fb.insert_inst(data::ObjLoad::new(is, pi), Type::I64);

    fb.insert_inst_no_result(control_flow::Return::new_single(is, val));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = CraneliftBackend::new();
    let artifact = backend.compile_module(&module).expect("compilation failed");

    let f: fn(i64) -> i64 = unsafe {
        let ptr = artifact.get_func_ptr::<fn(i64) -> i64>("get_elem").unwrap();
        std::mem::transmute(ptr)
    };

    assert_eq!(f(0), 10);
    assert_eq!(f(1), 20);
    assert_eq!(f(2), 30);
}

#[test]
fn cranelift_array_sum() {
    let isa = native_isa();
    let is = isa.inst_set();
    let mb = native_module_builder();

    // Build: fn sum_arr() -> i64 {
    //   let arr: [i64; 4] = [100, 200, 300, 400]
    //   return arr[0] + arr[1] + arr[2] + arr[3]
    // }
    let sig = Signature::new_single("sum_arr", Linkage::Public, &[], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let arr_ty = mb.declare_array_type(Type::I64, 4);
    let arr_objref_ty = mb.objref_type(arr_ty);
    let elem_objref_ty = mb.objref_type(Type::I64);

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    let arr = fb.insert_inst(data::ObjAlloc::new(is, arr_ty), arr_objref_ty);

    // Store 4 elements
    for (i, val) in [100i64, 200, 300, 400].iter().enumerate() {
        let idx = fb.make_imm_value(i as i64);
        let imm_val = fb.make_imm_value(*val);
        let p = fb.insert_inst(data::ObjIndex::new(is, arr, idx), elem_objref_ty);
        fb.insert_inst_no_result(data::ObjStore::new(is, p, imm_val));
    }

    // Load and sum
    let mut acc = {
        let idx = fb.make_imm_value(0i64);
        let p = fb.insert_inst(data::ObjIndex::new(is, arr, idx), elem_objref_ty);
        fb.insert_inst(data::ObjLoad::new(is, p), Type::I64)
    };
    for i in 1..4 {
        let idx = fb.make_imm_value(i as i64);
        let p = fb.insert_inst(data::ObjIndex::new(is, arr, idx), elem_objref_ty);
        let elem = fb.insert_inst(data::ObjLoad::new(is, p), Type::I64);
        acc = fb.insert_inst(arith::Add::new(is, acc, elem), Type::I64);
    }

    fb.insert_inst_no_result(control_flow::Return::new_single(is, acc));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = CraneliftBackend::new();
    let artifact = backend.compile_module(&module).expect("compilation failed");

    let f: fn() -> i64 = unsafe {
        let ptr = artifact.get_func_ptr::<fn() -> i64>("sum_arr").unwrap();
        std::mem::transmute(ptr)
    };

    assert_eq!(f(), 1000);
}

#[test]
fn cranelift_const_ref_array() {
    let isa = native_isa();
    let is = isa.inst_set();
    let mb = native_module_builder();

    // Declare a global constant array: [i64; 4] = [10, 20, 30, 40]
    let arr_ty = mb.declare_array_type(Type::I64, 4);
    let gv = mb.declare_gv(GlobalVariableData::constant(
        "ROUND_CONSTANTS".to_string(),
        arr_ty,
        Linkage::Private,
        GvInitializer::Array(vec![
            GvInitializer::Immediate(sonatina_ir::Immediate::I64(10)),
            GvInitializer::Immediate(sonatina_ir::Immediate::I64(20)),
            GvInitializer::Immediate(sonatina_ir::Immediate::I64(30)),
            GvInitializer::Immediate(sonatina_ir::Immediate::I64(40)),
        ]),
    ));

    // fn sum_consts(idx: i64) -> i64 { ROUND_CONSTANTS[idx] }
    let sig = Signature::new_single("get_const", Linkage::Public, &[Type::I64], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let constref_ty = mb.make_compound(sonatina_ir::types::CompoundType::ConstRef(arr_ty));
    let constref_type = Type::Compound(constref_ty);
    let elem_constref_ty = mb.make_compound(sonatina_ir::types::CompoundType::ConstRef(Type::I64));
    let elem_constref_type = Type::Compound(elem_constref_ty);

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    let idx = fb.args()[0];

    // const.ref → pointer to global array
    let arr_ref = fb.insert_inst(data::ConstRef::new(is, gv.into()), constref_type);
    // const.index → pointer to element
    let elem_ref = fb.insert_inst(data::ConstIndex::new(is, arr_ref, idx), elem_constref_type);
    // const.load → load the element value
    let val = fb.insert_inst(data::ConstLoad::new(is, elem_ref), Type::I64);

    fb.insert_inst_no_result(control_flow::Return::new_single(is, val));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = CraneliftBackend::new();
    let artifact = backend.compile_module(&module).expect("compilation failed");

    let f: fn(i64) -> i64 = unsafe {
        let ptr = artifact
            .get_func_ptr::<fn(i64) -> i64>("get_const")
            .unwrap();
        std::mem::transmute(ptr)
    };

    assert_eq!(f(0), 10);
    assert_eq!(f(1), 20);
    assert_eq!(f(2), 30);
    assert_eq!(f(3), 40);
}

#[test]
fn cranelift_poseidon_loop_with_const_array() {
    let isa = native_isa();
    let is = isa.inst_set();
    let mb = native_module_builder();

    // Global constant round array: [i64; 4] = [3, 5, 7, 11]
    let arr_ty = mb.declare_array_type(Type::I64, 4);
    let gv = mb.declare_gv(GlobalVariableData::constant(
        "ROUND_CONSTS".to_string(),
        arr_ty,
        Linkage::Private,
        GvInitializer::Array(vec![
            GvInitializer::Immediate(sonatina_ir::Immediate::I64(3)),
            GvInitializer::Immediate(sonatina_ir::Immediate::I64(5)),
            GvInitializer::Immediate(sonatina_ir::Immediate::I64(7)),
            GvInitializer::Immediate(sonatina_ir::Immediate::I64(11)),
        ]),
    ));

    // fn poseidon_sum() -> i64 {
    //   let C = ROUND_CONSTS;  // const array
    //   let mut acc: i64 = 1;
    //   for i in 0..4 {
    //     let c = C[i];
    //     acc = (acc + c) * (acc + c) + (acc + c);  // sigma(acc + c)
    //   }
    //   return acc;
    // }
    let sig = Signature::new_single("poseidon_sum", Linkage::Public, &[], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let constref_ty = mb.make_compound(sonatina_ir::types::CompoundType::ConstRef(arr_ty));
    let constref_type = Type::Compound(constref_ty);
    let elem_constref_ty = mb.make_compound(sonatina_ir::types::CompoundType::ConstRef(Type::I64));
    let elem_constref_type = Type::Compound(elem_constref_ty);

    let mut fb = mb.func_builder::<InstInserter>(func_ref);

    let entry = fb.append_block();
    let loop_header = fb.append_block();
    let loop_body = fb.append_block();
    let exit = fb.append_block();

    // entry: jump to loop with (acc=1, i=0)
    fb.switch_to_block(entry);
    let init_acc = fb.make_imm_value(1i64);
    let init_i = fb.make_imm_value(0i64);
    fb.insert_inst_no_result(control_flow::Jump::new(is, loop_header));

    // loop_header: phi(acc, i), check i < 4
    fb.switch_to_block(loop_header);
    let acc_phi = fb.insert_inst(
        control_flow::Phi::new(is, vec![(init_acc, entry)]),
        Type::I64,
    );
    let i_phi = fb.insert_inst(control_flow::Phi::new(is, vec![(init_i, entry)]), Type::I64);
    let four = fb.make_imm_value(4i64);
    let cond = fb.insert_inst(cmp::Lt::new(is, i_phi, four), Type::I1);
    fb.insert_inst_no_result(control_flow::Br::new(is, cond, loop_body, exit));

    // loop_body: c = C[i], sigma(acc + c), i++
    fb.switch_to_block(loop_body);
    let arr_ref = fb.insert_inst(data::ConstRef::new(is, gv.into()), constref_type);
    let elem_ref = fb.insert_inst(
        data::ConstIndex::new(is, arr_ref, i_phi),
        elem_constref_type,
    );
    let c = fb.insert_inst(data::ConstLoad::new(is, elem_ref), Type::I64);
    let sum = fb.insert_inst(arith::Add::new(is, acc_phi, c), Type::I64);
    let sq = fb.insert_inst(arith::Mul::new(is, sum, sum), Type::I64);
    let new_acc = fb.insert_inst(arith::Add::new(is, sq, sum), Type::I64);
    let one = fb.make_imm_value(1i64);
    let new_i = fb.insert_inst(arith::Add::new(is, i_phi, one), Type::I64);

    // Update phis and jump back
    fb.append_phi_arg(acc_phi, new_acc, loop_body);
    fb.append_phi_arg(i_phi, new_i, loop_body);
    fb.insert_inst_no_result(control_flow::Jump::new(is, loop_header));

    // exit: return acc
    fb.switch_to_block(exit);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, acc_phi));

    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = CraneliftBackend::new();
    let artifact = backend.compile_module(&module).expect("compilation failed");

    let f: fn() -> i64 = unsafe {
        let ptr = artifact
            .get_func_ptr::<fn() -> i64>("poseidon_sum")
            .unwrap();
        std::mem::transmute(ptr)
    };

    // Manual computation:
    // i=0: acc=1, c=3, sum=4, sq=16, new_acc=20
    // i=1: acc=20, c=5, sum=25, sq=625, new_acc=650
    // i=2: acc=650, c=7, sum=657, sq=431649, new_acc=432306
    // i=3: acc=432306, c=11, sum=432317, sq=186897988489, new_acc=186898420806
    let result = f();
    assert_eq!(result, 186898420806, "poseidon_sum with const array rounds");
}
