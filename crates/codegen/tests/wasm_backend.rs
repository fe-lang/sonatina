use sonatina_codegen::Backend;
use sonatina_codegen::isa::wasm::WasmBackend;
use sonatina_ir::{
    Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::{arith, cmp, control_flow},
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
        panic!("unsupported host architecture");
    };
    TargetTriple::new(arch, Vendor::Unknown, OperatingSystem::Native)
}

fn native_module_builder() -> ModuleBuilder {
    let isa = Native::new(native_triple());
    let ctx = ModuleCtx::new(&isa);
    ModuleBuilder::new(ctx)
}

#[test]
fn wasm_add_two_i64s_wasmtime() {
    let isa = Native::new(native_triple());
    let is = isa.inst_set();
    let mb = native_module_builder();

    let sig = Signature::new_single("add_i64", Linkage::Public, &[Type::I64, Type::I64], Type::I64);
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
    let backend = WasmBackend::new();
    let artifact = backend.compile_module(&module).expect("WASM compilation failed");

    // Validate WASM
    wasmparser::validate(&artifact.bytes).expect("produced invalid WASM");

    // Execute via wasmtime
    let engine = wasmtime::Engine::default();
    let wasm_module = wasmtime::Module::new(&engine, &artifact.bytes)
        .expect("wasmtime should load the WASM module");
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &wasm_module, &[])
        .expect("wasmtime should instantiate the module");

    let add_fn = instance
        .get_typed_func::<(i64, i64), i64>(&mut store, "add_i64")
        .expect("add_i64 export should exist");

    let result = add_fn.call(&mut store, (3, 4)).expect("call should succeed");
    assert_eq!(result, 7);

    let result = add_fn.call(&mut store, (100, 200)).expect("call should succeed");
    assert_eq!(result, 300);
}

#[test]
fn wasm_arithmetic_chain_wasmtime() {
    let isa = Native::new(native_triple());
    let is = isa.inst_set();
    let mb = native_module_builder();

    // f(a, b) = (a + b) * (a - b)
    let sig = Signature::new_single("arith", Linkage::Public, &[Type::I64, Type::I64], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    let a = fb.args()[0];
    let b = fb.args()[1];
    let sum = fb.insert_inst(arith::Add::new(is, a, b), Type::I64);
    let diff = fb.insert_inst(arith::Sub::new(is, a, b), Type::I64);
    let product = fb.insert_inst(arith::Mul::new(is, sum, diff), Type::I64);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, product));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = WasmBackend::new();
    let artifact = backend.compile_module(&module).expect("WASM compilation failed");

    wasmparser::validate(&artifact.bytes).expect("produced invalid WASM");

    let engine = wasmtime::Engine::default();
    let wasm_module = wasmtime::Module::new(&engine, &artifact.bytes)
        .expect("wasmtime should load the module");
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &wasm_module, &[])
        .expect("wasmtime should instantiate");

    let f = instance
        .get_typed_func::<(i64, i64), i64>(&mut store, "arith")
        .expect("arith export");

    // (5+3) * (5-3) = 16
    assert_eq!(f.call(&mut store, (5, 3)).unwrap(), 16);
    // (10+7) * (10-7) = 51
    assert_eq!(f.call(&mut store, (10, 7)).unwrap(), 51);
}

#[test]
fn wasm_constant_return_wasmtime() {
    let isa = Native::new(native_triple());
    let is = isa.inst_set();
    let mb = native_module_builder();

    let sig = Signature::new_single("the_answer", Linkage::Public, &[], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    let val = fb.make_imm_value(42i64);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, val));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = WasmBackend::new();
    let artifact = backend.compile_module(&module).expect("WASM compilation failed");

    wasmparser::validate(&artifact.bytes).expect("invalid WASM");

    let engine = wasmtime::Engine::default();
    let wasm_module = wasmtime::Module::new(&engine, &artifact.bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &wasm_module, &[]).unwrap();

    let f = instance
        .get_typed_func::<(), i64>(&mut store, "the_answer")
        .expect("the_answer export");

    assert_eq!(f.call(&mut store, ()).unwrap(), 42);
}

#[test]
fn wasm_loop_sum_wasmtime() {
    let isa = Native::new(native_triple());
    let is = isa.inst_set();
    let mb = native_module_builder();

    // fn sum_to(n: i64) -> i64 { let mut acc=0, i=0; while i<n { acc+=i; i++; } return acc; }
    let sig = Signature::new_single("sum_to", Linkage::Public, &[Type::I64], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    let loop_header = fb.append_block();
    let loop_body = fb.append_block();
    let exit = fb.append_block();

    fb.switch_to_block(entry);
    let n = fb.args()[0];
    let init_acc = fb.make_imm_value(0i64);
    let init_i = fb.make_imm_value(0i64);
    fb.insert_inst_no_result(control_flow::Jump::new(is, loop_header));

    fb.switch_to_block(loop_header);
    let acc = fb.insert_inst(control_flow::Phi::new(is, vec![(init_acc, entry)]), Type::I64);
    let i = fb.insert_inst(control_flow::Phi::new(is, vec![(init_i, entry)]), Type::I64);
    let cond = fb.insert_inst(cmp::Lt::new(is, i, n), Type::I1);
    fb.insert_inst_no_result(control_flow::Br::new(is, cond, loop_body, exit));

    fb.switch_to_block(loop_body);
    let new_acc = fb.insert_inst(arith::Add::new(is, acc, i), Type::I64);
    let one = fb.make_imm_value(1i64);
    let new_i = fb.insert_inst(arith::Add::new(is, i, one), Type::I64);
    fb.append_phi_arg(acc, new_acc, loop_body);
    fb.append_phi_arg(i, new_i, loop_body);
    fb.insert_inst_no_result(control_flow::Jump::new(is, loop_header));

    fb.switch_to_block(exit);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, acc));

    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = WasmBackend::new();
    let artifact = backend.compile_module(&module).expect("WASM compilation failed");

    wasmparser::validate(&artifact.bytes).expect("invalid WASM");

    let engine = wasmtime::Engine::default();
    let wasm_module = wasmtime::Module::new(&engine, &artifact.bytes).expect("load failed");
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &wasm_module, &[]).expect("instantiate");

    let f = instance.get_typed_func::<i64, i64>(&mut store, "sum_to").expect("sum_to export");

    // sum_to(5) = 0+1+2+3+4 = 10
    let r = f.call(&mut store, 5).unwrap();
    eprintln!("sum_to(5) = {r}");
    assert_eq!(r, 10);
    assert_eq!(f.call(&mut store, 10).unwrap(), 45);
    assert_eq!(f.call(&mut store, 0).unwrap(), 0);
}

/// Poseidon-style sigma loop on WASM with known-answer verification.
/// Same computation as cranelift_poseidon_loop_with_const_array but
/// uses inline constants (WASM doesn't have ConstRef yet).
#[test]
fn wasm_poseidon_sigma_loop_wasmtime() {
    let isa = Native::new(native_triple());
    let is = isa.inst_set();
    let mb = native_module_builder();

    // fn poseidon_sigma() -> i64 {
    //   let mut acc = 1;
    //   // Round constants inline: [3, 5, 7, 11]
    //   // Round 0: acc = sigma(acc + 3) where sigma(x) = x*x + x
    //   // ... repeat for each constant
    //   // Return acc after 4 rounds
    //   for i in 0..4: acc = (acc + C[i])^2 + (acc + C[i])
    //   Using a simpler version: acc += i*i + i per round (avoids needing const array)
    // }
    // Actually, let's do the exact same computation as the Cranelift test:
    // acc=1, C=[3,5,7,11], sigma(x)=x*x+x
    // Round 0: x=1+3=4, acc=4*4+4=20
    // Round 1: x=20+5=25, acc=25*25+25=650
    // Round 2: x=650+7=657, acc=657*657+657=432306
    // Round 3: x=432306+11=432317, acc=432317*432317+432317=186898420806
    //
    // We'll build this with a loop where the "constant" is computed as a function of i.
    // C[0]=3, C[1]=5, C[2]=7, C[3]=11
    // C[i] = 2*i + 3 for i=0,1,2 but C[3]=11 != 2*3+3=9
    // So we can't use a simple formula. Instead, use 4 unrolled iterations.

    let sig = Signature::new_single("poseidon_sigma", Linkage::Public, &[], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();
    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    // Unrolled 4 rounds with inline constants
    let mut acc = fb.make_imm_value(1i64);
    for c_val in [3i64, 5, 7, 11] {
        let c = fb.make_imm_value(c_val);
        let sum = fb.insert_inst(arith::Add::new(is, acc, c), Type::I64);
        let sq = fb.insert_inst(arith::Mul::new(is, sum, sum), Type::I64);
        acc = fb.insert_inst(arith::Add::new(is, sq, sum), Type::I64);
    }
    fb.insert_inst_no_result(control_flow::Return::new_single(is, acc));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = WasmBackend::new();
    let artifact = backend.compile_module(&module).expect("WASM compilation failed");
    wasmparser::validate(&artifact.bytes).expect("invalid WASM");

    let engine = wasmtime::Engine::default();
    let wasm_module = wasmtime::Module::new(&engine, &artifact.bytes).expect("load");
    let mut store = wasmtime::Store::new(&engine, ());
    let instance = wasmtime::Instance::new(&mut store, &wasm_module, &[]).expect("instantiate");
    let f = instance.get_typed_func::<(), i64>(&mut store, "poseidon_sigma").expect("export");

    let result = f.call(&mut store, ()).unwrap();
    assert_eq!(result, 186898420806, "WASM Poseidon sigma should match Cranelift known answer");
}

/// Cross-target loop known-answer: same loop IR → Cranelift + WASM, compare.
#[test]
fn cross_target_loop_cranelift_vs_wasm() {
    use sonatina_codegen::isa::cranelift::CraneliftBackend;

    let isa = Native::new(native_triple());
    let is = isa.inst_set();
    let mb = native_module_builder();

    // sum_to(n) with loop — same IR compiled to both backends
    let sig = Signature::new_single("sum_to", Linkage::Public, &[Type::I64], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();
    let mut fb = mb.func_builder::<InstInserter>(func_ref);

    let entry = fb.append_block();
    let loop_header = fb.append_block();
    let loop_body = fb.append_block();
    let exit = fb.append_block();

    fb.switch_to_block(entry);
    let n = fb.args()[0];
    let init_acc = fb.make_imm_value(0i64);
    let init_i = fb.make_imm_value(0i64);
    fb.insert_inst_no_result(control_flow::Jump::new(is, loop_header));

    fb.switch_to_block(loop_header);
    let acc = fb.insert_inst(control_flow::Phi::new(is, vec![(init_acc, entry)]), Type::I64);
    let i = fb.insert_inst(control_flow::Phi::new(is, vec![(init_i, entry)]), Type::I64);
    let cond = fb.insert_inst(cmp::Lt::new(is, i, n), Type::I1);
    fb.insert_inst_no_result(control_flow::Br::new(is, cond, loop_body, exit));

    fb.switch_to_block(loop_body);
    let new_acc = fb.insert_inst(arith::Add::new(is, acc, i), Type::I64);
    let one = fb.make_imm_value(1i64);
    let new_i = fb.insert_inst(arith::Add::new(is, i, one), Type::I64);
    fb.append_phi_arg(acc, new_acc, loop_body);
    fb.append_phi_arg(i, new_i, loop_body);
    fb.insert_inst_no_result(control_flow::Jump::new(is, loop_header));

    fb.switch_to_block(exit);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, acc));
    fb.seal_all();
    fb.finish();

    let module = mb.build();

    // Cranelift
    let cl = CraneliftBackend::new();
    let cl_art = cl.compile_module(&module).expect("cranelift");
    let cl_fn: fn(i64) -> i64 = unsafe {
        std::mem::transmute(cl_art.get_func_ptr::<fn(i64) -> i64>("sum_to").unwrap())
    };

    // WASM
    let wasm = WasmBackend::new();
    let wasm_art = wasm.compile_module(&module).expect("wasm");
    wasmparser::validate(&wasm_art.bytes).expect("invalid");
    let engine = wasmtime::Engine::default();
    let wm = wasmtime::Module::new(&engine, &wasm_art.bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let inst = wasmtime::Instance::new(&mut store, &wm, &[]).unwrap();
    let wasm_fn = inst.get_typed_func::<i64, i64>(&mut store, "sum_to").unwrap();

    for n in [0, 1, 5, 10, 100] {
        let cl_result = cl_fn(n);
        let wasm_result = wasm_fn.call(&mut store, n).unwrap();
        assert_eq!(cl_result, wasm_result, "Cranelift vs WASM for sum_to({n})");
        assert_eq!(cl_result, n * (n - 1) / 2, "sum_to({n}) formula check");
    }
}
