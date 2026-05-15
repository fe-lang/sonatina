use sonatina_codegen::Backend;
use sonatina_codegen::isa::wasm::WasmBackend;
use sonatina_ir::{
    Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::{arith, control_flow},
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
