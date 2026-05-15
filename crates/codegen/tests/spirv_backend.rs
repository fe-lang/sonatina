use sonatina_codegen::Backend;
use sonatina_codegen::isa::spirv::SpirvBackend;
use sonatina_ir::{
    Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::{arith, control_flow},
    isa::{Isa, native::Native},
    module::ModuleCtx,
};
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

fn native_module_builder() -> ModuleBuilder {
    let arch = if cfg!(target_arch = "x86_64") {
        Architecture::X86_64
    } else {
        Architecture::Aarch64
    };
    let triple = TargetTriple::new(arch, Vendor::Unknown, OperatingSystem::Native);
    let isa = Native::new(triple);
    let ctx = ModuleCtx::new(&isa);
    ModuleBuilder::new(ctx)
}

#[test]
fn spirv_constant_return_valid() {
    let isa = Native::new(TargetTriple::new(
        Architecture::X86_64, Vendor::Unknown, OperatingSystem::Native
    ));
    let is = isa.inst_set();
    let mb = native_module_builder();

    let sig = Signature::new_single("compute", Linkage::Public, &[], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    let val = fb.make_imm_value(42i64);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, val));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = SpirvBackend::new();
    let artifact = backend.compile_module(&module).expect("SPIR-V compilation failed");

    // Basic structural validation: check magic number
    assert!(artifact.words.len() > 5, "SPIR-V module too small");
    assert_eq!(artifact.words[0], 0x07230203, "wrong SPIR-V magic number");

    let bytes = artifact.as_bytes();
    eprintln!("SPIR-V module: {} words, {} bytes", artifact.words.len(), bytes.len());

    // Validate with spirv-val if available
    let tmp = std::env::temp_dir().join("test_spirv.spv");
    std::fs::write(&tmp, &bytes).unwrap();
    let result = std::process::Command::new("spirv-val")
        .arg(tmp.to_str().unwrap())
        .output();
    match result {
        Ok(output) => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            if !stderr.is_empty() { eprintln!("spirv-val stderr: {stderr}"); }
            if !stdout.is_empty() { eprintln!("spirv-val stdout: {stdout}"); }
            assert!(output.status.success(), "spirv-val validation failed");
        }
        Err(_) => {
            eprintln!("spirv-val not found — skipping validation (structural check passed)");
        }
    }
    let _ = std::fs::remove_file(&tmp);
}

#[test]
fn spirv_arithmetic_return_valid() {
    let isa = Native::new(TargetTriple::new(
        Architecture::X86_64, Vendor::Unknown, OperatingSystem::Native
    ));
    let is = isa.inst_set();
    let mb = native_module_builder();

    // f() -> i64 { return 100 }
    let sig = Signature::new_single("arithmetic", Linkage::Public, &[], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();

    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

    let val = fb.make_imm_value(100i64);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, val));
    fb.seal_all();
    fb.finish();

    let module = mb.build();
    let backend = SpirvBackend::new().with_workgroup_size(1, 1, 1);
    let artifact = backend.compile_module(&module).expect("SPIR-V compilation failed");

    assert_eq!(artifact.words[0], 0x07230203);
    eprintln!("SPIR-V arithmetic module: {} words", artifact.words.len());
}

#[test]
fn spirv_poseidon_sigma_valid() {
    let isa = Native::new(TargetTriple::new(
        Architecture::X86_64, Vendor::Unknown, OperatingSystem::Native
    ));
    let is = isa.inst_set();
    let mb = native_module_builder();

    // Same Poseidon sigma computation as Cranelift and WASM tests:
    // acc=1, C=[3,5,7,11], sigma(x)=x*x+x, 4 rounds unrolled
    let sig = Signature::new_single("poseidon_sigma", Linkage::Public, &[], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();
    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

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
    let backend = SpirvBackend::new().with_workgroup_size(1, 1, 1);
    let artifact = backend.compile_module(&module).expect("SPIR-V compilation failed");

    assert_eq!(artifact.words[0], 0x07230203, "SPIR-V magic");
    eprintln!("SPIR-V Poseidon module: {} words", artifact.words.len());

    // Validate with spirv-val
    let tmp = std::env::temp_dir().join("poseidon_spirv.spv");
    std::fs::write(&tmp, artifact.as_bytes()).unwrap();
    if let Ok(output) = std::process::Command::new("spirv-val").arg(tmp.to_str().unwrap()).output() {
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprintln!("spirv-val: {stderr}");
        }
        assert!(output.status.success(), "SPIR-V Poseidon should validate");
    }
    let _ = std::fs::remove_file(&tmp);
}

/// Three-backend Poseidon known-answer: Cranelift executes, WASM executes,
/// SPIR-V validates. All use the same computation.
#[test]
fn three_backend_poseidon_known_answer() {
    use sonatina_codegen::isa::cranelift::CraneliftBackend;
    use sonatina_codegen::isa::wasm::WasmBackend;

    let isa = Native::new(TargetTriple::new(
        Architecture::X86_64, Vendor::Unknown, OperatingSystem::Native
    ));
    let is = isa.inst_set();
    let mb = native_module_builder();

    let sig = Signature::new_single("poseidon", Linkage::Public, &[], Type::I64);
    let func_ref = mb.declare_function(sig).unwrap();
    let mut fb = mb.func_builder::<InstInserter>(func_ref);
    let entry = fb.append_block();
    fb.switch_to_block(entry);

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
    let expected = 186898420806i64;

    // Cranelift execution
    let cl = CraneliftBackend::new();
    let cl_art = cl.compile_module(&module).expect("cranelift");
    let cl_fn: fn() -> i64 = unsafe {
        std::mem::transmute(cl_art.get_func_ptr::<fn() -> i64>("poseidon").unwrap())
    };
    assert_eq!(cl_fn(), expected, "Cranelift Poseidon");

    // WASM execution
    let wasm = WasmBackend::new();
    let wasm_art = wasm.compile_module(&module).expect("wasm");
    wasmparser::validate(&wasm_art.bytes).expect("invalid wasm");
    let engine = wasmtime::Engine::default();
    let wm = wasmtime::Module::new(&engine, &wasm_art.bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let inst = wasmtime::Instance::new(&mut store, &wm, &[]).unwrap();
    let wasm_fn = inst.get_typed_func::<(), i64>(&mut store, "poseidon").unwrap();
    assert_eq!(wasm_fn.call(&mut store, ()).unwrap(), expected, "WASM Poseidon");

    // SPIR-V validation (execution requires GPU)
    let spirv = SpirvBackend::new();
    let spirv_art = spirv.compile_module(&module).expect("spirv");
    assert_eq!(spirv_art.words[0], 0x07230203);
    let tmp = std::env::temp_dir().join("poseidon_3way.spv");
    std::fs::write(&tmp, spirv_art.as_bytes()).unwrap();
    if let Ok(output) = std::process::Command::new("spirv-val").arg(tmp.to_str().unwrap()).output() {
        assert!(output.status.success(), "SPIR-V Poseidon should validate");
    }
    let _ = std::fs::remove_file(&tmp);
}
