use sonatina_codegen::Backend;
use sonatina_codegen::isa::spirv::SpirvBackend;
use sonatina_ir::{
    Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::control_flow,
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
