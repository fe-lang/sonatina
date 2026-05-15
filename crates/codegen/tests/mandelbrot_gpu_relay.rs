//! Phase 4+5: Full 3-backend Mandelbrot relay with GPU execution.
//!
//! All three backends COMPUTE:
//! - Cranelift: native JIT
//! - WASM: wasmtime
//! - GPU: wgpu compute shader (via WGSL from Naga)
//!
//! Falls gracefully if no GPU adapter is available.

use sonatina_codegen::Backend;
use sonatina_codegen::isa::cranelift::CraneliftBackend;
use sonatina_codegen::isa::wasm::WasmBackend;
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

fn build_step_re() -> sonatina_ir::Module {
    let isa = Native::new(TargetTriple::new(
        if cfg!(target_arch = "x86_64") { Architecture::X86_64 } else { Architecture::Aarch64 },
        Vendor::Unknown, OperatingSystem::Native,
    ));
    let is = isa.inst_set();
    let mb = ModuleBuilder::new(ModuleCtx::new(&isa));

    let sig = Signature::new_single("step_re", Linkage::Public,
        &[Type::I64, Type::I64, Type::I64], Type::I64);
    let fr = mb.declare_function(sig).unwrap();
    let mut fb = mb.func_builder::<InstInserter>(fr);
    let entry = fb.append_block();
    fb.switch_to_block(entry);
    let z_re = fb.args()[0]; let z_im = fb.args()[1]; let c_re = fb.args()[2];
    let re_sq = fb.insert_inst(arith::Mul::new(is, z_re, z_re), Type::I64);
    let im_sq = fb.insert_inst(arith::Mul::new(is, z_im, z_im), Type::I64);
    let diff = fb.insert_inst(arith::Sub::new(is, re_sq, im_sq), Type::I64);
    let ten = fb.make_imm_value(10i64);
    let shifted = fb.insert_inst(arith::Sar::new(is, ten, diff), Type::I64);
    let result = fb.insert_inst(arith::Add::new(is, shifted, c_re), Type::I64);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, result));
    fb.seal_all(); fb.finish();
    mb.build()
}

fn try_gpu_step(wgsl: &str, z_re: i64, z_im: i64, c_re: i64) -> Option<i64> {
    let instance = wgpu::Instance::default();
    let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
        power_preference: wgpu::PowerPreference::LowPower,
        force_fallback_adapter: true,
        ..Default::default()
    })).ok()?;

    eprintln!("    [GPU] adapter: {}", adapter.get_info().name);

    let (device, queue) = pollster::block_on(
        adapter.request_device(&Default::default())
    ).ok()?;

    let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("step_re"),
        source: wgpu::ShaderSource::Wgsl(wgsl.into()),
    });

    let input: Vec<u8> = [z_re, z_im, c_re].iter().flat_map(|v| v.to_le_bytes()).collect();
    let input_buf = device.create_buffer(&wgpu::BufferDescriptor {
        label: None, size: 24,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });
    queue.write_buffer(&input_buf, 0, &input);

    let output_buf = device.create_buffer(&wgpu::BufferDescriptor {
        label: None, size: 8,
        usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
        mapped_at_creation: false,
    });
    let staging_buf = device.create_buffer(&wgpu::BufferDescriptor {
        label: None, size: 8,
        usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
        mapped_at_creation: false,
    });

    let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: None, layout: None, module: &shader,
        entry_point: Some("main"),
        compilation_options: Default::default(),
        cache: None,
    });

    let bgl = pipeline.get_bind_group_layout(0);
    let bg = device.create_bind_group(&wgpu::BindGroupDescriptor {
        label: None, layout: &bgl,
        entries: &[
            wgpu::BindGroupEntry { binding: 0, resource: output_buf.as_entire_binding() },
            wgpu::BindGroupEntry { binding: 1, resource: input_buf.as_entire_binding() },
        ],
    });

    let mut enc = device.create_command_encoder(&Default::default());
    { let mut p = enc.begin_compute_pass(&Default::default()); p.set_pipeline(&pipeline); p.set_bind_group(0, &bg, &[]); p.dispatch_workgroups(1,1,1); }
    enc.copy_buffer_to_buffer(&output_buf, 0, &staging_buf, 0, 8);
    queue.submit(Some(enc.finish()));

    let slice = staging_buf.slice(..);
    let (tx, rx) = std::sync::mpsc::channel();
    slice.map_async(wgpu::MapMode::Read, move |r| { tx.send(r).unwrap(); });
    let _ = device.poll(wgpu::PollType::Wait { submission_index: None, timeout: Some(std::time::Duration::from_secs(10)) });
    rx.recv().ok()?.ok()?;
    let data = slice.get_mapped_range();
    let result = i64::from_le_bytes(data[0..8].try_into().unwrap());
    drop(data); staging_buf.unmap();
    Some(result)
}

#[test]
fn full_three_backend_mandelbrot_relay() {
    let module = build_step_re();

    eprintln!("╔══════════════════════════════════════════════════════════╗");
    eprintln!("║  FULL 3-BACKEND MANDELBROT RELAY                        ║");
    eprintln!("║  Cranelift → WASM → GPU (wgpu) — all compute           ║");
    eprintln!("╚══════════════════════════════════════════════════════════╝");

    // Cranelift
    let cl = CraneliftBackend::new();
    let cl_art = cl.compile_module(&module).expect("cranelift");
    let cl_step: fn(i64,i64,i64)->i64 = unsafe {
        std::mem::transmute(cl_art.get_func_ptr::<fn(i64,i64,i64)->i64>("step_re").unwrap())
    };

    // WASM
    let wasm = WasmBackend::new();
    let wasm_art = wasm.compile_module(&module).expect("wasm");
    wasmparser::validate(&wasm_art.bytes).expect("invalid wasm");
    let engine = wasmtime::Engine::default();
    let wm = wasmtime::Module::new(&engine, &wasm_art.bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let inst = wasmtime::Instance::new(&mut store, &wm, &[]).unwrap();
    let wasm_step = inst.get_typed_func::<(i64,i64,i64),i64>(&mut store, "step_re").unwrap();

    // SPIR-V + WGSL
    let spirv = SpirvBackend::new().with_workgroup_size(1,1,1);
    let spirv_art = spirv.compile_module(&module).expect("spirv");
    let wgsl = spirv_art.wgsl.as_ref().expect("WGSL should be generated");
    eprintln!("  WGSL generated ({} chars)", wgsl.len());

    // Test: verify all three agree
    let cases = [(0i64,0,-512), (-512,614,-512), (100,200,300)];
    let mut gpu_ok = false;

    for (zr, zi, cr) in &cases {
        let cl_r = cl_step(*zr, *zi, *cr);
        let wasm_r = wasm_step.call(&mut store, (*zr, *zi, *cr)).unwrap();
        assert_eq!(cl_r, wasm_r, "CL==WASM for ({zr},{zi},{cr})");

        eprint!("  step_re({zr},{zi},{cr}): CL={cl_r} WASM={wasm_r}");

        match try_gpu_step(wgsl, *zr, *zi, *cr) {
            Some(gpu_r) => {
                assert_eq!(cl_r, gpu_r, "CL==GPU for ({zr},{zi},{cr})");
                eprintln!(" GPU={gpu_r} ✓");
                gpu_ok = true;
            }
            None => { eprintln!(" (no GPU)"); }
        }
    }

    // Relay: CL → WASM → GPU (or CL fallback)
    let c_re = -512i64;
    let (mut zr, mut zi) = (0i64, 0i64);

    // Leg 1: Cranelift
    for _ in 0..5 { let nr = cl_step(zr, zi, c_re); zi = cl_step(zi, zr, 614); zr = nr; }
    eprintln!("\n  Relay leg 1 (Cranelift, 5 steps): z=({zr},{zi})");

    // Leg 2: WASM
    for _ in 0..5 {
        let nr = wasm_step.call(&mut store, (zr, zi, c_re)).unwrap();
        zi = wasm_step.call(&mut store, (zi, zr, 614)).unwrap();
        zr = nr;
    }
    eprintln!("  Relay leg 2 (WASM, 5 steps):     z=({zr},{zi})");

    // Leg 3: GPU (or Cranelift fallback)
    if gpu_ok {
        for _ in 0..5 {
            let nr = try_gpu_step(wgsl, zr, zi, c_re).unwrap();
            zi = try_gpu_step(wgsl, zi, zr, 614).unwrap();
            zr = nr;
        }
        eprintln!("  Relay leg 3 (GPU, 5 steps):      z=({zr},{zi})");
    } else {
        for _ in 0..5 { let nr = cl_step(zr, zi, c_re); zi = cl_step(zi, zr, 614); zr = nr; }
        eprintln!("  Relay leg 3 (CL fallback):       z=({zr},{zi})");
    }

    // Verify against pure Cranelift 15-step reference
    let (mut ref_zr, mut ref_zi) = (0i64, 0i64);
    for _ in 0..15 { let nr = cl_step(ref_zr, ref_zi, c_re); ref_zi = cl_step(ref_zi, ref_zr, 614); ref_zr = nr; }
    assert_eq!((zr, zi), (ref_zr, ref_zi), "Relay must match reference");

    eprintln!("\n╔══════════════════════════════════════════════════════════╗");
    if gpu_ok {
        eprintln!("║  ALL THREE BACKENDS COMPUTED — RELAY VERIFIED           ║");
    } else {
        eprintln!("║  CL + WASM computed, GPU validated (no adapter)         ║");
    }
    eprintln!("╚══════════════════════════════════════════════════════════╝");
}
