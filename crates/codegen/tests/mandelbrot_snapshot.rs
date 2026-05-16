//! Mandelbrot snapshot test: NxN escape times from each backend.
//! Default N=32. Override with MANDELBROT_N env var.

use sonatina_codegen::Backend;
use sonatina_codegen::isa::cranelift::CraneliftBackend;
use sonatina_codegen::isa::wasm::WasmBackend;
use sonatina_ir::{
    Linkage, Signature, Type,
    builder::ModuleBuilder, func_cursor::InstInserter,
    inst::{arith, cmp, control_flow},
    isa::{Isa, native::Native}, module::ModuleCtx,
};
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

fn build_escape_time() -> sonatina_ir::Module {
    let isa = Native::new(TargetTriple::new(
        if cfg!(target_arch = "x86_64") { Architecture::X86_64 } else { Architecture::Aarch64 },
        Vendor::Unknown, OperatingSystem::Native));
    let is = isa.inst_set();
    let mb = ModuleBuilder::new(ModuleCtx::new(&isa));
    let sig = Signature::new_single("escape_time", Linkage::Public,
        &[Type::I64, Type::I64, Type::I64], Type::I64);
    let fr = mb.declare_function(sig).unwrap();
    let mut fb = mb.func_builder::<InstInserter>(fr);
    let entry = fb.append_block();
    let lh = fb.append_block();
    let lb = fb.append_block();
    let cont = fb.append_block();
    let esc = fb.append_block();
    let exit = fb.append_block();
    fb.switch_to_block(entry);
    let c_re = fb.args()[0]; let c_im = fb.args()[1]; let max = fb.args()[2];
    let zero = fb.make_imm_value(0i64);
    fb.insert_inst_no_result(control_flow::Jump::new(is, lh));
    fb.switch_to_block(lh);
    let zr = fb.insert_inst(control_flow::Phi::new(is, vec![(zero, entry)]), Type::I64);
    let zi = fb.insert_inst(control_flow::Phi::new(is, vec![(zero, entry)]), Type::I64);
    let i = fb.insert_inst(control_flow::Phi::new(is, vec![(zero, entry)]), Type::I64);
    let c = fb.insert_inst(cmp::Lt::new(is, i, max), Type::I1);
    fb.insert_inst_no_result(control_flow::Br::new(is, c, lb, exit));
    fb.switch_to_block(lb);
    let rr = fb.insert_inst(arith::Mul::new(is, zr, zr), Type::I64);
    let ii = fb.insert_inst(arith::Mul::new(is, zi, zi), Type::I64);
    let mag = fb.insert_inst(arith::Add::new(is, rr, ii), Type::I64);
    let th = fb.make_imm_value(4_194_304i64);
    let ec = fb.insert_inst(cmp::Lt::new(is, mag, th), Type::I1);
    fb.insert_inst_no_result(control_flow::Br::new(is, ec, cont, esc));
    fb.switch_to_block(cont);
    let diff = fb.insert_inst(arith::Sub::new(is, rr, ii), Type::I64);
    let ten = fb.make_imm_value(10i64);
    let sr = fb.insert_inst(arith::Sar::new(is, ten, diff), Type::I64);
    let nr = fb.insert_inst(arith::Add::new(is, sr, c_re), Type::I64);
    let p = fb.insert_inst(arith::Mul::new(is, zr, zi), Type::I64);
    let two = fb.make_imm_value(2i64);
    let d = fb.insert_inst(arith::Mul::new(is, two, p), Type::I64);
    let si = fb.insert_inst(arith::Sar::new(is, ten, d), Type::I64);
    let ni = fb.insert_inst(arith::Add::new(is, si, c_im), Type::I64);
    let one = fb.make_imm_value(1i64);
    let ni2 = fb.insert_inst(arith::Add::new(is, i, one), Type::I64);
    fb.append_phi_arg(zr, nr, cont);
    fb.append_phi_arg(zi, ni, cont);
    fb.append_phi_arg(i, ni2, cont);
    fb.insert_inst_no_result(control_flow::Jump::new(is, lh));
    fb.switch_to_block(esc);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, i));
    fb.switch_to_block(exit);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, max));
    fb.seal_all(); fb.finish();
    mb.build()
}

fn render_ascii(data: &[i64], n: usize, max: i64) -> String {
    let chars = b" .,:;+*%#@";
    let mut out = String::new();
    for row in 0..n {
        for col in 0..n {
            let iters = data[row * n + col];
            let ch = if iters >= max {
                '@'
            } else if iters <= 1 {
                ' '
            } else {
                let idx = (iters as usize * (chars.len() - 1)) / max as usize;
                chars[idx.min(chars.len() - 1)] as char
            };
            out.push(ch);
        }
        out.push('\n');
    }
    out
}

#[test]
fn mandelbrot_snapshot_cranelift() {
    let n: usize = std::env::var("MANDELBROT_N").ok()
        .and_then(|s| s.parse().ok()).unwrap_or(32);
    let max = 50i64;
    let module = build_escape_time();

    let cl = CraneliftBackend::new();
    let art = cl.compile_module(&module).expect("cranelift");
    let f: fn(i64,i64,i64)->i64 = unsafe {
        std::mem::transmute(art.get_func_ptr::<fn(i64,i64,i64)->i64>("escape_time").unwrap())
    };

    let mut data = Vec::with_capacity(n * n);
    for row in 0..n {
        for col in 0..n {
            let c_re = -2048 + (col as i64 * 2662) / n as i64;
            let c_im = -1229 + (row as i64 * 2458) / n as i64;
            data.push(f(c_re, c_im, max));
        }
    }

    let ascii = render_ascii(&data, n, max);
    insta::assert_snapshot!("cranelift_32x32", ascii);
}

#[test]
fn mandelbrot_snapshot_wasm() {
    let n: usize = std::env::var("MANDELBROT_N").ok()
        .and_then(|s| s.parse().ok()).unwrap_or(32);
    let max = 50i64;
    let module = build_escape_time();

    let wasm = WasmBackend::new();
    let art = wasm.compile_module(&module).expect("wasm");
    wasmparser::validate(&art.bytes).expect("invalid");
    let engine = wasmtime::Engine::default();
    let wm = wasmtime::Module::new(&engine, &art.bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let inst = wasmtime::Instance::new(&mut store, &wm, &[]).unwrap();
    let f = inst.get_typed_func::<(i64,i64,i64),i64>(&mut store, "escape_time").unwrap();

    let mut data = Vec::with_capacity(n * n);
    for row in 0..n {
        for col in 0..n {
            let c_re = -2048 + (col as i64 * 2662) / n as i64;
            let c_im = -1229 + (row as i64 * 2458) / n as i64;
            data.push(f.call(&mut store, (c_re, c_im, max)).unwrap());
        }
    }

    let ascii = render_ascii(&data, n, max);
    insta::assert_snapshot!("wasm_32x32", ascii);
}

#[test]
fn mandelbrot_snapshot_spirv_compiles() {
    use sonatina_codegen::isa::spirv::SpirvBackend;

    let module = build_escape_time();
    let spirv = SpirvBackend::new().with_workgroup_size(1, 1, 1);
    let art = spirv.compile_module(&module).expect("spirv escape_time must compile");
    assert_eq!(art.words[0], 0x07230203, "valid SPIR-V magic number");
    assert!(art.wgsl.is_some(), "WGSL output must be generated");
    let wgsl = art.wgsl.as_ref().unwrap();
    assert!(wgsl.contains("fn main"), "WGSL must contain entry point");
    eprintln!("  SPIR-V: {} words, WGSL: {} chars", art.words.len(), wgsl.len());
}

#[test]
fn mandelbrot_snapshot_spirv_gpu() {
    use sonatina_codegen::isa::spirv::SpirvBackend;

    let module = build_escape_time();
    let spirv = SpirvBackend::new().with_workgroup_size(1, 1, 1);
    let art = spirv.compile_module(&module).expect("spirv");
    let wgsl = art.wgsl.as_ref().expect("WGSL");

    let instance = wgpu::Instance::default();
    let adapter = match pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
        power_preference: wgpu::PowerPreference::LowPower,
        force_fallback_adapter: false,
        ..Default::default()
    })) {
        Ok(a) => a,
        Err(_) => { eprintln!("  No GPU adapter — skipping GPU snapshot"); return; }
    };
    let (device, queue) = match pollster::block_on(adapter.request_device(
        &wgpu::DeviceDescriptor {
            required_features: wgpu::Features::SHADER_INT64,
            ..Default::default()
        }
    )) {
        Ok(dq) => dq,
        Err(_) => { eprintln!("  No SHADER_INT64 support — skipping"); return; }
    };

    eprintln!("  GPU: {}", adapter.get_info().name);

    let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("escape_time"),
        source: wgpu::ShaderSource::Wgsl(wgsl.into()),
    });

    // Spot-check a few pixels against Cranelift
    let cl = CraneliftBackend::new();
    let cl_art = cl.compile_module(&module).expect("cranelift");
    let cl_fn: fn(i64,i64,i64)->i64 = unsafe {
        std::mem::transmute(cl_art.get_func_ptr::<fn(i64,i64,i64)->i64>("escape_time").unwrap())
    };

    let spots = [
        (-2048i64, 0i64),    // far left
        (0, 0),              // origin
        (614, 0),            // right
        (-512, 614),         // upper
        (-1024, -614),       // lower left
    ];
    let max = 50i64;

    for (c_re, c_im) in &spots {
        let expected = cl_fn(*c_re, *c_im, max);

        let input: Vec<u8> = [*c_re, *c_im, max].iter().flat_map(|v| v.to_le_bytes()).collect();
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
        {
            let mut p = enc.begin_compute_pass(&Default::default());
            p.set_pipeline(&pipeline);
            p.set_bind_group(0, &bg, &[]);
            p.dispatch_workgroups(1, 1, 1);
        }
        enc.copy_buffer_to_buffer(&output_buf, 0, &staging_buf, 0, 8);
        queue.submit(Some(enc.finish()));

        let slice = staging_buf.slice(..);
        let (tx, rx) = std::sync::mpsc::channel();
        slice.map_async(wgpu::MapMode::Read, move |r| { tx.send(r).unwrap(); });
        let _ = device.poll(wgpu::PollType::Wait {
            submission_index: None,
            timeout: Some(std::time::Duration::from_secs(10)),
        });
        rx.recv().unwrap().unwrap();
        let data = slice.get_mapped_range();
        let gpu_result = i64::from_le_bytes(data[0..8].try_into().unwrap());
        drop(data);
        staging_buf.unmap();

        eprintln!("  ({c_re},{c_im}): CL={expected} GPU={gpu_result}");
        assert_eq!(expected, gpu_result, "GPU must match Cranelift at ({c_re},{c_im})");
    }
    eprintln!("  All {} spot checks passed — GPU matches Cranelift", spots.len());
}


/// Build a batch escape_and_store function in Sonatina IR.
/// Takes (c_re, c_im, max_iter, index) and stores escape_time result
/// to an ObjAlloc'd output buffer at the given index.
///
/// This is the "Fe program" -- same IR compiles to Cranelift, WASM, and SPIR-V.
fn build_escape_and_store() -> sonatina_ir::Module {
    use sonatina_ir::inst::data;

    let isa = Native::new(TargetTriple::new(
        if cfg!(target_arch = "x86_64") { Architecture::X86_64 } else { Architecture::Aarch64 },
        Vendor::Unknown, OperatingSystem::Native));
    let is = isa.inst_set();
    let mb = ModuleBuilder::new(ModuleCtx::new(&isa));

    let arr_ty = mb.declare_array_type(Type::I64, 1024);
    let arr_objref_ty = mb.objref_type(arr_ty);

    let sig = Signature::new_single("escape_and_store", Linkage::Public,
        &[Type::I64, Type::I64, Type::I64, Type::I64], Type::I64);
    let fr = mb.declare_function(sig).unwrap();
    let mut fb = mb.func_builder::<InstInserter>(fr);

    let entry = fb.append_block();
    let lh = fb.append_block();
    let lb = fb.append_block();
    let cont = fb.append_block();
    let esc = fb.append_block();
    let exit = fb.append_block();

    fb.switch_to_block(entry);
    let c_re = fb.args()[0];
    let c_im = fb.args()[1];
    let max = fb.args()[2];
    let idx = fb.args()[3];
    let zero = fb.make_imm_value(0i64);

    let buf = fb.insert_inst(data::ObjAlloc::new(is, arr_ty), arr_objref_ty);

    fb.insert_inst_no_result(control_flow::Jump::new(is, lh));

    fb.switch_to_block(lh);
    let zr = fb.insert_inst(control_flow::Phi::new(is, vec![(zero, entry)]), Type::I64);
    let zi = fb.insert_inst(control_flow::Phi::new(is, vec![(zero, entry)]), Type::I64);
    let i = fb.insert_inst(control_flow::Phi::new(is, vec![(zero, entry)]), Type::I64);
    let c = fb.insert_inst(cmp::Lt::new(is, i, max), Type::I1);
    fb.insert_inst_no_result(control_flow::Br::new(is, c, lb, exit));

    fb.switch_to_block(lb);
    let rr = fb.insert_inst(arith::Mul::new(is, zr, zr), Type::I64);
    let ii = fb.insert_inst(arith::Mul::new(is, zi, zi), Type::I64);
    let mag = fb.insert_inst(arith::Add::new(is, rr, ii), Type::I64);
    let th = fb.make_imm_value(4_194_304i64);
    let ec = fb.insert_inst(cmp::Lt::new(is, mag, th), Type::I1);
    fb.insert_inst_no_result(control_flow::Br::new(is, ec, cont, esc));

    fb.switch_to_block(cont);
    let diff = fb.insert_inst(arith::Sub::new(is, rr, ii), Type::I64);
    let ten = fb.make_imm_value(10i64);
    let sr = fb.insert_inst(arith::Sar::new(is, ten, diff), Type::I64);
    let nr = fb.insert_inst(arith::Add::new(is, sr, c_re), Type::I64);
    let p = fb.insert_inst(arith::Mul::new(is, zr, zi), Type::I64);
    let two = fb.make_imm_value(2i64);
    let d = fb.insert_inst(arith::Mul::new(is, two, p), Type::I64);
    let si = fb.insert_inst(arith::Sar::new(is, ten, d), Type::I64);
    let ni = fb.insert_inst(arith::Add::new(is, si, c_im), Type::I64);
    let one = fb.make_imm_value(1i64);
    let ni2 = fb.insert_inst(arith::Add::new(is, i, one), Type::I64);
    fb.append_phi_arg(zr, nr, cont);
    fb.append_phi_arg(zi, ni, cont);
    fb.append_phi_arg(i, ni2, cont);
    fb.insert_inst_no_result(control_flow::Jump::new(is, lh));

    let elem_objref_ty = mb.objref_type(Type::I64);

    fb.switch_to_block(esc);
    let slot = fb.insert_inst(data::ObjIndex::new(is, buf, idx), elem_objref_ty);
    fb.insert_inst_no_result(data::ObjStore::new(is, slot, i));
    fb.insert_inst_no_result(control_flow::Return::new_single(is, i));

    fb.switch_to_block(exit);
    let slot2 = fb.insert_inst(data::ObjIndex::new(is, buf, idx), elem_objref_ty);
    fb.insert_inst_no_result(data::ObjStore::new(is, slot2, max));
    fb.insert_inst_no_result(control_flow::Return::new_single(is, max));

    fb.seal_all();
    fb.finish();
    mb.build()
}

#[test]
fn batch_escape_spirv_compiles() {
    use sonatina_codegen::isa::spirv::SpirvBackend;

    let module = build_escape_and_store();
    let spirv = SpirvBackend::new().with_workgroup_size(1, 1, 1);
    let art = spirv.compile_module(&module).expect("spirv escape_and_store must compile");
    assert_eq!(art.words[0], 0x07230203, "valid SPIR-V magic");
    let wgsl = art.wgsl.as_ref().expect("WGSL should be generated");
    eprintln!("  SPIR-V: {} words, WGSL: {} chars", art.words.len(), wgsl.len());
    eprintln!("  WGSL:\n{wgsl}");
}

#[test]
fn batch_escape_cranelift() {
    let module = build_escape_and_store();
    let cl = CraneliftBackend::new();
    let art = cl.compile_module(&module).expect("cranelift");
    let f: fn(i64,i64,i64,i64)->i64 = unsafe {
        std::mem::transmute(art.get_func_ptr::<fn(i64,i64,i64,i64)->i64>("escape_and_store").unwrap())
    };
    let result = f(-2048, 0, 50, 0);
    eprintln!("  escape_and_store(-2048, 0, 50, idx=0) = {result}");
    assert!(result >= 1 && result <= 50);
}
