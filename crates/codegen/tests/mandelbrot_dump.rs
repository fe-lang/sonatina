//! Dump escape-time data from all three backends to /tmp/

use sonatina_codegen::Backend;
use sonatina_codegen::isa::cranelift::CraneliftBackend;
use sonatina_codegen::isa::wasm::WasmBackend;
use sonatina_codegen::isa::spirv::SpirvBackend;
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

fn render_grid(f: &dyn Fn(i64,i64,i64)->i64, size: i64, max: i64) -> Vec<i64> {
    let mut data = Vec::with_capacity((size * size) as usize);
    for row in 0..size {
        for col in 0..size {
            let c_re = -2048 + (col * 2662) / size;
            let c_im = -1229 + (row * 2458) / size;
            data.push(f(c_re, c_im, max));
        }
    }
    data
}

fn to_json(data: &[i64]) -> String {
    format!("[{}]", data.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(","))
}

#[test]
fn dump_all_backends() {
    let module = build_escape_time();
    let size: i64 = 256;
    let max = 80i64;

    // Cranelift
    let t0 = std::time::Instant::now();
    let cl = CraneliftBackend::new();
    let cl_art = cl.compile_module(&module).expect("cranelift");
    let cl_compile = t0.elapsed();
    let cl_fn: fn(i64,i64,i64)->i64 = unsafe {
        std::mem::transmute(cl_art.get_func_ptr::<fn(i64,i64,i64)->i64>("escape_time").unwrap())
    };
    let t1 = std::time::Instant::now();
    let cl_data = render_grid(&|a,b,c| cl_fn(a,b,c), size, max);
    let cl_render = t1.elapsed();
    std::fs::write("/tmp/mandelbrot_cranelift.json", to_json(&cl_data)).unwrap();
    eprintln!("  Cranelift: compile={:?} render={:?}", cl_compile, cl_render);

    // WASM
    let t0 = std::time::Instant::now();
    let wasm = WasmBackend::new();
    let wasm_art = wasm.compile_module(&module).expect("wasm");
    wasmparser::validate(&wasm_art.bytes).expect("invalid");
    let engine = wasmtime::Engine::default();
    let wm = wasmtime::Module::new(&engine, &wasm_art.bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let inst = wasmtime::Instance::new(&mut store, &wm, &[]).unwrap();
    let wasm_fn = inst.get_typed_func::<(i64,i64,i64),i64>(&mut store, "escape_time").unwrap();
    let wasm_compile = t0.elapsed();
    let t1 = std::time::Instant::now();
    let mut wasm_data = Vec::with_capacity((size * size) as usize);
    for row in 0..size {
        for col in 0..size {
            let c_re = -2048 + (col * 2662) / size;
            let c_im = -1229 + (row * 2458) / size;
            wasm_data.push(wasm_fn.call(&mut store, (c_re, c_im, max)).unwrap());
        }
    }
    let wasm_render = t1.elapsed();
    std::fs::write("/tmp/mandelbrot_wasm.json", to_json(&wasm_data)).unwrap();
    eprintln!("  WASM:      compile={:?} render={:?}", wasm_compile, wasm_render);

    // SPIR-V — escape_time has loops+branches+3params, complex for Naga.
    let t0 = std::time::Instant::now();
    let spirv = SpirvBackend::new().with_workgroup_size(1,1,1);
    let spirv_art = spirv.compile_module(&module).expect("SPIR-V escape_time compilation failed");
    let spirv_compile = t0.elapsed();
    eprintln!("  SPIR-V:    compile={:?} (WGSL={}chars)", spirv_compile,
        spirv_art.wgsl.as_ref().map(|w| w.len()).unwrap_or(0));
    assert_eq!(spirv_art.words[0], 0x07230203, "valid SPIR-V magic");

    // Verify identical
    let mismatches = cl_data.iter().zip(wasm_data.iter()).filter(|(a,b)| a != b).count();
    eprintln!("  CL vs WASM: {}/{} pixels identical", cl_data.len() - mismatches, cl_data.len());
    assert_eq!(mismatches, 0);

    eprintln!("  Files: /tmp/mandelbrot_cranelift.json, /tmp/mandelbrot_wasm.json");
}
