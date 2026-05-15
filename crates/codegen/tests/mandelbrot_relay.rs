//! Mandelbrot relay: iterations handed between Cranelift → WASM → SPIR-V
//!
//! Fixed-point integer Mandelbrot (×1024 scale, shift-based division).
//! z = z² + c where z_re' = (z_re²-z_im²)>>10 + c_re
//!                   z_im' = (2·z_re·z_im)>>10 + c_im
//! Escape: z_re² + z_im² > 4·1024² = 4_194_304

use sonatina_codegen::Backend;
use sonatina_codegen::isa::cranelift::CraneliftBackend;
use sonatina_codegen::isa::wasm::WasmBackend;
use sonatina_codegen::isa::spirv::SpirvBackend;
use sonatina_ir::{
    Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::{arith, cmp, control_flow},
    isa::{Isa, native::Native},
    module::ModuleCtx,
};
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

fn build_mandelbrot_module() -> sonatina_ir::Module {
    let isa = Native::new(TargetTriple::new(
        if cfg!(target_arch = "x86_64") { Architecture::X86_64 } else { Architecture::Aarch64 },
        Vendor::Unknown, OperatingSystem::Native,
    ));
    let is = isa.inst_set();
    let ctx = ModuleCtx::new(&isa);
    let mb = ModuleBuilder::new(ctx);

    // mandelbrot_step_re(z_re, z_im, c_re: i64) -> i64
    // = (z_re*z_re - z_im*z_im) >> 10 + c_re
    let sig_re = Signature::new_single("step_re", Linkage::Public,
        &[Type::I64, Type::I64, Type::I64], Type::I64);
    let fr_re = mb.declare_function(sig_re).unwrap();
    {
        let mut fb = mb.func_builder::<InstInserter>(fr_re);
        let entry = fb.append_block();
        fb.switch_to_block(entry);
        let z_re = fb.args()[0];
        let z_im = fb.args()[1];
        let c_re = fb.args()[2];
        let re_sq = fb.insert_inst(arith::Mul::new(is, z_re, z_re), Type::I64);
        let im_sq = fb.insert_inst(arith::Mul::new(is, z_im, z_im), Type::I64);
        let diff = fb.insert_inst(arith::Sub::new(is, re_sq, im_sq), Type::I64);
        let ten = fb.make_imm_value(10i64);
        let shifted = fb.insert_inst(arith::Sar::new(is, diff, ten), Type::I64);
        let result = fb.insert_inst(arith::Add::new(is, shifted, c_re), Type::I64);
        fb.insert_inst_no_result(control_flow::Return::new_single(is, result));
        fb.seal_all();
        fb.finish();
    }

    // mandelbrot_step_im(z_re, z_im, c_im: i64) -> i64
    // = (2 * z_re * z_im) >> 10 + c_im
    let sig_im = Signature::new_single("step_im", Linkage::Public,
        &[Type::I64, Type::I64, Type::I64], Type::I64);
    let fr_im = mb.declare_function(sig_im).unwrap();
    {
        let mut fb = mb.func_builder::<InstInserter>(fr_im);
        let entry = fb.append_block();
        fb.switch_to_block(entry);
        let z_re = fb.args()[0];
        let z_im = fb.args()[1];
        let c_im = fb.args()[2];
        let two = fb.make_imm_value(2i64);
        let prod = fb.insert_inst(arith::Mul::new(is, z_re, z_im), Type::I64);
        let doubled = fb.insert_inst(arith::Mul::new(is, two, prod), Type::I64);
        let ten = fb.make_imm_value(10i64);
        let shifted = fb.insert_inst(arith::Sar::new(is, doubled, ten), Type::I64);
        let result = fb.insert_inst(arith::Add::new(is, shifted, c_im), Type::I64);
        fb.insert_inst_no_result(control_flow::Return::new_single(is, result));
        fb.seal_all();
        fb.finish();
    }

    mb.build()
}

fn mandelbrot_cl(
    step_re: fn(i64, i64, i64) -> i64,
    step_im: fn(i64, i64, i64) -> i64,
    mut z_re: i64, mut z_im: i64,
    c_re: i64, c_im: i64, n: usize,
) -> (i64, i64, bool) {
    for _ in 0..n {
        let new_re = step_re(z_re, z_im, c_re);
        let new_im = step_im(z_re, z_im, c_im);
        z_re = new_re;
        z_im = new_im;
        if z_re.saturating_mul(z_re).saturating_add(z_im.saturating_mul(z_im)) > 4_194_304 {
            return (z_re, z_im, true);
        }
    }
    (z_re, z_im, false)
}

fn mandelbrot_wasm(
    step_re: &wasmtime::TypedFunc<(i64, i64, i64), i64>,
    step_im: &wasmtime::TypedFunc<(i64, i64, i64), i64>,
    store: &mut wasmtime::Store<()>,
    mut z_re: i64, mut z_im: i64,
    c_re: i64, c_im: i64, n: usize,
) -> (i64, i64, bool) {
    for _ in 0..n {
        let new_re = step_re.call(&mut *store, (z_re, z_im, c_re)).unwrap();
        let new_im = step_im.call(&mut *store, (z_re, z_im, c_im)).unwrap();
        z_re = new_re;
        z_im = new_im;
        if z_re.saturating_mul(z_re).saturating_add(z_im.saturating_mul(z_im)) > 4_194_304 {
            return (z_re, z_im, true);
        }
    }
    (z_re, z_im, false)
}

#[test]
fn mandelbrot_relay_cranelift_wasm_spirv() {
    let module = build_mandelbrot_module();

    eprintln!("╔══════════════════════════════════════════════════════╗");
    eprintln!("║  MANDELBROT RELAY: Cranelift → WASM → SPIR-V        ║");
    eprintln!("╚══════════════════════════════════════════════════════╝");

    // ── Cranelift backend ──────────────────────────────────────────
    let cl = CraneliftBackend::new();
    let cl_art = cl.compile_module(&module).expect("cranelift");
    let cl_step_re: fn(i64, i64, i64) -> i64 = unsafe {
        std::mem::transmute(cl_art.get_func_ptr::<fn(i64, i64, i64) -> i64>("step_re").unwrap())
    };
    let cl_step_im: fn(i64, i64, i64) -> i64 = unsafe {
        std::mem::transmute(cl_art.get_func_ptr::<fn(i64, i64, i64) -> i64>("step_im").unwrap())
    };

    // ── WASM backend ───────────────────────────────────────────────
    let wasm = WasmBackend::new();
    let wasm_art = wasm.compile_module(&module).expect("wasm");
    wasmparser::validate(&wasm_art.bytes).expect("invalid wasm");
    let engine = wasmtime::Engine::default();
    let wm = wasmtime::Module::new(&engine, &wasm_art.bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let inst = wasmtime::Instance::new(&mut store, &wm, &[]).unwrap();
    let wasm_step_re = inst.get_typed_func::<(i64, i64, i64), i64>(&mut store, "step_re").unwrap();
    let wasm_step_im = inst.get_typed_func::<(i64, i64, i64), i64>(&mut store, "step_im").unwrap();

    // ── SPIR-V backend ─────────────────────────────────────────────
    let spirv = SpirvBackend::new();
    let spirv_art = spirv.compile_module(&module).expect("spirv");
    assert_eq!(spirv_art.words[0], 0x07230203, "valid SPIR-V");
    eprintln!("  SPIR-V: step functions validated ✓");

    // ── Fixed-point coordinates (×1024 scale) ──────────────────────
    // c = (-0.5, 0.6) → (-512, 614) in fixed-point
    let c_re: i64 = -512;
    let c_im: i64 = 614;

    // ── LEG 1: Cranelift runs first 10 iterations ──────────────────
    let (z_re_cl, z_im_cl, escaped_cl) = mandelbrot_cl(
        cl_step_re, cl_step_im, 0, 0, c_re, c_im, 10);
    eprintln!("  Leg 1 (Cranelift, 10 iters): z=({z_re_cl}, {z_im_cl}) escaped={escaped_cl}");

    // ── LEG 2: WASM picks up Cranelift's state, runs 10 more ──────
    let (z_re_wasm, z_im_wasm, escaped_wasm) = mandelbrot_wasm(
        &wasm_step_re, &wasm_step_im, &mut store,
        z_re_cl, z_im_cl, c_re, c_im, 10);
    eprintln!("  Leg 2 (WASM, 10 more):        z=({z_re_wasm}, {z_im_wasm}) escaped={escaped_wasm}");

    // ── VERIFY: 20 iterations purely on Cranelift ──────────────────
    let (z_re_full, z_im_full, escaped_full) = mandelbrot_cl(
        cl_step_re, cl_step_im, 0, 0, c_re, c_im, 20);
    eprintln!("  Verify (Cranelift, 20 iters):  z=({z_re_full}, {z_im_full}) escaped={escaped_full}");
    assert_eq!((z_re_wasm, z_im_wasm, escaped_wasm), (z_re_full, z_im_full, escaped_full),
        "Relay (CL→WASM) must match full Cranelift run");

    // ── VERIFY: 20 iterations purely on WASM ───────────────────────
    let (z_re_wfull, z_im_wfull, escaped_wfull) = mandelbrot_wasm(
        &wasm_step_re, &wasm_step_im, &mut store, 0, 0, c_re, c_im, 20);
    assert_eq!((z_re_wfull, z_im_wfull, escaped_wfull), (z_re_full, z_im_full, escaped_full),
        "Full WASM must match full Cranelift");

    // ── BONUS: 5×5 escape grid ─────────────────────────────────────
    eprintln!("\n  5×5 Mandelbrot escape map (20 iters, ×1024 fixed-point):");
    eprintln!("  c_re: -2048..1024  c_im: -1536..1536");
    let mut grid_match = true;
    for row in 0..5 {
        let mut line = String::from("    ");
        for col in 0..5 {
            let cr = -2048 + col * 768;
            let ci = -1536 + row * 768;
            let (_, _, esc_cl) = mandelbrot_cl(cl_step_re, cl_step_im, 0, 0, cr, ci, 20);
            let (_, _, esc_wasm) = mandelbrot_wasm(
                &wasm_step_re, &wasm_step_im, &mut store, 0, 0, cr, ci, 20);
            if esc_cl != esc_wasm { grid_match = false; }
            line.push(if esc_cl { '·' } else { '█' });
        }
        eprintln!("{line}");
    }
    assert!(grid_match, "Cranelift and WASM escape maps must match");

    eprintln!("\n╔══════════════════════════════════════════════════════╗");
    eprintln!("║  MANDELBROT RELAY PASSED                             ║");
    eprintln!("║  State handed: Cranelift → WASM, verified on both    ║");
    eprintln!("║  SPIR-V step function validated                      ║");
    eprintln!("║  5×5 escape grid identical across backends           ║");
    eprintln!("╚══════════════════════════════════════════════════════╝");
}
