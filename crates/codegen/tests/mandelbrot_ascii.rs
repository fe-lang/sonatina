//! 64×64 ASCII Mandelbrot rendered by Cranelift JIT and WASM wasmtime.

use sonatina_codegen::Backend;
use sonatina_codegen::isa::cranelift::CraneliftBackend;
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

fn build_mandelbrot_module() -> sonatina_ir::Module {
    let isa = Native::new(TargetTriple::new(
        if cfg!(target_arch = "x86_64") { Architecture::X86_64 } else { Architecture::Aarch64 },
        Vendor::Unknown, OperatingSystem::Native,
    ));
    let is = isa.inst_set();
    let mb = ModuleBuilder::new(ModuleCtx::new(&isa));

    // escape_time(c_re, c_im, max_iter) -> iterations
    let sig = Signature::new_single("escape_time", Linkage::Public,
        &[Type::I64, Type::I64, Type::I64], Type::I64);
    let fr = mb.declare_function(sig).unwrap();
    let mut fb = mb.func_builder::<InstInserter>(fr);

    let entry = fb.append_block();
    let loop_header = fb.append_block();
    let loop_body = fb.append_block();
    let cont = fb.append_block();
    let escaped = fb.append_block();
    let exit = fb.append_block();

    // entry
    fb.switch_to_block(entry);
    let c_re = fb.args()[0];
    let c_im = fb.args()[1];
    let max_iter = fb.args()[2];
    let zero = fb.make_imm_value(0i64);
    fb.insert_inst_no_result(control_flow::Jump::new(is, loop_header));

    // loop_header
    fb.switch_to_block(loop_header);
    let z_re = fb.insert_inst(control_flow::Phi::new(is, vec![(zero, entry)]), Type::I64);
    let z_im = fb.insert_inst(control_flow::Phi::new(is, vec![(zero, entry)]), Type::I64);
    let i = fb.insert_inst(control_flow::Phi::new(is, vec![(zero, entry)]), Type::I64);
    let cond = fb.insert_inst(cmp::Lt::new(is, i, max_iter), Type::I1);
    fb.insert_inst_no_result(control_flow::Br::new(is, cond, loop_body, exit));

    // loop_body: check escape
    fb.switch_to_block(loop_body);
    let re_sq = fb.insert_inst(arith::Mul::new(is, z_re, z_re), Type::I64);
    let im_sq = fb.insert_inst(arith::Mul::new(is, z_im, z_im), Type::I64);
    let mag_sq = fb.insert_inst(arith::Add::new(is, re_sq, im_sq), Type::I64);
    let threshold = fb.make_imm_value(4_194_304i64);
    let esc_cond = fb.insert_inst(cmp::Lt::new(is, mag_sq, threshold), Type::I1);
    fb.insert_inst_no_result(control_flow::Br::new(is, esc_cond, cont, escaped));

    // cont: compute next z
    fb.switch_to_block(cont);
    let diff = fb.insert_inst(arith::Sub::new(is, re_sq, im_sq), Type::I64);
    let ten = fb.make_imm_value(10i64);
    let shifted_re = fb.insert_inst(arith::Sar::new(is, ten, diff), Type::I64);
    let new_re = fb.insert_inst(arith::Add::new(is, shifted_re, c_re), Type::I64);

    let prod = fb.insert_inst(arith::Mul::new(is, z_re, z_im), Type::I64);
    let two = fb.make_imm_value(2i64);
    let doubled = fb.insert_inst(arith::Mul::new(is, two, prod), Type::I64);
    let shifted_im = fb.insert_inst(arith::Sar::new(is, ten, doubled), Type::I64);
    let new_im = fb.insert_inst(arith::Add::new(is, shifted_im, c_im), Type::I64);

    let one = fb.make_imm_value(1i64);
    let new_i = fb.insert_inst(arith::Add::new(is, i, one), Type::I64);

    fb.append_phi_arg(z_re, new_re, cont);
    fb.append_phi_arg(z_im, new_im, cont);
    fb.append_phi_arg(i, new_i, cont);
    fb.insert_inst_no_result(control_flow::Jump::new(is, loop_header));

    // escaped
    fb.switch_to_block(escaped);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, i));

    // exit: max_iter reached
    fb.switch_to_block(exit);
    fb.insert_inst_no_result(control_flow::Return::new_single(is, max_iter));

    fb.seal_all();
    fb.finish();
    mb.build()
}

const CHARS: &[u8] = b" .,:;+*%#@";

fn escape_to_char(iters: i64, max: i64) -> char {
    if iters >= max { return '@' } // in the set = dense
    if iters <= 1 { return ' ' } // escaped immediately = blank
    let idx = (iters as usize * (CHARS.len() - 1)) / max as usize;
    CHARS[idx.min(CHARS.len() - 1)] as char
}

#[test]
fn mandelbrot_64x64_ascii() {
    let module = build_mandelbrot_module();
    let max_iter = 50i64;

    let cl = CraneliftBackend::new();
    let cl_art = cl.compile_module(&module).expect("cranelift");
    let cl_fn: fn(i64, i64, i64) -> i64 = unsafe {
        std::mem::transmute(cl_art.get_func_ptr::<fn(i64, i64, i64) -> i64>("escape_time").unwrap())
    };

    let wasm = WasmBackend::new();
    let wasm_art = wasm.compile_module(&module).expect("wasm");
    wasmparser::validate(&wasm_art.bytes).expect("invalid wasm");
    let engine = wasmtime::Engine::default();
    let wm = wasmtime::Module::new(&engine, &wasm_art.bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let inst = wasmtime::Instance::new(&mut store, &wm, &[]).unwrap();
    let wasm_fn = inst.get_typed_func::<(i64, i64, i64), i64>(&mut store, "escape_time").unwrap();

    eprintln!("\n  64×64 MANDELBROT — Cranelift JIT + WASM (verified identical)\n");

    let mut match_count = 0;
    let total = 64 * 64;

    for row in 0..64 {
        let mut line = String::new();
        for col in 0..64 {
            // Full domain: re [-2.0, 0.6], im [-1.2, 1.2] in ×1024 fixed-point
            let c_re = -2048 + (col * 2662) / 64;
            let c_im = -1229 + (row * 2458) / 64;

            let cl_iters = cl_fn(c_re, c_im, max_iter);
            let wasm_iters = wasm_fn.call(&mut store, (c_re, c_im, max_iter)).unwrap();

            if cl_iters == wasm_iters { match_count += 1; }
            line.push(escape_to_char(cl_iters, max_iter));
        }
        eprintln!("  {line}");
    }

    assert_eq!(match_count, total, "All pixels must match between Cranelift and WASM");
    eprintln!("\n  {match_count}/{total} pixels identical across backends ✓");
}
