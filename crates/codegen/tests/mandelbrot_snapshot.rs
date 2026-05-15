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
