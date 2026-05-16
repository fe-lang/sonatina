//! Mandelbrot relay renderer: each pixel's iterations alternate between backends.
//! Cranelift does iters 0-16, WASM does 17-33, Cranelift does 34-50.
//! The rendered image IS the relay — every pixel crossed backend boundaries.

use sonatina_codegen::{
    Backend,
    isa::{cranelift::CraneliftBackend, wasm::WasmBackend},
};
use sonatina_ir::{
    Linkage, Signature, Type,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::{arith, cmp, control_flow},
    isa::{Isa, native::Native},
    module::ModuleCtx,
};
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

fn build_step_module() -> sonatina_ir::Module {
    let isa = Native::new(TargetTriple::new(
        if cfg!(target_arch = "x86_64") {
            Architecture::X86_64
        } else {
            Architecture::Aarch64
        },
        Vendor::Unknown,
        OperatingSystem::Native,
    ));
    let is = isa.inst_set();
    let mb = ModuleBuilder::new(ModuleCtx::new(&isa));

    // step(z_re, z_im, c_re, c_im) -> (new_z_re, new_z_im) as two functions
    for (name, compute_re) in [("step_re", true), ("step_im", false)] {
        let sig = Signature::new_single(
            name,
            Linkage::Public,
            &[Type::I64, Type::I64, Type::I64],
            Type::I64,
        );
        let fr = mb.declare_function(sig).unwrap();
        let mut fb = mb.func_builder::<InstInserter>(fr);
        let entry = fb.append_block();
        fb.switch_to_block(entry);
        let zr = fb.args()[0];
        let zi = fb.args()[1];
        let c = fb.args()[2];
        let ten = fb.make_imm_value(10i64);

        let result = if compute_re {
            let rr = fb.insert_inst(arith::Mul::new(is, zr, zr), Type::I64);
            let ii = fb.insert_inst(arith::Mul::new(is, zi, zi), Type::I64);
            let diff = fb.insert_inst(arith::Sub::new(is, rr, ii), Type::I64);
            let shifted = fb.insert_inst(arith::Sar::new(is, ten, diff), Type::I64);
            fb.insert_inst(arith::Add::new(is, shifted, c), Type::I64)
        } else {
            let two = fb.make_imm_value(2i64);
            let prod = fb.insert_inst(arith::Mul::new(is, zr, zi), Type::I64);
            let doubled = fb.insert_inst(arith::Mul::new(is, two, prod), Type::I64);
            let shifted = fb.insert_inst(arith::Sar::new(is, ten, doubled), Type::I64);
            fb.insert_inst(arith::Add::new(is, shifted, c), Type::I64)
        };
        fb.insert_inst_no_result(control_flow::Return::new_single(is, result));
        fb.seal_all();
        fb.finish();
    }
    mb.build()
}

struct RelayBackends {
    cl_re: fn(i64, i64, i64) -> i64,
    cl_im: fn(i64, i64, i64) -> i64,
}

fn relay_escape_time(
    cl: &RelayBackends,
    wasm_re: &wasmtime::TypedFunc<(i64, i64, i64), i64>,
    wasm_im: &wasmtime::TypedFunc<(i64, i64, i64), i64>,
    store: &mut wasmtime::Store<()>,
    c_re: i64,
    c_im: i64,
    max_iter: i64,
    leg_size: i64,
) -> (i64, i64) {
    // (iterations, which_backend_finished)
    let mut zr: i64 = 0;
    let mut zi: i64 = 0;

    for iter in 0..max_iter {
        if zr.saturating_mul(zr).saturating_add(zi.saturating_mul(zi)) > 4_194_304 {
            let backend = (iter / leg_size) % 2; // 0=CL, 1=WASM
            return (iter, backend);
        }

        let leg = (iter / leg_size) % 2;
        let (new_re, new_im) = if leg == 0 {
            // Cranelift leg
            ((cl.cl_re)(zr, zi, c_re), (cl.cl_im)(zr, zi, c_im))
        } else {
            // WASM leg
            {
                let re = wasm_re.call(&mut *store, (zr, zi, c_re)).unwrap();
                let im = wasm_im.call(&mut *store, (zr, zi, c_im)).unwrap();
                (re, im)
            }
        };
        zr = new_re;
        zi = new_im;
    }
    (max_iter, 2) // in the set
}

#[test]
fn mandelbrot_relay_render() {
    let module = build_step_module();
    let n: usize = std::env::var("MANDELBROT_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(64);
    let max_iter = 80i64;
    let leg_size = 10i64; // alternate every 10 iterations

    // Cranelift
    let cl_backend = CraneliftBackend::new();
    let cl_art = cl_backend.compile_module(&module).expect("cranelift");
    let cl = RelayBackends {
        cl_re: unsafe {
            std::mem::transmute(
                cl_art
                    .get_func_ptr::<fn(i64, i64, i64) -> i64>("step_re")
                    .unwrap(),
            )
        },
        cl_im: unsafe {
            std::mem::transmute(
                cl_art
                    .get_func_ptr::<fn(i64, i64, i64) -> i64>("step_im")
                    .unwrap(),
            )
        },
    };

    // WASM
    let wasm_backend = WasmBackend::new();
    let wasm_art = wasm_backend.compile_module(&module).expect("wasm");
    wasmparser::validate(&wasm_art.bytes).expect("invalid");
    let engine = wasmtime::Engine::default();
    let wm = wasmtime::Module::new(&engine, &wasm_art.bytes).unwrap();
    let mut store = wasmtime::Store::new(&engine, ());
    let inst = wasmtime::Instance::new(&mut store, &wm, &[]).unwrap();
    let wasm_re = inst
        .get_typed_func::<(i64, i64, i64), i64>(&mut store, "step_re")
        .unwrap();
    let wasm_im = inst
        .get_typed_func::<(i64, i64, i64), i64>(&mut store, "step_im")
        .unwrap();

    let t0 = std::time::Instant::now();

    let mut iters_data = Vec::with_capacity(n * n);
    let mut backend_data = Vec::with_capacity(n * n);

    for row in 0..n {
        for col in 0..n {
            let c_re = -2048 + (col as i64 * 2662) / n as i64;
            let c_im = -1229 + (row as i64 * 2458) / n as i64;
            let (iters, backend) = relay_escape_time(
                &cl, &wasm_re, &wasm_im, &mut store, c_re, c_im, max_iter, leg_size,
            );
            iters_data.push(iters);
            backend_data.push(backend);
        }
    }

    let elapsed = t0.elapsed();
    eprintln!("  Relay render: {}×{} in {:?}", n, n, elapsed);

    // Count which backend finished each pixel
    let cl_count = backend_data.iter().filter(|&&b| b == 0).count();
    let wasm_count = backend_data.iter().filter(|&&b| b == 1).count();
    let set_count = backend_data.iter().filter(|&&b| b == 2).count();
    eprintln!("  Escaped on Cranelift: {cl_count}");
    eprintln!("  Escaped on WASM:      {wasm_count}");
    eprintln!("  In the set:           {set_count}");

    // Build HTML with real relay data
    let iters_json = format!(
        "[{}]",
        iters_data
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );
    let backend_json = format!(
        "[{}]",
        backend_data
            .iter()
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(",")
    );

    let html = format!(
        r##"<!DOCTYPE html>
<html>
<head><title>Mandelbrot Relay</title>
<style>
body{{background:#0a0a0a;color:#e0e0e0;font-family:monospace;margin:40px}}
h1{{color:#ff6b35;font-size:22px}}
canvas{{border:1px solid #333;display:block;margin:10px 0;image-rendering:pixelated;width:512px;height:512px}}
.info{{color:#999;font-size:12px}}
.cl{{color:#4caf50}}.wasm{{color:#5c6bc0}}.set{{color:#666}}
</style>
</head>
<body>
<h1>Mandelbrot Relay — Every Pixel Crossed Backend Boundaries</h1>
<p>Iterations alternate: <span class="cl">Cranelift (0-9)</span> →
<span class="wasm">WASM (10-19)</span> → <span class="cl">Cranelift (20-29)</span> → ...
</p>
<p>Escaped on <span class="cl">Cranelift: {cl_count}</span> |
<span class="wasm">WASM: {wasm_count}</span> |
<span class="set">In set: {set_count}</span></p>

<canvas id="c" width="{n}" height="{n}"></canvas>
<div class="info">{n}×{n} | {max_iter} max iterations | {leg_size}-iteration legs | Relay time: {elapsed:?}</div>

<script>
const iters={iters_json};
const backends={backend_json};
const W={n},H={n},MAX={max_iter};
const ctx=document.getElementById('c').getContext('2d');
const img=ctx.createImageData(W,H);
for(let i=0;i<iters.length;i++){{
  const t=iters[i]/MAX;
  let r,g,b;
  if(iters[i]>=MAX){{r=g=b=10;}}
  else if(backends[i]==0){{
    // Cranelift: green tint
    r=Math.floor(2*(1-t)*t*t*t*255);
    g=Math.floor(12*(1-t)*(1-t)*t*t*255);
    b=Math.floor(4*(1-t)*(1-t)*(1-t)*t*255);
  }}else{{
    // WASM: blue tint
    r=Math.floor(4*(1-t)*(1-t)*(1-t)*t*255);
    g=Math.floor(6*(1-t)*(1-t)*t*t*255);
    b=Math.floor(12*(1-t)*t*t*t*255);
  }}
  img.data[i*4]=r;img.data[i*4+1]=g;img.data[i*4+2]=b;img.data[i*4+3]=255;
}}
ctx.putImageData(img,0,0);
</script>
</body>
</html>"##
    );

    std::fs::write("/tmp/mandelbrot_relay.html", &html).expect("write html");
    eprintln!("  Written /tmp/mandelbrot_relay.html");

    // Also snapshot the ASCII version
    let chars = b" .,:;+*%#@";
    let mut ascii = String::new();
    for row in 0..n.min(32) {
        for col in 0..n.min(32) {
            let idx = row * n + col * (n / 32);
            let iters = iters_data[idx.min(iters_data.len() - 1)];
            let ch = if iters >= max_iter {
                '@'
            } else if iters <= 1 {
                ' '
            } else {
                chars[((iters as usize * (chars.len() - 1)) / max_iter as usize)
                    .min(chars.len() - 1)] as char
            };
            ascii.push(ch);
        }
        ascii.push('\n');
    }
    eprintln!("\n  Relay ASCII (32×32 sample):\n");
    for line in ascii.lines() {
        eprintln!("  {line}");
    }
}
