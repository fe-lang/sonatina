//! Generated programs over structs, arrays and objects, run on the host-native
//! backend and on the WebAssembly backend. The native backend is the oracle for
//! the meaning of the aggregate and object instructions.

#![allow(clippy::crosspointer_transmute, dead_code)]

#[path = "wasm/harness.rs"]
mod harness;

use harness::Machine;
use sonatina_codegen::{Compile, OptLevel};
use sonatina_cranelift::CraneliftJitBackend;
use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};
use sonatina_wasm::WasmBackend;
use wasmtime::Val;

struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 ^ (self.0 >> 29)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

const PRELUDE: &str = "type @P = { i32, i64 };
func private %mk(v0.i32, v1.i64) -> @P {
    block0:
        v2.@P = insert_value undef.@P 0.i32 v0;
        v3.@P = insert_value v2 1.i32 v1;
        return v3;
}
func private %bump(v0.@P) -> @P {
    block0:
        v1.i32 = extract_value v0 0.i32;
        v2.i32 = add v1 1.i32;
        v3.@P = insert_value v0 0.i32 v2;
        return v3;
}
func private %sum(v0.@P, v1.[i32; 4]) -> i64 {
    block0:
        v2.i32 = extract_value v0 0.i32;
        v3.i64 = extract_value v0 1.i32;
        v4.i32 = extract_value v1 0.i32;
        v5.i32 = extract_value v1 1.i32;
        v6.i32 = extract_value v1 2.i32;
        v7.i32 = extract_value v1 3.i32;
        v8.i32 = add v2 v4;
        v9.i32 = add v5 v6;
        v10.i32 = add v8 v9;
        v11.i32 = xor v10 v7;
        v12.i64 = zext v11 i64;
        v13.i64 = add v12 v3;
        return v13;
}
";

const MAX_BEFORE: usize = 12;
const MAX_AFTER: usize = 12;

#[derive(Default)]
struct Pool {
    i32s: Vec<String>,
    i64s: Vec<String>,
    ps: Vec<String>,
    arrays: Vec<String>,
    p_objects: Vec<String>,
    a_objects: Vec<String>,
}

struct Generator<'a> {
    rng: &'a mut Lcg,
    next: usize,
    pool: Pool,
    text: String,
}

impl Generator<'_> {
    fn name(&mut self) -> String {
        self.next += 1;
        format!("v{}", self.next + 10)
    }

    fn pick(&mut self, from: &[String]) -> String {
        from[self.rng.below(from.len())].clone()
    }

    fn line(&mut self, line: String) {
        self.text += "        ";
        self.text += &line;
        self.text += "\n";
    }

    fn index(&mut self) -> String {
        if self.rng.below(2) == 0 {
            format!("{}.i32", self.rng.below(4))
        } else {
            let source = self.pick(&self.pool.i32s.clone());
            let masked = self.name();
            self.line(format!("{masked}.i32 = and {source} 3.i32;"));
            masked
        }
    }

    fn p_value(&mut self) -> String {
        if self.pool.ps.is_empty() || self.rng.below(4) == 0 {
            let a = self.pick(&self.pool.i32s.clone());
            let b = self.pick(&self.pool.i64s.clone());
            let n = self.name();
            self.line(format!("{n}.@P = call %mk {a} {b};"));
            self.pool.ps.push(n);
        }
        self.pick(&self.pool.ps.clone())
    }

    fn array_value(&mut self) -> String {
        if self.pool.arrays.is_empty() || self.rng.below(4) == 0 {
            let mut current = "undef.[i32; 4]".to_string();
            for k in 0..4 {
                let element = self.pick(&self.pool.i32s.clone());
                let n = self.name();
                self.line(format!(
                    "{n}.[i32; 4] = insert_value {current} {k}.i32 {element};"
                ));
                current = n;
            }
            self.pool.arrays.push(current);
        }
        self.pick(&self.pool.arrays.clone())
    }

    fn p_object(&mut self) -> String {
        if self.pool.p_objects.is_empty() || self.rng.below(4) == 0 {
            let p = self.p_value();
            let o = self.name();
            self.line(format!("{o}.objref<@P> = obj.alloc @P;"));
            self.line(format!("obj.store {o} {p};"));
            self.pool.p_objects.push(o);
        }
        self.pick(&self.pool.p_objects.clone())
    }

    fn a_object(&mut self) -> String {
        if self.pool.a_objects.is_empty() || self.rng.below(4) == 0 {
            let a = self.array_value();
            let o = self.name();
            self.line(format!("{o}.objref<[i32; 4]> = obj.alloc [i32; 4];"));
            self.line(format!("obj.store {o} {a};"));
            self.pool.a_objects.push(o);
        }
        self.pick(&self.pool.a_objects.clone())
    }

    /// One random operation.
    fn operation(&mut self) {
        match self.rng.below(22) {
            0 => {
                let (a, b, n) = (
                    self.pick(&self.pool.i32s.clone()),
                    self.pick(&self.pool.i32s.clone()),
                    self.name(),
                );
                let op = ["add", "sub", "mul", "xor", "or"][self.rng.below(5)];
                self.line(format!("{n}.i32 = {op} {a} {b};"));
                self.pool.i32s.push(n);
            }
            1 => {
                let (a, b, n) = (
                    self.pick(&self.pool.i64s.clone()),
                    self.pick(&self.pool.i64s.clone()),
                    self.name(),
                );
                let op = ["add", "sub", "mul", "xor"][self.rng.below(4)];
                self.line(format!("{n}.i64 = {op} {a} {b};"));
                self.pool.i64s.push(n);
            }
            2 => {
                let (a, n) = (self.pick(&self.pool.i32s.clone()), self.name());
                self.line(format!("{n}.i64 = zext {a} i64;"));
                self.pool.i64s.push(n);
            }
            3 => {
                let (a, n) = (self.pick(&self.pool.i64s.clone()), self.name());
                self.line(format!("{n}.i32 = trunc {a} i32;"));
                self.pool.i32s.push(n);
            }
            4 => {
                self.p_value();
            }
            5 => {
                let p = self.p_value();
                let n = self.name();
                if self.rng.below(2) == 0 {
                    let s = self.pick(&self.pool.i32s.clone());
                    self.line(format!("{n}.@P = insert_value {p} 0.i32 {s};"));
                } else {
                    let s = self.pick(&self.pool.i64s.clone());
                    self.line(format!("{n}.@P = insert_value {p} 1.i32 {s};"));
                }
                self.pool.ps.push(n);
            }
            6 => {
                let p = self.p_value();
                let n = self.name();
                if self.rng.below(2) == 0 {
                    self.line(format!("{n}.i32 = extract_value {p} 0.i32;"));
                    self.pool.i32s.push(n);
                } else {
                    self.line(format!("{n}.i64 = extract_value {p} 1.i32;"));
                    self.pool.i64s.push(n);
                }
            }
            7 => {
                self.array_value();
            }
            8 => {
                let a = self.array_value();
                let s = self.pick(&self.pool.i32s.clone());
                let k = self.rng.below(4);
                let n = self.name();
                self.line(format!("{n}.[i32; 4] = insert_value {a} {k}.i32 {s};"));
                self.pool.arrays.push(n);
            }
            9 => {
                let a = self.array_value();
                let k = self.rng.below(4);
                let n = self.name();
                self.line(format!("{n}.i32 = extract_value {a} {k}.i32;"));
                self.pool.i32s.push(n);
            }
            10 => {
                self.p_object();
            }
            11 => {
                let (o, p) = (self.p_object(), self.p_value());
                self.line(format!("obj.store {o} {p};"));
            }
            12 => {
                let o = self.p_object();
                let n = self.name();
                self.line(format!("{n}.@P = obj.load {o};"));
                self.pool.ps.push(n);
            }
            13 => {
                let o = self.p_object();
                let f = self.name();
                if self.rng.below(2) == 0 {
                    let s = self.pick(&self.pool.i32s.clone());
                    self.line(format!("{f}.objref<i32> = obj.proj {o} 0.i32;"));
                    self.line(format!("obj.store {f} {s};"));
                } else {
                    let s = self.pick(&self.pool.i64s.clone());
                    self.line(format!("{f}.objref<i64> = obj.proj {o} 1.i32;"));
                    self.line(format!("obj.store {f} {s};"));
                }
            }
            14 => {
                let o = self.p_object();
                let (f, n) = (self.name(), self.name());
                if self.rng.below(2) == 0 {
                    self.line(format!("{f}.objref<i32> = obj.proj {o} 0.i32;"));
                    self.line(format!("{n}.i32 = obj.load {f};"));
                    self.pool.i32s.push(n);
                } else {
                    self.line(format!("{f}.objref<i64> = obj.proj {o} 1.i32;"));
                    self.line(format!("{n}.i64 = obj.load {f};"));
                    self.pool.i64s.push(n);
                }
            }
            15 => {
                self.a_object();
            }
            16 => {
                let o = self.a_object();
                let index = self.index();
                let s = self.pick(&self.pool.i32s.clone());
                let e = self.name();
                self.line(format!("{e}.objref<i32> = obj.index {o} {index};"));
                self.line(format!("obj.store {e} {s};"));
            }
            17 => {
                let o = self.a_object();
                let index = self.index();
                let (e, n) = (self.name(), self.name());
                self.line(format!("{e}.objref<i32> = obj.index {o} {index};"));
                self.line(format!("{n}.i32 = obj.load {e};"));
                self.pool.i32s.push(n);
            }
            18 => {
                let o = self.a_object();
                let n = self.name();
                self.line(format!("{n}.[i32; 4] = obj.load {o};"));
                self.pool.arrays.push(n);
            }
            19 => {
                let (p, a, n) = (self.p_value(), self.array_value(), self.name());
                self.line(format!("{n}.i64 = call %sum {p} {a};"));
                self.pool.i64s.push(n);
            }
            20 => {
                let (p, n) = (self.p_value(), self.name());
                self.line(format!("{n}.@P = call %bump {p};"));
                self.pool.ps.push(n);
            }
            _ => {
                let (o, a) = (self.a_object(), self.array_value());
                self.line(format!("obj.store {o} {a};"));
            }
        }
    }
}

/// A program, with a loop in the middle that carries a struct and a sum and
/// writes an object, followed by a checksum of everything.
fn program(rng: &mut Lcg) -> String {
    let mut generator = Generator {
        rng,
        next: 0,
        pool: Pool {
            i32s: vec!["v0".to_string()],
            i64s: vec!["v1".to_string()],
            ..Pool::default()
        },
        text: String::new(),
    };
    let before = generator.rng.below(MAX_BEFORE);
    for _ in 0..before {
        generator.operation();
    }
    // The loop: a struct and a sum are carried; an object is written each pass.
    let carried = generator.p_value();
    let object = generator.p_object();
    let elements = generator.a_object();
    let bound = generator.name();
    generator.line(format!("{bound}.i32 = and v0 7.i32;"));
    let entry = format!("block{}", 0);
    let (counter, state, sum, next_counter, next_state, next_sum) = (
        generator.name(),
        generator.name(),
        generator.name(),
        generator.name(),
        generator.name(),
        generator.name(),
    );
    // Most loops keep the struct in an object. In the others it is a phi.
    let phi_state = generator.rng.below(10) < 3;
    let state_object = if phi_state {
        String::new()
    } else {
        let o = generator.name();
        generator.line(format!("{o}.objref<@P> = obj.alloc @P;"));
        generator.line(format!("obj.store {o} {carried};"));
        o
    };
    generator.text += "        jump block1;\n    block1:\n";
    generator.text += &format!(
        "        {counter}.i32 = phi (0.i32 {entry}) ({next_counter} block2);\n        {sum}.i64 = phi (0.i64 {entry}) ({next_sum} block2);\n"
    );
    if phi_state {
        generator.text +=
            &format!("        {state}.@P = phi ({carried} {entry}) ({next_state} block2);\n");
    }
    let both = generator.rng.below(2) == 0;
    let c2 = if both {
        generator.name()
    } else {
        String::new()
    };
    let slot = generator.name();
    let (cond, a, b, c, d, e, f, g, h) = (
        generator.name(),
        generator.name(),
        generator.name(),
        generator.name(),
        generator.name(),
        generator.name(),
        generator.name(),
        generator.name(),
        generator.name(),
    );
    let c2 = if both { c2 } else { c.clone() };
    let second = if both {
        let n = generator.name();
        format!(
            "        {n}.i64 = extract_value {state} 1.i32;\n        {c2}.@P = insert_value {c} 1.i32 {n};\n"
        )
    } else {
        String::new()
    };
    generator.text += &format!(
        "        {cond}.i1 = lt {counter} {bound};\n        br {cond} block2 block3;\n    block2:\n"
    );
    if !phi_state {
        generator.text += &format!("        {state}.@P = obj.load {state_object};\n");
    }
    generator.text += &format!(
        "        {a}.i32 = extract_value {state} 0.i32;\n        {b}.i32 = add {a} {counter};\n        {c}.@P = insert_value {state} 0.i32 {b};\n{second}        {next_state}.@P = call %bump {c2};\n        {d}.i64 = extract_value {state} 1.i32;\n        {next_sum}.i64 = add {sum} {d};\n        {slot}.i32 = and {counter} 3.i32;\n        {e}.objref<i32> = obj.index {elements} {slot};\n        obj.store {e} {b};\n        {f}.i64 = zext {b} i64;\n        {g}.objref<i64> = obj.proj {object} 1.i32;\n        obj.store {g} {f};\n        {h}.@P = obj.load {object};\n        obj.store {object} {h};\n        {next_counter}.i32 = add {counter} 1.i32;\n"
    );
    if !phi_state {
        generator.text += &format!("        obj.store {state_object} {next_state};\n");
    }
    generator.text += "        jump block1;\n    block3:\n";
    if phi_state {
        generator.pool.ps.push(state.clone());
    } else {
        let fin = generator.name();
        generator.line(format!("{fin}.@P = obj.load {state_object};"));
        generator.pool.ps.push(fin);
    }
    generator.pool.i64s.push(sum);
    let after = generator.rng.below(MAX_AFTER);
    for _ in 0..after {
        generator.operation();
    }
    // Checksum of everything.
    let mut terms: Vec<String> = Vec::new();
    let pool = std::mem::take(&mut generator.pool);
    for v in &pool.i32s {
        let n = generator.name();
        generator.line(format!("{n}.i64 = zext {v} i64;"));
        terms.push(n);
    }
    terms.extend(pool.i64s.iter().cloned());
    for p in &pool.ps {
        let (x, y, z) = (generator.name(), generator.name(), generator.name());
        generator.line(format!("{x}.i32 = extract_value {p} 0.i32;"));
        generator.line(format!("{y}.i64 = extract_value {p} 1.i32;"));
        generator.line(format!("{z}.i64 = zext {x} i64;"));
        terms.push(y);
        terms.push(z);
    }
    for array in &pool.arrays {
        for k in 0..4 {
            let (x, y) = (generator.name(), generator.name());
            generator.line(format!("{x}.i32 = extract_value {array} {k}.i32;"));
            generator.line(format!("{y}.i64 = zext {x} i64;"));
            terms.push(y);
        }
    }
    for o in &pool.p_objects {
        let (p, x, y, z) = (
            generator.name(),
            generator.name(),
            generator.name(),
            generator.name(),
        );
        generator.line(format!("{p}.@P = obj.load {o};"));
        generator.line(format!("{x}.i32 = extract_value {p} 0.i32;"));
        generator.line(format!("{y}.i64 = extract_value {p} 1.i32;"));
        generator.line(format!("{z}.i64 = zext {x} i64;"));
        terms.push(y);
        terms.push(z);
    }
    for o in &pool.a_objects {
        let array = generator.name();
        generator.line(format!("{array}.[i32; 4] = obj.load {o};"));
        for k in 0..4 {
            let (x, y) = (generator.name(), generator.name());
            generator.line(format!("{x}.i32 = extract_value {array} {k}.i32;"));
            generator.line(format!("{y}.i64 = zext {x} i64;"));
            terms.push(y);
        }
    }
    let mut accumulator = "0.i64".to_string();
    for term in terms {
        let (m, a) = (generator.name(), generator.name());
        generator.line(format!("{m}.i64 = mul {accumulator} 1099511628211.i64;"));
        generator.line(format!("{a}.i64 = add {m} {term};"));
        accumulator = a;
    }
    generator.line(format!("return {accumulator};"));
    format!(
        "{PRELUDE}func public %f(v0.i32, v1.i64) -> i64 {{\n    block0:\n{}}}\n",
        generator.text
    )
}

fn native_triple() -> TargetTriple {
    let architecture = if cfg!(target_arch = "x86_64") {
        Architecture::X86_64
    } else {
        Architecture::Aarch64
    };
    TargetTriple::new(architecture, Vendor::Unknown, OperatingSystem::Native)
}

fn parse(target: &str, source: &str) -> sonatina_ir::Module {
    let module = sonatina_parser::parse_module(&format!("target = \"{target}\"\n{source}"))
        .unwrap_or_else(|errors| panic!("the program should parse: {errors:?}\n{source}"))
        .module;
    let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    assert!(!report.has_errors(), "{report}\n{source}");
    module
}

#[test]
fn generated_aggregate_programs_agree_with_the_native_backend() {
    let mut rng = Lcg(0x5eed_a66e);
    let inputs = [
        (0i32, 0i64),
        (3, -5),
        (7, 1 << 40),
        (-1, i64::MAX),
        (12345, 987_654_321),
    ];
    for case in 0..200 {
        let source = program(&mut rng);
        for level in [OptLevel::O0, OptLevel::O2] {
            let mut compile = Compile::new(
                parse(&native_triple().to_string(), &source),
                CraneliftJitBackend::new(),
            )
            .with_opt_level(level);
            compile.optimize();
            let native = compile.compile().unwrap_or_else(|errors| {
                panic!("native, case {case} {level:?}: {errors:?}\n{source}")
            });
            let f: unsafe extern "C" fn(i32, i64) -> i64 =
                unsafe { std::mem::transmute(native.function_address("f").unwrap()) };
            let bytes = Compile::new(parse("wasm32-unknown-native", &source), WasmBackend::new())
                .with_opt_level(level)
                .compile()
                .unwrap_or_else(|errors| {
                    panic!("wasm, case {case} {level:?}: {errors:?}\n{source}")
                })
                .into_bytes();
            wasmparser::Validator::new()
                .validate_all(&bytes)
                .unwrap_or_else(|error| panic!("invalid module, case {case}: {error}\n{source}"));
            let mut machine = Machine::new(&bytes);
            let wasm_f = machine.func("f");
            for (n, x) in inputs {
                let want = unsafe { f(n, x) };
                let got = machine.call(&wasm_f, &[Val::I32(n), Val::I64(x)])[0].unwrap_i64();
                assert_eq!(
                    got, want,
                    "case {case} {level:?} input ({n}, {x})\n{source}"
                );
            }
        }
    }
}
