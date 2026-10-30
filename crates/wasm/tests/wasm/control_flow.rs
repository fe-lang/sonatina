//! Control flow: loops, phis, switches, traps and optimizer agreement.

use sonatina_codegen::{Compile, OptLevel};
use sonatina_wasm::WasmBackend;
use wasmtime::Val;

use crate::harness::{Machine, compile_valid, i32s, parse, validate};

fn machine(source: &str) -> Machine {
    Machine::new(&compile_valid(&parse(source)))
}

const SUM_TO: &str = "func public %sum_to(v0.i32) -> i32 {
    block0:
        jump block1;
    block1:
        v1.i32 = phi (0.i32 block0) (v4 block2);
        v2.i32 = phi (1.i32 block0) (v5 block2);
        v3.i1 = gt v2 v0;
        br v3 block3 block2;
    block2:
        v4.i32 = add v1 v2;
        v5.i32 = add v2 1.i32;
        jump block1;
    block3:
        return v1;
}
";

#[test]
fn loops_carry_values_through_phis() {
    let mut machine = machine(SUM_TO);
    let sum_to = machine.func("sum_to");
    for (n, expected) in [(0, 0), (1, 1), (10, 55), (1000, 500_500)] {
        assert_eq!(i32s(&machine.call(&sum_to, &[Val::I32(n)])), [expected]);
    }
}

#[test]
fn phis_are_a_parallel_copy() {
    // Fibonacci swaps two phis each iteration: (a, b) = (b, a + b).
    let source = "func public %fib(v0.i64) -> i64 {
    block0:
        jump block1;
    block1:
        v1.i64 = phi (0.i64 block0) (v2 block2);
        v2.i64 = phi (1.i64 block0) (v5 block2);
        v3.i64 = phi (0.i64 block0) (v6 block2);
        v4.i1 = eq v3 v0;
        br v4 block3 block2;
    block2:
        v5.i64 = add v1 v2;
        v6.i64 = add v3 1.i64;
        jump block1;
    block3:
        return v1;
}
";
    let mut machine = machine(source);
    let fib = machine.func("fib");
    let expected = [0i64, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
    for (n, want) in expected.iter().enumerate() {
        assert_eq!(
            machine.call(&fib, &[Val::I64(n as i64)])[0].unwrap_i64(),
            *want
        );
    }
    assert_eq!(
        machine.call(&fib, &[Val::I64(90)])[0].unwrap_i64(),
        2_880_067_194_370_816_120
    );
}

#[test]
fn a_loop_may_start_at_the_entry_block() {
    // The loop header is the entry block, which WebAssembly cannot re-enter,
    // so the translation adds a prologue. State lives in memory.
    let source = "func public %count_down() -> i32 {
    block0:
        v0.i32 = mload 16.i32 i32;
        v1.i32 = sub v0 1.i32;
        mstore 16.i32 v1 i32;
        v2.i1 = is_zero v1;
        br v2 block1 block0;
    block1:
        return v1;
}
";
    let mut machine = machine(source);
    machine.write(16, &5i32.to_le_bytes());
    let count_down = machine.func("count_down");
    assert_eq!(i32s(&machine.call(&count_down, &[])), [0]);
    assert_eq!(machine.read(16, 4), 0i32.to_le_bytes());
}

#[test]
fn memory_loaded_before_a_loop_keeps_its_snapshot() {
    // `v0` is read once. The loop changes the memory it was read from, and the
    // value must not be re-read after the loop.
    let source = "func public %snapshot() -> (i32, i32) {
    block0:
        v0.i32 = mload 16.i32 i32;
        jump block1;
    block1:
        v1.i32 = phi (0.i32 block0) (v3 block1);
        v2.i32 = add v0 100.i32;
        mstore 16.i32 v2 i32;
        v3.i32 = add v1 1.i32;
        v4.i1 = eq v3 3.i32;
        br v4 block2 block1;
    block2:
        v5.i32 = mload 16.i32 i32;
        return (v0, v5);
}
";
    let mut machine = machine(source);
    machine.write(16, &7i32.to_le_bytes());
    let snapshot = machine.func("snapshot");
    assert_eq!(i32s(&machine.call(&snapshot, &[])), [7, 107]);
}

#[test]
fn nested_branches_and_unreachable_blocks() {
    let source = "func public %classify(v0.i32) -> i32 {
    block0:
        v1.i1 = slt v0 0.i32;
        br v1 block1 block2;
    block1:
        return -1.i32;
    block2:
        v2.i1 = is_zero v0;
        br v2 block3 block4;
    block3:
        return 0.i32;
    block4:
        return 1.i32;
    block5:
        v3.i32 = add v0 v0;
        return v3;
}
";
    let mut machine = machine(source);
    let classify = machine.func("classify");
    for (input, want) in [(-5, -1), (0, 0), (9, 1), (i32::MIN, -1), (i32::MAX, 1)] {
        assert_eq!(i32s(&machine.call(&classify, &[Val::I32(input)])), [want]);
    }
}

#[test]
fn br_table_selects_a_case_a_default_or_traps() {
    let source = "func public %with_default(v0.i32) -> i32 {
    block0:
        br_table v0 block4 (1.i32 block1) (2.i32 block2) (-7.i32 block3);
    block1:
        return 10.i32;
    block2:
        return 20.i32;
    block3:
        return 30.i32;
    block4:
        return 99.i32;
}
func public %no_default(v0.i32) -> i32 {
    block0:
        br_table v0 (5.i32 block1);
    block1:
        return 50.i32;
}
func public %joined(v0.i64) -> i64 {
    block0:
        br_table v0 block3 (0.i64 block1) (1.i64 block2);
    block1:
        jump block3;
    block2:
        jump block3;
    block3:
        v1.i64 = phi (100.i64 block0) (200.i64 block1) (300.i64 block2);
        return v1;
}
";
    let mut machine = machine(source);
    let with_default = machine.func("with_default");
    for (input, want) in [(1, 10), (2, 20), (-7, 30), (0, 99), (3, 99), (i32::MIN, 99)] {
        assert_eq!(
            i32s(&machine.call(&with_default, &[Val::I32(input)])),
            [want]
        );
    }
    let no_default = machine.func("no_default");
    assert_eq!(i32s(&machine.call(&no_default, &[Val::I32(5)])), [50]);
    assert!(machine.try_call(&no_default, &[Val::I32(6)]).is_err());
    let joined = machine.func("joined");
    for (input, want) in [(0, 200), (1, 300), (2, 100)] {
        assert_eq!(
            machine.call(&joined, &[Val::I64(input)])[0].unwrap_i64(),
            want
        );
    }
}

#[test]
fn unreachable_traps() {
    let source = "func public %halt(v0.i32) -> i32 {
    block0:
        br v0 block1 block2;
    block1:
        unreachable;
    block2:
        return 1.i32;
}
";
    let mut machine = machine(source);
    let halt = machine.func("halt");
    assert_eq!(i32s(&machine.call(&halt, &[Val::I32(0)])), [1]);
    assert!(machine.try_call(&halt, &[Val::I32(1)]).is_err());
}

#[test]
fn branching_on_a_64_bit_condition_tests_for_nonzero() {
    let source = "func public %is_set(v0.i64) -> i32 {
    block0:
        br v0 block1 block2;
    block1:
        return 1.i32;
    block2:
        return 0.i32;
}
";
    let mut machine = machine(source);
    let is_set = machine.func("is_set");
    for (input, want) in [(0, 0), (1, 1), (1 << 40, 1), (-1, 1)] {
        assert_eq!(i32s(&machine.call(&is_set, &[Val::I64(input)])), [want]);
    }
}

#[test]
fn the_optimizer_does_not_change_results() {
    let source = format!(
        "{SUM_TO}func public %mix(v0.i32, v1.i32) -> i32 {{
    block0:
        v2.i32 = call %sum_to v0;
        (v3.i32, v4.i1) = uaddo v2 v1;
        br v4 block1 block2;
    block1:
        return 0.i32;
    block2:
        v5.i32 = mul v3 3.i32;
        return v5;
}}
"
    );
    let inputs = [(0, 0), (10, 5), (1000, 7), (100_000, 1), (70_000, 0)];
    let mut unoptimized = machine(&source);
    let reference = unoptimized.func("mix");
    for level in [OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let bytes = Compile::new(parse(&source), WasmBackend::new())
            .with_opt_level(level)
            .compile()
            .expect("optimized compilation succeeds")
            .into_bytes();
        validate(&bytes);
        let mut optimized = Machine::new(&bytes);
        let func = optimized.func("mix");
        for (a, b) in inputs {
            let args = [Val::I32(a), Val::I32(b)];
            assert_eq!(
                i32s(&optimized.call(&func, &args)),
                i32s(&unoptimized.call(&reference, &args)),
                "{level:?}: mix({a}, {b})"
            );
        }
    }
}

#[test]
fn irreducible_control_flow_is_structured() {
    // Blocks 1 and 2 form a loop that can be entered at either block. Each
    // adds to its own counter in memory until it reaches a limit and then
    // hands over to the other or leaves.
    let source = "func public %cycle(v0.i1) -> (i32, i32) {
    block0:
        br v0 block1 block2;
    block1:
        v1.i32 = mload 16.i32 i32;
        v2.i32 = add v1 1.i32;
        mstore 16.i32 v2 i32;
        v3.i1 = lt v2 5.i32;
        br v3 block2 block3;
    block2:
        v4.i32 = mload 20.i32 i32;
        v5.i32 = add v4 10.i32;
        mstore 20.i32 v5 i32;
        v6.i1 = lt v5 50.i32;
        br v6 block1 block3;
    block3:
        v7.i32 = mload 16.i32 i32;
        v8.i32 = mload 20.i32 i32;
        return (v7, v8);
}
";
    // The same control flow, simulated.
    let simulate = |start_in_first: bool| {
        let (mut a, mut b) = (0, 0);
        let mut in_first = start_in_first;
        loop {
            if in_first {
                a += 1;
                if a < 5 {
                    in_first = false;
                } else {
                    break;
                }
            } else {
                b += 10;
                if b < 50 {
                    in_first = true;
                } else {
                    break;
                }
            }
        }
        (a, b)
    };
    for start_in_first in [true, false] {
        let mut machine = machine(source);
        let cycle = machine.func("cycle");
        let results = i32s(&machine.call(&cycle, &[Val::I32(i32::from(start_in_first))]));
        let (a, b) = simulate(start_in_first);
        assert_eq!(results, [a, b], "start_in_first = {start_in_first}");
    }
}

#[test]
fn loops_without_an_exit_and_bodies_that_never_return_are_accepted() {
    let source = "func public %spin(v0.i32) -> i32 {
    block0:
        br v0 block1 block2;
    block1:
        jump block1;
    block2:
        return 0.i32;
}
func public %never() -> i32 {
    block0:
        unreachable;
}
";
    let mut machine = machine(source);
    let spin = machine.func("spin");
    assert_eq!(i32s(&machine.call(&spin, &[Val::I32(0)])), [0]);
    let never = machine.func("never");
    assert!(machine.try_call(&never, &[]).is_err());
}

// ---------------------------------------------------------------------------
// Reads, writes and calls stay in program order.
// ---------------------------------------------------------------------------

/// One step of a generated straight-line program over eight 32-bit cells of
/// memory at addresses 64, 68, ...
#[derive(Clone, Copy, Debug)]
enum Step {
    Load(usize),
    Store(usize, usize),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Xor(usize, usize),
    /// A call that writes cell 7 with its argument and returns it plus one.
    Bump(usize),
}

fn random_steps(rng: &mut crate::Lcg, count: usize) -> Vec<Step> {
    // Values 0 and 1 are the parameters. Every step refers to earlier values.
    let mut steps = Vec::new();
    let mut values = 2;
    for _ in 0..count {
        let pick = |rng: &mut crate::Lcg, values: usize| (rng.next() % values as u64) as usize;
        let cell = (rng.next() % 8) as usize;
        let step = match rng.next() % 9 {
            0 | 1 => Step::Load(cell),
            2 | 3 => Step::Store(cell, pick(rng, values)),
            4 => Step::Add(pick(rng, values), pick(rng, values)),
            5 => Step::Sub(pick(rng, values), pick(rng, values)),
            6 => Step::Mul(pick(rng, values), pick(rng, values)),
            7 => Step::Xor(pick(rng, values), pick(rng, values)),
            _ => Step::Bump(pick(rng, values)),
        };
        if !matches!(step, Step::Store(..)) {
            values += 1;
        }
        steps.push(step);
        // Often follow a read with a pure operation on its value.
        if matches!(step, Step::Load(_) | Step::Bump(_)) && !rng.next().is_multiple_of(3) {
            let newest = values - 1;
            let other = (rng.next() % values as u64) as usize;
            steps.push(match rng.next() % 3 {
                0 => Step::Add(newest, other),
                1 => Step::Xor(other, newest),
                _ => Step::Mul(newest, other),
            });
            values += 1;
        }
    }
    steps
}

/// The IR of a program, and its result for the given memory and parameters.
fn run_steps(steps: &[Step], memory: &mut [i32; 8], params: [i32; 2]) -> (String, i32) {
    let mut ir = String::from(
        "func private %bump(v0.i32) -> i32 {
    block0:
        v1.*i32 = int_to_ptr 92.i32 *i32;
        mstore v1 v0 i32;
        v2.i32 = add v0 1.i32;
        return v2;
}
func public %f(v0.i32, v1.i32) -> i32 {
    block0:
",
    );
    let mut values = vec![params[0], params[1]];
    // Value numbers: the parameters are v0 and v1, a step that produces a value
    // is v(2 + its rank), and addresses are v1000 + step.
    for (index, step) in steps.iter().enumerate() {
        let name = values.len();
        match *step {
            Step::Load(cell) => {
                ir += &format!(
                    "        v{}.*i32 = int_to_ptr {}.i32 *i32;\n        v{name}.i32 = mload v{} i32;\n",
                    1000 + index,
                    64 + 4 * cell,
                    1000 + index
                );
                values.push(memory[cell]);
            }
            Step::Store(cell, from) => {
                ir += &format!(
                    "        v{}.*i32 = int_to_ptr {}.i32 *i32;\n        mstore v{} v{from} i32;\n",
                    1000 + index,
                    64 + 4 * cell,
                    1000 + index
                );
                memory[cell] = values[from];
            }
            Step::Add(a, b) => {
                ir += &format!("        v{name}.i32 = add v{a} v{b};\n");
                values.push(values[a].wrapping_add(values[b]));
            }
            Step::Sub(a, b) => {
                ir += &format!("        v{name}.i32 = sub v{a} v{b};\n");
                values.push(values[a].wrapping_sub(values[b]));
            }
            Step::Mul(a, b) => {
                ir += &format!("        v{name}.i32 = mul v{a} v{b};\n");
                values.push(values[a].wrapping_mul(values[b]));
            }
            Step::Xor(a, b) => {
                ir += &format!("        v{name}.i32 = xor v{a} v{b};\n");
                values.push(values[a] ^ values[b]);
            }
            Step::Bump(from) => {
                ir += &format!("        v{name}.i32 = call %bump v{from};\n");
                memory[7] = values[from];
                values.push(values[from].wrapping_add(1));
            }
        }
    }
    // Combine the values that no step uses, at the end, so that results of
    // early reads are held across later writes.
    let mut used = vec![false; values.len()];
    for step in steps {
        match *step {
            Step::Load(_) => {}
            Step::Store(_, a) | Step::Bump(a) => used[a] = true,
            Step::Add(a, b) | Step::Sub(a, b) | Step::Mul(a, b) | Step::Xor(a, b) => {
                used[a] = true;
                used[b] = true;
            }
        }
    }
    let mut accumulator = String::from("0.i32");
    let mut result = 0i32;
    for (index, value) in values.iter().enumerate() {
        if used[index] {
            continue;
        }
        ir += &format!(
            "        v{}.i32 = mul {accumulator} 31.i32;\n",
            2000 + index
        );
        ir += &format!(
            "        v{}.i32 = add v{} v{index};\n",
            3000 + index,
            2000 + index
        );
        accumulator = format!("v{}", 3000 + index);
        result = result.wrapping_mul(31).wrapping_add(*value);
    }
    ir += &format!("        return {accumulator};\n}}\n");
    (ir, result)
}

#[test]
fn generated_programs_keep_reads_writes_and_calls_in_order() {
    let mut rng = crate::Lcg(0x0dd5_eed5);
    for case in 0..250 {
        let steps = random_steps(&mut rng, 8 + (case % 24));
        let memory = [3, 1, 4, 1, 5, 9, 2, 6];
        let params = [rng.next() as i32, rng.next() as i32];
        let (source, want) = run_steps(&steps, &mut memory.clone(), params);
        let mut machine = Machine::new(&compile_valid(&parse(&source)));
        let start: Vec<u8> = memory.iter().flat_map(|v| v.to_le_bytes()).collect();
        machine.write(64, &start);
        let f = machine.func("f");
        let got = machine.call(&f, &[Val::I32(params[0]), Val::I32(params[1])])[0].unwrap_i32();
        assert_eq!(got, want, "case {case}: {steps:?}\n{source}");
        let after = machine.read(64, 32);
        let mut expected = memory;
        let _ = run_steps(&steps, &mut expected, params);
        let want_memory: Vec<u8> = expected.iter().flat_map(|v| v.to_le_bytes()).collect();
        assert_eq!(after, want_memory, "case {case}: memory after");
    }
}
