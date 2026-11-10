//! Tail calls: recursion in constant stack, in WebAssembly's and the module's.

use sonatina_codegen::OptLevel;
use sonatina_wasm::WasmBackend;
use wasmparser::{Operator, Parser, Payload};
use wasmtime::Val;

use crate::{harness::Machine, memory_runtime::build_with};

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os];

/// The number of `return_call`s in a module.
fn return_calls(bytes: &[u8]) -> usize {
    let mut count = 0;
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::CodeSectionEntry(body) = payload.unwrap() {
            let operators = body.get_operators_reader().unwrap();
            count += operators
                .into_iter()
                .filter(|operator| matches!(operator, Ok(Operator::ReturnCall { .. })))
                .count();
        }
    }
    count
}

#[test]
fn a_recursive_cycle_makes_tail_calls() {
    // Five million calls deep: far beyond an engine's stack without them.
    let source = "func private %count(v0.i64, v1.i64) -> i64 {
    block0:
        v2.i1 = eq v0 0.i64;
        br v2 block1 block2;
    block1:
        return v1;
    block2:
        v3.i64 = sub v0 1.i64;
        v4.i64 = add v1 v0;
        v5.i64 = call %count v3 v4;
        return v5;
}
func private %even(v0.i64) -> i32 {
    block0:
        v1.i1 = eq v0 0.i64;
        br v1 block1 block2;
    block1:
        return 1.i32;
    block2:
        v2.i64 = sub v0 1.i64;
        v3.i32 = call %odd v2;
        return v3;
}
func private %odd(v0.i64) -> i32 {
    block0:
        v1.i1 = eq v0 0.i64;
        br v1 block1 block2;
    block1:
        return 0.i32;
    block2:
        v2.i64 = sub v0 1.i64;
        v3.i32 = call %even v2;
        return v3;
}
func public %sum(v0.i64) -> i64 {
    block0:
        v1.i64 = call %count v0 0.i64;
        return v1;
}
func public %is_even(v0.i64) -> i32 {
    block0:
        v1.i32 = call %even v0;
        return v1;
}";
    for level in LEVELS {
        let bytes = build_with(source, level, WasmBackend::new());
        assert_eq!(return_calls(&bytes), 3, "{level:?}");
        let mut machine = Machine::new(&bytes);
        let sum = machine.func("sum");
        let n = 5_000_000;
        assert_eq!(
            machine.call(&sum, &[Val::I64(n)])[0].unwrap_i64(),
            n * (n + 1) / 2,
            "{level:?}"
        );
        let is_even = machine.func("is_even");
        for (n, want) in [(5_000_000, 1), (4_999_999, 0)] {
            assert_eq!(
                machine.call(&is_even, &[Val::I64(n)])[0].unwrap_i32(),
                want,
                "{level:?}"
            );
        }
    }
}

#[test]
fn a_tail_call_reuses_the_frame_of_its_caller() {
    // Each call of `walk` builds a pair in its frame and passes on the pair
    // it received. A million frames of 16 bytes would not fit a stack of
    // 64 KiB, so each callee must start where its caller did.
    let source = "type @Pair = {i64, i64};
func private %walk(v0.i64, v1.@Pair) -> i64 {
    block0:
        v2.i1 = eq v0 0.i64;
        br v2 block1 block2;
    block1:
        v3.i64 = extract_value v1 0.i32;
        v4.i64 = extract_value v1 1.i32;
        v5.i64 = add v3 v4;
        return v5;
    block2:
        v6.@Pair = insert_value v1 1.i32 v0;
        v7.i64 = extract_value v6 1.i32;
        v8.i64 = sub v7 1.i64;
        v9.i64 = call %walk v8 v1;
        return v9;
}
func public %run(v0.i64) -> i64 {
    block0:
        v1.@Pair = insert_value undef.@Pair 0.i32 40.i64;
        v2.@Pair = insert_value v1 1.i32 2.i64;
        v3.i64 = call %walk v0 v2;
        return v3;
}";
    for level in LEVELS {
        let bytes = build_with(source, level, WasmBackend::new().with_stack_size(1 << 16));
        let mut machine = Machine::new(&bytes);
        let run = machine.func("run");
        assert_eq!(
            machine.call(&run, &[Val::I64(1_000_000)])[0].unwrap_i64(),
            42,
            "{level:?}"
        );
    }
}

#[test]
fn an_aggregate_built_in_the_frame_outlives_a_call_in_tail_position() {
    // `step` passes a pair it built in its own frame, so the callee's frame
    // must not replace it: the callee reads the pair after writing its own.
    let source = "type @Pair = {i64, i64};
func private %step(v0.i64, v1.@Pair) -> i64 {
    block0:
        v2.i1 = eq v0 0.i64;
        br v2 block1 block2;
    block1:
        v3.i64 = extract_value v1 0.i32;
        v4.i64 = extract_value v1 1.i32;
        v5.i64 = add v3 v4;
        return v5;
    block2:
        v6.i64 = extract_value v1 0.i32;
        v7.i64 = add v6 v0;
        v8.@Pair = insert_value v1 0.i32 v7;
        v9.@Pair = insert_value v8 1.i32 v0;
        v10.i64 = sub v0 1.i64;
        v11.i64 = call %step v10 v9;
        return v11;
}
func public %run(v0.i64) -> i64 {
    block0:
        v1.@Pair = insert_value undef.@Pair 0.i32 0.i64;
        v2.@Pair = insert_value v1 1.i32 0.i64;
        v3.i64 = call %step v0 v2;
        return v3;
}";
    for level in LEVELS {
        let bytes = build_with(source, level, WasmBackend::new());
        let mut machine = Machine::new(&bytes);
        let run = machine.func("run");
        // The first field sums 100..=1 and the second ends at 1.
        assert_eq!(
            machine.call(&run, &[Val::I64(100)])[0].unwrap_i64(),
            5051,
            "{level:?}"
        );
    }
}
