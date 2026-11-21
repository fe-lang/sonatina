//! Tail calls: recursion in constant stack, in WebAssembly's and the module's.

use sonatina_codegen::OptLevel;
use sonatina_wasm::WasmBackend;
use wasmparser::{Operator, Parser, Payload};
use wasmtime::Val;

use crate::{harness::Machine, memory_runtime::build_with};

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os];

/// The number of operators of a module that `matches` picks.
fn operators(bytes: &[u8], matches: impl Fn(&Operator) -> bool) -> usize {
    let mut count = 0;
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::CodeSectionEntry(body) = payload.unwrap() {
            let operators = body.get_operators_reader().unwrap();
            count += operators
                .into_iter()
                .filter(|operator| matches(operator.as_ref().unwrap()))
                .count();
        }
    }
    count
}

/// The number of `return_call`s in a module.
fn return_calls(bytes: &[u8]) -> usize {
    operators(bytes, |operator| {
        matches!(operator, Operator::ReturnCall { .. })
    })
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
    // `@Pair` has more fields than a value held in parts, so it is in
    // memory. Each call of `walk` builds a pair in its frame and passes on
    // the pair it received. A million frames of 48 bytes would not fit a
    // stack of 64 KiB, so each callee must start where its caller did.
    let source = "type @Pair = {i64, i64, i64, i64, i64, i64};
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
        v2.@Pair = agg.make @Pair 40.i64 2.i64 0.i64 0.i64 0.i64 0.i64;
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
    // `@Pair`, of six fields, is in memory. `step` passes a pair it built in
    // its own frame, so the callee's frame must not replace it: the callee
    // reads the pair after writing its own.
    let source = "type @Pair = {i64, i64, i64, i64, i64, i64};
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
        v2.@Pair = agg.make @Pair 0.i64 0.i64 0.i64 0.i64 0.i64 0.i64;
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

#[test]
fn handlers_pass_a_cursor_held_in_parts_in_constant_stack() {
    // An interpreter in the style of fevm: each handler takes a cursor of
    // five parts, builds the next one and dispatches on the opcode at its
    // `pc` through a `br_table` whose arms tail-call the handlers. A cursor
    // in memory would take a slot of each handler's frame and keep it alive
    // across the call; held in parts, it takes none, so a million steps run
    // in a stack of 4 KiB and in the engine's.
    let source = "type @Cursor = {*i8, i32, i64, *i64, i32};
func private %dispatch(v0.@Cursor) -> i64 {
    block0:
        v1.*i8 = extract_value v0 0.i32;
        v2.i32 = extract_value v0 1.i32;
        v3.i32 = and v2 3.i32;
        v4.*i8 = gep v1 v3;
        v5.i8 = mload v4 i8;
        br_table v5 block4 (0.i8 block1) (1.i8 block2) (2.i8 block3);
    block1:
        v6.i64 = call %step v0;
        return v6;
    block2:
        v7.i64 = call %add v0;
        return v7;
    block3:
        v8.i64 = call %double v0;
        return v8;
    block4:
        v9.i64 = extract_value v0 2.i32;
        return v9;
}
func private %step(v0.@Cursor) -> i64 {
    block0:
        v1.i32 = extract_value v0 4.i32;
        v2.i1 = eq v1 0.i32;
        br v2 block1 block2;
    block1:
        v3.i64 = extract_value v0 2.i64;
        return v3;
    block2:
        v4.i32 = sub v1 1.i32;
        v5.i32 = extract_value v0 1.i32;
        v6.i32 = add v5 1.i32;
        v7.@Cursor = insert_value v0 1.i32 v6;
        v8.@Cursor = insert_value v7 4.i32 v4;
        v9.i64 = call %dispatch v8;
        return v9;
}
func private %add(v0.@Cursor) -> i64 {
    block0:
        v1.*i64 = extract_value v0 3.i32;
        v2.i64 = mload v1 i64;
        v3.i64 = extract_value v0 2.i32;
        v4.i64 = add v3 v2;
        v5.@Cursor = insert_value v0 2.i32 v4;
        v6.i64 = call %step v5;
        return v6;
}
func private %double(v0.@Cursor) -> i64 {
    block0:
        v1.i64 = extract_value v0 2.i32;
        v2.i64 = shl 1.i64 v1;
        v3.i64 = and v2 4294967295.i64;
        v4.@Cursor = insert_value v0 2.i32 v3;
        v5.i64 = call %step v4;
        return v5;
}
func public %run(v0.i32, v1.*i8, v2.*i64) -> i64 {
    block0:
        v3.@Cursor = agg.make @Cursor v1 0.i32 0.i64 v2 v0;
        v4.i64 = call %dispatch v3;
        return v4;
}";
    for level in LEVELS {
        let bytes = build_with(source, level, WasmBackend::new().with_stack_size(4096));
        assert!(return_calls(&bytes) >= 4, "{level:?}");
        let mut machine = Machine::new(&bytes);
        let base = machine.memory_size();
        machine.grow_memory(1);
        // The code cycles through step, add, double, step; the operand of
        // `add` is 3.
        machine.write(base, &[0, 1, 2, 0]);
        machine.write(base + 8, &3i64.to_le_bytes());
        let run = machine.func("run");
        let steps = 1_000_000;
        let mut want: i64 = 0;
        for pc in 0..steps {
            match pc % 4 {
                1 => want += 3,
                2 => want = (want << 1) & 0xffff_ffff,
                _ => {}
            }
        }
        let got = machine.call(
            &run,
            &[
                Val::I32(steps),
                Val::I32(base as i32),
                Val::I32(base as i32 + 8),
            ],
        );
        assert_eq!(got[0].unwrap_i64(), want, "{level:?}");
    }
}

#[test]
fn a_switch_of_tail_calls_is_one_indirect_tail_call_at_os() {
    // Every destination of `%next`'s `br_table`, the default included,
    // tail-calls with the cursor, so at `Os` the switch is one
    // `return_call_indirect` through a table of the handlers, which both
    // handlers share. Other levels keep direct calls, which engines make
    // faster. The opcode is a byte, so the table has 256 entries and no
    // index falls outside it: 3 runs `%halt` from the default, which is not
    // inlined, so that the default begins with its call.
    let source = "type @Cursor = {*i8, i32, i64};
func private %next(v0.@Cursor) -> i64 {
    block0:
        v1.*i8 = extract_value v0 0.i32;
        v2.i32 = extract_value v0 1.i32;
        v3.*i8 = gep v1 v2;
        v4.i8 = mload v3 i8;
        br_table v4 block3 (0.i8 block1) (1.i8 block2);
    block1:
        v5.i64 = call %inc v0;
        return v5;
    block2:
        v6.i64 = call %twice v0;
        return v6;
    block3:
        v7.i64 = call %halt v0;
        return v7;
}
func private %inc(v0.@Cursor) -> i64 {
    block0:
        v1.i64 = extract_value v0 2.i32;
        v2.i64 = add v1 1.i64;
        v3.i32 = extract_value v0 1.i32;
        v4.i32 = add v3 1.i32;
        v5.@Cursor = insert_value v0 2.i32 v2;
        v6.@Cursor = insert_value v5 1.i32 v4;
        v7.i64 = call %next v6;
        return v7;
}
func private %twice(v0.@Cursor) -> i64 {
    block0:
        v1.i64 = extract_value v0 2.i32;
        v2.i64 = add v1 v1;
        v3.i32 = extract_value v0 1.i32;
        v4.i32 = add v3 1.i32;
        v5.@Cursor = insert_value v0 2.i32 v2;
        v6.@Cursor = insert_value v5 1.i32 v4;
        v7.i64 = call %next v6;
        return v7;
}
func inline(never) private %halt(v0.@Cursor) -> i64 {
    block0:
        v1.i64 = extract_value v0 2.i32;
        return v1;
}
func public %run(v0.*i8) -> i64 {
    block0:
        v1.@Cursor = agg.make @Cursor v0 0.i32 0.i64;
        v2.i64 = call %next v1;
        return v2;
}";
    for level in [OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let bytes = build_with(source, level, WasmBackend::new().with_stack_size(4096));
        let indirect = operators(&bytes, |operator| {
            matches!(operator, Operator::ReturnCallIndirect { .. })
        });
        let tables = operators(&bytes, |operator| {
            matches!(operator, Operator::BrTable { .. })
        });
        // The inliner may copy `%next` into each handler.
        if level == OptLevel::Os {
            assert!(indirect >= 1 && tables == 0, "{level:?}");
        } else {
            assert_eq!(indirect, 0, "{level:?}");
        }
        let mut machine = Machine::new(&bytes);
        let base = machine.memory_size();
        machine.grow_memory(2);
        // 100,000 increments and doublings, and a halt.
        let mut code = vec![0u8; 100_000];
        for (index, byte) in code.iter_mut().enumerate() {
            *byte = u8::from(index % 50 == 49);
        }
        code.push(3);
        machine.write(base, &code);
        let want = (0..100_000).fold(0i64, |value: i64, index| {
            if index % 50 == 49 {
                value.wrapping_add(value)
            } else {
                value.wrapping_add(1)
            }
        });
        let run = machine.func("run");
        let got = machine.call(&run, &[Val::I32(base as i32)]);
        assert_eq!(got[0].unwrap_i64(), want, "{level:?}");
    }
}
