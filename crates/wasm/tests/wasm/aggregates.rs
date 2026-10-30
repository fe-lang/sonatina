//! Frames, aggregates, objects, constants and the arena.

use sonatina_codegen::{Compile, OptLevel};
use sonatina_wasm::WasmBackend;
use wasmtime::Val;

use super::harness::{Machine, parse};

/// Compile at `level` (through the optimizer, as Fe does), validate, and check
/// that compiling again gives the same bytes.
pub fn build_at(source: &str, level: OptLevel) -> Vec<u8> {
    build(source, level)
}

fn build(source: &str, level: OptLevel) -> Vec<u8> {
    let first = compile_at(source, level);
    wasmparser::Validator::new()
        .validate_all(&first)
        .unwrap_or_else(|error| panic!("emitted module is invalid: {error}\n{source}"));
    assert_eq!(
        first,
        compile_at(source, level),
        "compilation is not deterministic"
    );
    first
}

fn compile_at(source: &str, level: OptLevel) -> Vec<u8> {
    Compile::new(parse(source), WasmBackend::new())
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("wasm compilation failed: {errors:?}\n{source}"))
        .into_bytes()
}

const LEVELS: [OptLevel; 3] = [OptLevel::O0, OptLevel::O2, OptLevel::Os];

#[test]
fn alloca_gep_and_scalar_memory() {
    let source = "func public %squares(v0.i32) -> i32 {
    block0:
        v1.*[i32; 8] = alloca [i32; 8];
        jump block1;
    block1:
        v2.i32 = phi (0.i32 block0) (v7 block2);
        v3.i1 = lt v2 8.i32;
        br v3 block2 block3;
    block2:
        v4.*i32 = gep v1 0.i32 v2;
        v5.i32 = mul v2 v2;
        v6.i32 = add v5 v0;
        mstore v4 v6 i32;
        v7.i32 = add v2 1.i32;
        jump block1;
    block3:
        v8.*i32 = gep v1 0.i32 5.i32;
        v9.i32 = mload v8 i32;
        v10.*i32 = gep v1 0.i32 7.i32;
        v11.i32 = mload v10 i32;
        v12.i32 = add v9 v11;
        return v12;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let squares = machine.func("squares");
        for base in [0, 1, 100] {
            let got = machine.call(&squares, &[Val::I32(base)])[0].unwrap_i32();
            assert_eq!(got, 25 + 49 + 2 * base, "{level:?}");
        }
    }
}

#[test]
fn objects_are_updated_in_place_and_loads_are_snapshots() {
    let source = "type @Pair = { i32, i32 };
func public %f(v0.i32, v1.i32) -> i32 {
    block0:
        v2.objref<@Pair> = obj.alloc @Pair;
        v3.objref<i32> = obj.proj v2 0.i32;
        obj.store v3 v0;
        v4.objref<i32> = obj.proj v2 1.i32;
        obj.store v4 v1;
        v5.@Pair = obj.load v2;
        obj.store v3 99.i32;
        v6.i32 = extract_value v5 0.i32;
        v7.i32 = obj.load v3;
        v8.i32 = extract_value v5 1.i32;
        v9.i32 = mul v6 1000.i32;
        v10.i32 = add v9 v7;
        v11.i32 = mul v8 1000000.i32;
        v12.i32 = add v10 v11;
        return v12;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let f = machine.func("f");
        assert_eq!(
            machine.call(&f, &[Val::I32(7), Val::I32(3)])[0].unwrap_i32(),
            7_000 + 99 + 3_000_000,
            "{level:?}"
        );
    }
}

#[test]
fn aggregates_pass_to_calls_and_return_through_a_buffer() {
    let source = "type @Pair = { i32, i64 };
type @Line = { @Pair, @Pair };
func private %make(v0.i32, v1.i64) -> @Pair {
    block0:
        v2.@Pair = insert_value undef.@Pair 0.i32 v0;
        v3.@Pair = insert_value v2 1.i32 v1;
        return v3;
}
func private %swap(v0.@Pair) -> @Pair {
    block0:
        v1.i32 = extract_value v0 0.i32;
        v2.i64 = extract_value v0 1.i32;
        v3.i32 = trunc v2 i32;
        v4.i64 = zext v1 i64;
        v5.@Pair = call %make v3 v4;
        return v5;
}
func public %f(v0.i32, v1.i64) -> i64 {
    block0:
        v2.@Pair = call %make v0 v1;
        v3.@Pair = call %swap v2;
        v4.@Line = insert_value undef.@Line 0.i32 v2;
        v5.@Line = insert_value v4 1.i32 v3;
        v6.@Pair = extract_value v5 1.i32;
        v7.i32 = extract_value v6 0.i32;
        v8.i64 = extract_value v6 1.i32;
        v9.i64 = zext v7 i64;
        v10.i64 = mul v9 1000000.i64;
        v11.i64 = add v10 v8;
        return v11;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let f = machine.func("f");
        let got = machine.call(&f, &[Val::I32(12), Val::I64(34)])[0].unwrap_i64();
        assert_eq!(got, 34_000_000 + 12, "{level:?}");
    }
}

#[test]
fn constants_are_read_from_data_segments() {
    let source = "type @Row = { i8, i32 };
global private const [i32; 4] $primes = [2, 3, 5, 7];
global private const [@Row; 2] $rows = [{1, 100}, {2, 200}];
func public %prime(v0.i32) -> i32 {
    block0:
        v1.constref<[i32; 4]> = const.ref $primes;
        v2.i1 = lt v0 4.i32;
        br v2 block1 block2;
    block1:
        v3.constref<i32> = const.index v1 v0;
        v4.i32 = const.load v3;
        return v4;
    block2:
        unreachable;
}
func public %row(v0.i32) -> i32 {
    block0:
        v1.constref<[@Row; 2]> = const.ref $rows;
        v2.constref<@Row> = const.index v1 v0;
        v3.constref<i32> = const.proj v2 1.i32;
        v4.i32 = const.load v3;
        v5.constref<i8> = const.proj v2 0.i32;
        v6.i8 = const.load v5;
        v7.i32 = zext v6 i32;
        v8.i32 = add v4 v7;
        return v8;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let prime = machine.func("prime");
        for (i, want) in [2, 3, 5, 7].into_iter().enumerate() {
            assert_eq!(
                machine.call(&prime, &[Val::I32(i as i32)])[0].unwrap_i32(),
                want
            );
        }
        assert!(machine.try_call(&prime, &[Val::I32(4)]).is_err());
        let row = machine.func("row");
        assert_eq!(machine.call(&row, &[Val::I32(0)])[0].unwrap_i32(), 101);
        assert_eq!(machine.call(&row, &[Val::I32(1)])[0].unwrap_i32(), 202);
    }
}

#[test]
fn a_constref_result_outlives_later_calls() {
    // The first result stays live through a phi while the loop calls again.
    let source = "global private const i32 $one = 1;
global private const i32 $two = 2;
func private %pick(v0.i32) -> constref<i32> {
    block0:
        v1.i1 = eq v0 0.i32;
        br v1 block1 block2;
    block1:
        v2.constref<i32> = const.ref $one;
        return v2;
    block2:
        v3.constref<i32> = const.ref $two;
        return v3;
}
func public %first() -> i32 {
    block0:
        v0.constref<i32> = const.ref $two;
        jump block1;
    block1:
        v1.i32 = phi (0.i32 block0) (v4 block3);
        v2.constref<i32> = phi (v0 block0) (v6 block3);
        v3.constref<i32> = call %pick v1;
        v4.i32 = add v1 1.i32;
        v5.i1 = eq v1 0.i32;
        br v5 block2 block3;
    block2:
        jump block3;
    block3:
        v6.constref<i32> = phi (v3 block2) (v2 block1);
        v7.i1 = lt v4 2.i32;
        br v7 block1 block4;
    block4:
        v8.i32 = const.load v6;
        return v8;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let first = machine.func("first");
        assert_eq!(machine.call(&first, &[])[0].unwrap_i32(), 1, "{level:?}");
    }
}

#[test]
fn counters_and_indices_of_256_bits_work() {
    let source = "func public %sum(v0.i32) -> i32 {
    block0:
        v1.objref<[i32; 5]> = obj.alloc [i32; 5];
        jump block1;
    block1:
        v2.i256 = phi (0.i256 block0) (v8 block2);
        v3.i1 = lt v2 5.i256;
        br v3 block2 block3;
    block2:
        v4.i32 = trunc v2 i32;
        v5.i32 = mul v4 v0;
        v6.objref<i32> = obj.index v1 v2;
        obj.store v6 v5;
        v8.i256 = add v2 1.i256;
        jump block1;
    block3:
        v9.i32 = phi (0.i32 block1) (v15 block4);
        v10.i256 = phi (0.i256 block1) (v16 block4);
        v11.i1 = lt v10 5.i256;
        br v11 block4 block5;
    block4:
        v12.objref<i32> = obj.index v1 v10;
        v13.i32 = obj.load v12;
        v15.i32 = add v9 v13;
        (v16.i256, v17.i1) = uaddo v10 1.i256;
        jump block3;
    block5:
        return v9;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let sum = machine.func("sum");
        for n in [0, 1, 7] {
            assert_eq!(
                machine.call(&sum, &[Val::I32(n)])[0].unwrap_i32(),
                10 * n,
                "{level:?}"
            );
        }
    }
}

#[test]
fn a_loop_consumer_of_a_preheader_aggregate_does_not_change_it() {
    // `v4` is built before the loop and has one consumer, which runs on every
    // iteration. Its element 1 must be 7 each time.
    let source = "type @P = { i32, i32 };
func public %f(v0.i32, v1.i32) -> i32 {
    block0:
        v2.@P = insert_value undef.@P 0.i32 v0;
        v3.@P = insert_value v2 1.i32 7.i32;
        jump block1;
    block1:
        v4.i32 = phi (0.i32 block0) (v10 block1);
        v5.i32 = phi (0.i32 block0) (v11 block1);
        v6.i32 = add v0 v4;
        v7.@P = insert_value v3 0.i32 v6;
        v8.i32 = extract_value v7 1.i32;
        v9.i32 = extract_value v7 0.i32;
        v12.i32 = add v5 v8;
        v11.i32 = add v12 v9;
        v10.i32 = add v4 1.i32;
        v13.i1 = lt v10 v1;
        br v13 block1 block2;
    block2:
        return v11;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let f = machine.func("f");
        for (start, count) in [(5, 1), (5, 4), (-3, 6)] {
            let want: i32 = (0..count).map(|i| 7 + start + i).sum();
            let got = machine.call(&f, &[Val::I32(start), Val::I32(count)])[0].unwrap_i32();
            assert_eq!(got, want, "{level:?} {start} {count}");
        }
    }
}

#[test]
fn mixed_parameters_and_results_cross_calls() {
    // 256-bit values, aggregates and scalars as parameters, with 256-bit results
    // (four values) and a recursive call.
    let source = "type @P = { i64, i32 };
func private %mix(v0.i256, v1.@P, v2.i64, v3.i32) -> i256 {
    block0:
        v4.i1 = is_zero v3;
        br v4 block1 block2;
    block1:
        v5.i64 = extract_value v1 0.i32;
        v6.i64 = add v5 v2;
        v7.i256 = zext v6 i256;
        v8.i256 = add v0 v7;
        return v8;
    block2:
        v9.i32 = sub v3 1.i32;
        v10.i256 = shl 1.i256 v0;
        v11.i256 = call %mix v10 v1 v2 v9;
        return v11;
}
func public %f(v0.i64, v1.i32) -> i64 {
    block0:
        v2.@P = insert_value undef.@P 0.i32 v0;
        v3.@P = insert_value v2 1.i32 v1;
        v4.i256 = zext v0 i256;
        v5.i256 = call %mix v4 v3 5.i64 v1;
        v6.i256 = shr 64.i256 v5;
        v7.i64 = trunc v6 i64;
        v8.i64 = trunc v5 i64;
        v9.i64 = add v7 v8;
        return v9;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let f = machine.func("f");
        for (seed, depth) in [(3i64, 0i32), (3, 1), (3, 4), (1, 40)] {
            // mix doubles its first argument `depth` times, then adds seed + 5.
            let value = (u128::from(seed as u64) << depth) + (seed as u128 + 5);
            let want = ((value >> 64) as u64).wrapping_add(value as u64) as i64;
            let got = machine.call(&f, &[Val::I64(seed), Val::I32(depth)])[0].unwrap_i64();
            assert_eq!(got, want, "{level:?} {seed} {depth}");
        }
    }
}

#[test]
fn a_256_bit_phi_swaps_in_parallel() {
    let source = "func public %f(v0.i64, v1.i64, v2.i32) -> i64 {
    block0:
        v3.i256 = zext v0 i256;
        v4.i256 = zext v1 i256;
        jump block1;
    block1:
        v5.i256 = phi (v3 block0) (v6 block2);
        v6.i256 = phi (v4 block0) (v5 block2);
        v7.i32 = phi (0.i32 block0) (v8 block2);
        v9.i1 = lt v7 v2;
        br v9 block2 block3;
    block2:
        v8.i32 = add v7 1.i32;
        jump block1;
    block3:
        v10.i256 = shl 64.i256 v5;
        v11.i256 = add v10 v6;
        v12.i64 = trunc v11 i64;
        v13.i256 = shr 64.i256 v11;
        v14.i64 = trunc v13 i64;
        v15.i64 = mul v14 1000.i64;
        v16.i64 = add v15 v12;
        return v16;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let f = machine.func("f");
        for n in 0..4 {
            let (a, b) = if n % 2 == 0 { (3, 4) } else { (4, 3) };
            let got = machine.call(&f, &[Val::I64(3), Val::I64(4), Val::I32(n)])[0].unwrap_i64();
            assert_eq!(got, a * 1000 + b, "{level:?} after {n} swaps");
        }
    }
}

#[test]
fn exports_keep_their_signatures_when_the_module_has_a_runtime() {
    // An export is a wrapper around a function with a hidden parameter. It
    // canonicalizes narrow parameters, passes several results through, and a
    // trap in the function reaches the host.
    let source = "func public %f(v0.i8, v1.i64, v2.i1) -> (i64, i8, i32, i32) {
    block0:
        v3.*[i8; 4] = alloca [i8; 4];
        v4.*i8 = gep v3 0.i32 3.i32;
        mstore v4 v0 i8;
        v5.i8 = mload v4 i8;
        v6.i8 = add v5 1.i8;
        v7.i32 = zext v2 i32;
        v8.i64 = add v1 1.i64;
        v9.i32 = zext v0 i32;
        return (v8, v6, v7, v9);
}
func public %g(v0.i32) -> i32 {
    block0:
        v1.*i32 = alloca i32;
        mstore v1 v0 i32;
        v2.i1 = is_zero v0;
        br v2 block1 block2;
    block1:
        unreachable;
    block2:
        v3.i32 = mload v1 i32;
        return v3;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let f = machine.func("f");
        // The i8 and i1 parameters arrive with garbage above their widths.
        let out = machine.call(&f, &[Val::I32(0x1234_56ff), Val::I64(9), Val::I32(3)]);
        assert_eq!(out[0].unwrap_i64(), 10, "{level:?}");
        assert_eq!(out[1].unwrap_i32(), 0, "{level:?}: 0xff + 1 wraps to 0");
        assert_eq!(out[2].unwrap_i32(), 1, "{level:?}: the i1 is its low bit");
        assert_eq!(
            out[3].unwrap_i32(),
            0xff,
            "{level:?}: the i8 is its low byte"
        );
        let g = machine.func("g");
        assert!(machine.try_call(&g, &[Val::I32(0)]).is_err());
        assert_eq!(machine.call(&g, &[Val::I32(77)])[0].unwrap_i32(), 77);
    }
}

#[test]
fn a_function_without_parameters_can_count_in_256_bits() {
    let source = "func public %f() -> i32 {
    block0:
        jump block1;
    block1:
        v0.i256 = phi (0.i256 block0) (v2 block1);
        v1.i32 = phi (0.i32 block0) (v3 block1);
        v2.i256 = add v0 3.i256;
        v3.i32 = add v1 2.i32;
        v4.i1 = lt v2 30.i256;
        br v4 block1 block2;
    block2:
        return v3;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let f = machine.func("f");
        assert_eq!(machine.call(&f, &[])[0].unwrap_i32(), 20, "{level:?}");
    }
}

/// A loop carries a two-field struct and updates one field. The other field
/// reaches the back edge unchanged, so its scalar phi is its own user. The
/// optimizer panicked on it at -O1 and above.
#[test]
fn a_loop_can_carry_a_struct_and_update_one_field() {
    let source = "type @P = { i32, i32 };
func public %f(v0.i32) -> i32 {
    block0:
        v1.@P = insert_value undef.@P 0.i32 v0;
        v2.@P = insert_value v1 1.i32 v0;
        jump block1;
    block1:
        v3.i32 = phi (0.i32 block0) (v7 block2);
        v4.@P = phi (v2 block0) (v6 block2);
        v11.i1 = lt v3 v0;
        br v11 block2 block3;
    block2:
        v8.i32 = extract_value v4 0.i32;
        v9.i32 = add v8 v3;
        v6.@P = insert_value v4 0.i32 v9;
        v7.i32 = add v3 1.i32;
        jump block1;
    block3:
        v13.i32 = extract_value v4 0.i32;
        v14.i32 = extract_value v4 1.i32;
        v15.i32 = mul v13 1000.i32;
        v16.i32 = add v15 v14;
        return v16;
}
";
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::Os] {
        let mut machine = Machine::new(&build_at(source, level));
        let f = machine.func("f");
        for n in [0, 1, 2, 5, 10] {
            let sum = n + n * (n - 1) / 2;
            assert_eq!(
                machine.call(&f, &[Val::I32(n)])[0].unwrap_i32(),
                sum * 1000 + n,
                "{level:?}: f({n})"
            );
        }
    }
}
