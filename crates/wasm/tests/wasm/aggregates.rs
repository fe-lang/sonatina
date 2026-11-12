//! Frames, aggregates, objects, constants and the arena.

use sonatina_codegen::{Backend, BackendOptions, Compile, OptLevel};
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
fn the_sym_addr_of_a_global_is_its_address() {
    // A host reads the bytes of `$data` at the address `%data` returns, and
    // `%third` reads them through a pointer made from it.
    let source = "global private const [i8; 4] $data = [11, 22, 33, 44];
func public %data() -> i32 {
    block0:
        v0.i32 = sym_addr $data;
        return v0;
}
func public %third() -> i8 {
    block0:
        v0.i32 = sym_addr $data;
        v1.i32 = add v0 2.i32;
        v2.*i8 = int_to_ptr v1 *i8;
        v3.i8 = mload v2 i8;
        return v3;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let data = machine.func("data");
        let address = machine.call(&data, &[])[0].unwrap_i32();
        assert_eq!(
            machine.read(address as usize, 4),
            [11, 22, 33, 44],
            "{level:?}"
        );
        let third = machine.func("third");
        assert_eq!(machine.call(&third, &[])[0].unwrap_i32(), 33, "{level:?}");
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

/// Whether a function body of the module has a `memory.copy`.
fn has_memory_copy(bytes: &[u8]) -> bool {
    wasmparser::Parser::new(0).parse_all(bytes).any(|payload| {
        let Ok(wasmparser::Payload::CodeSectionEntry(body)) = payload else {
            return false;
        };
        body.get_operators_reader()
            .expect("the body has operators")
            .into_iter()
            .any(|op| matches!(op, Ok(wasmparser::Operator::MemoryCopy { .. })))
    })
}

/// The number of `memory.fill`s in the function bodies of the module.
fn memory_fills(bytes: &[u8]) -> usize {
    wasmparser::Parser::new(0)
        .parse_all(bytes)
        .map(|payload| {
            let Ok(wasmparser::Payload::CodeSectionEntry(body)) = payload else {
                return 0;
            };
            body.get_operators_reader()
                .expect("the body has operators")
                .into_iter()
                .filter(|op| matches!(op, Ok(wasmparser::Operator::MemoryFill { .. })))
                .count()
        })
        .sum()
}

#[test]
fn inserts_that_write_every_byte_need_no_zero_fill() {
    // Built field by field from `undef`, `%full` writes every byte of its
    // storage, which then needs no filling first. `%partial` leaves the
    // second field undef, which reads as zero although `%full` left a value
    // in the frame both use.
    let source = "type @Pair = { i64, i64 };
func public %full(v0.i64, v1.i64, v2.*@Pair) {
    block0:
        v3.@Pair = insert_value undef.@Pair 0.i32 v0;
        v4.@Pair = insert_value v3 1.i32 v1;
        mstore v2 v4 @Pair;
        return;
}
func public %partial(v0.i64, v1.*@Pair) {
    block0:
        v2.@Pair = insert_value undef.@Pair 0.i32 v0;
        mstore v1 v2 @Pair;
        return;
}";
    let bytes = WasmBackend::new()
        .compile_module(&parse(source), &BackendOptions::default())
        .unwrap_or_else(|errors| panic!("{errors:?}"))
        .into_bytes();
    assert_eq!(memory_fills(&bytes), 1, "only `%partial` fills");
    let mut machine = Machine::new(&bytes);
    let base = machine.memory_size();
    machine.grow_memory(1);
    let words = |machine: &mut Machine| -> Vec<i64> {
        machine
            .read(base, 16)
            .chunks(8)
            .map(|chunk| i64::from_le_bytes(chunk.try_into().unwrap()))
            .collect()
    };
    let full = machine.func("full");
    machine.call(&full, &[Val::I64(7), Val::I64(9), Val::I32(base as i32)]);
    assert_eq!(words(&mut machine), [7, 9]);
    let partial = machine.func("partial");
    machine.call(&partial, &[Val::I64(5), Val::I32(base as i32)]);
    assert_eq!(words(&mut machine), [5, 0]);
}

#[test]
fn inserts_cover_an_aggregate_in_any_order_but_not_its_padding() {
    // `%reversed` writes the fields last to first and needs no fill. The
    // fields of `@Gap` leave seven bytes of padding unwritten, and `%huge`
    // writes one byte of a 1 GiB array, so both keep their fills; the check
    // takes memory for the inserts, not for the bytes of the aggregate.
    let source = "type @Pair = { i64, i64 };
type @Gap = { i8, i64 };
func public %reversed(v0.i64, v1.i64, v2.*@Pair) {
    block0:
        v3.@Pair = insert_value undef.@Pair 1.i32 v1;
        v4.@Pair = insert_value v3 0.i32 v0;
        mstore v2 v4 @Pair;
        return;
}
func public %padded(v0.i8, v1.i64, v2.*@Gap) {
    block0:
        v3.@Gap = insert_value undef.@Gap 0.i32 v0;
        v4.@Gap = insert_value v3 1.i32 v1;
        mstore v2 v4 @Gap;
        return;
}
func public %huge(v0.i8, v1.*[i8; 1073741824]) {
    block0:
        v2.[i8; 1073741824] = insert_value undef.[i8; 1073741824] 0.i32 v0;
        mstore v1 v2 [i8; 1073741824];
        return;
}";
    let bytes = WasmBackend::new()
        .compile_module(&parse(source), &BackendOptions::default())
        .unwrap_or_else(|errors| panic!("{errors:?}"))
        .into_bytes();
    assert_eq!(memory_fills(&bytes), 2, "`%padded` and `%huge` fill");
    let mut machine = Machine::new(&bytes);
    let base = machine.memory_size();
    machine.grow_memory(1);
    let reversed = machine.func("reversed");
    machine.call(
        &reversed,
        &[Val::I64(7), Val::I64(9), Val::I32(base as i32)],
    );
    let words: Vec<i64> = machine
        .read(base, 16)
        .chunks(8)
        .map(|chunk| i64::from_le_bytes(chunk.try_into().unwrap()))
        .collect();
    assert_eq!(words, [7, 9]);
}

#[test]
fn a_small_copy_is_a_memory_copy_only_at_os() {
    // Loads and stores copy a small aggregate faster, and a `memory.copy` is
    // smaller, so `Os` makes every copy one. The IR goes to the backend as
    // it is, without the pipeline, which could take the copy apart.
    let source = "type @Pair = { i64, i64 };
func public %copy(v0.*@Pair, v1.*@Pair) {
    block0:
        v2.@Pair = mload v0 @Pair;
        mstore v1 v2 @Pair;
        return;
}";
    for (opt_level, copies) in [(OptLevel::O2, false), (OptLevel::Os, true)] {
        let bytes = WasmBackend::new()
            .compile_module(&parse(source), &BackendOptions { opt_level })
            .unwrap_or_else(|errors| panic!("{opt_level:?}: {errors:?}"))
            .into_bytes();
        assert_eq!(has_memory_copy(&bytes), copies, "{opt_level:?}");
        let mut machine = Machine::new(&bytes);
        let base = machine.memory_size();
        machine.grow_memory(1);
        let pair: Vec<u8> = (1..=16).collect();
        machine.write(base, &pair);
        let copy = machine.func("copy");
        machine.call(&copy, &[Val::I32(base as i32), Val::I32(base as i32 + 16)]);
        assert_eq!(machine.read(base + 16, 16), pair, "{opt_level:?}");
    }
}

#[test]
fn an_aggregate_above_the_inline_copy_size_passes_by_value() {
    // 96 bytes: larger than the 64 that are copied with loads and stores, so
    // arguments, results and stores of it are `memory.copy`.
    let source = "type @Big = { i256, [i64; 6], i8 };
func private %make(v0.i64) -> @Big {
    block0:
        v1.i256 = zext v0 i256;
        v2.i256 = shl 200.i256 v1;
        v3.@Big = insert_value undef.@Big 0.i32 v2;
        v4.[i64; 6] = insert_value undef.[i64; 6] 0.i32 v0;
        v5.[i64; 6] = insert_value v4 5.i32 9.i64;
        v6.@Big = insert_value v3 1.i32 v5;
        v7.@Big = insert_value v6 2.i32 -1.i8;
        return v7;
}
func private %bump(v0.@Big) -> @Big {
    block0:
        v1.[i64; 6] = extract_value v0 1.i32;
        v2.i64 = extract_value v1 5.i32;
        v3.i64 = add v2 1.i64;
        v4.[i64; 6] = insert_value v1 5.i32 v3;
        v5.@Big = insert_value v0 1.i32 v4;
        return v5;
}
func public %run(v0.i64, v1.*@Big, v2.*@Big) {
    block0:
        v3.@Big = call %make v0;
        v4.@Big = call %bump v3;
        mstore v1 v3 @Big;
        mstore v2 v4 @Big;
        return;
}";
    let words = |bytes: Vec<u8>| -> Vec<u64> {
        bytes
            .chunks(8)
            .map(|chunk| u64::from_le_bytes(chunk.try_into().unwrap()))
            .collect()
    };
    for level in LEVELS {
        let bytes = build(source, level);
        assert!(has_memory_copy(&bytes), "{level:?}");
        let mut machine = Machine::new(&bytes);
        let out = machine.memory_size();
        machine.grow_memory(1);
        let run = machine.func("run");
        machine.call(
            &run,
            &[Val::I64(5), Val::I32(out as i32), Val::I32(out as i32 + 96)],
        );
        // The callee changed its copy of the argument, not the caller's value.
        for (base, last) in [(out, 9), (out + 96, 10)] {
            let fields = words(machine.read(base, 80));
            assert_eq!(fields[..4], [0, 0, 0, 5 << 8], "{level:?}");
            assert_eq!(fields[4..], [5, 0, 0, 0, 0, last], "{level:?}");
            assert_eq!(machine.read(base + 80, 1), [0xff], "{level:?}");
        }
    }
}

#[test]
fn an_insert_into_an_extracted_view_leaves_the_parent_unchanged() {
    let source = "type @Pair = { i64, i64 };
type @Outer = { @Pair, i64 };
func public %snapshots(v0.i64, v1.i64, v2.*[i64; 6]) {
    block0:
        v3.@Pair = insert_value undef.@Pair 0.i32 v0;
        v4.@Pair = insert_value v3 1.i32 v1;
        v5.@Outer = insert_value undef.@Outer 0.i32 v4;
        v6.@Outer = insert_value v5 1.i32 7.i64;
        v7.@Pair = extract_value v6 0.i32;
        v8.@Pair = insert_value v7 0.i32 91.i64;
        v9.@Outer = insert_value v6 0.i32 v8;
        v10.@Outer = insert_value v9 1.i32 93.i64;
        v11.@Pair = extract_value v6 0.i32;
        v12.i64 = extract_value v11 0.i32;
        v13.i64 = extract_value v11 1.i32;
        v14.@Pair = extract_value v10 0.i32;
        v15.i64 = extract_value v14 0.i32;
        v16.i64 = extract_value v14 1.i32;
        v17.i64 = extract_value v6 1.i32;
        v18.i64 = extract_value v10 1.i32;
        v19.[i64; 6] = insert_value undef.[i64; 6] 0.i32 v12;
        v20.[i64; 6] = insert_value v19 1.i32 v13;
        v21.[i64; 6] = insert_value v20 2.i32 v15;
        v22.[i64; 6] = insert_value v21 3.i32 v16;
        v23.[i64; 6] = insert_value v22 4.i32 v17;
        v24.[i64; 6] = insert_value v23 5.i32 v18;
        mstore v2 v24 [i64; 6];
        return;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let out = machine.memory_size();
        machine.grow_memory(1);
        let snapshots = machine.func("snapshots");
        machine.call(
            &snapshots,
            &[Val::I64(11), Val::I64(22), Val::I32(out as i32)],
        );
        let words: Vec<i64> = machine
            .read(out, 48)
            .chunks(8)
            .map(|chunk| i64::from_le_bytes(chunk.try_into().unwrap()))
            .collect();
        assert_eq!(words, [11, 22, 91, 22, 7, 93], "{level:?}");
    }
}

#[test]
fn global_addresses_merge_in_phis_and_constant_fields_load() {
    let source = "type @Record = { i8, i128, [i16; 3], i256 };
global private i64 $counter = 41;
global private i64 $zero = 0;
global private const @Record $data = {1, 2, [3, 4, 5], 6};
func public %bump(v0.i64) -> i64 {
    block0:
        v1.i64 = mload $counter i64;
        v2.i64 = add v1 v0;
        mstore $counter v2 i64;
        return v2;
}
func public %read(v0.i8) -> i64 {
    block0:
        v1.i1 = is_zero v0;
        br v1 block1 block2;
    block1:
        jump block3;
    block2:
        jump block3;
    block3:
        v2.*i64 = phi ($counter block1) ($zero block2);
        v3.i64 = mload v2 i64;
        return v3;
}
func public %field() -> i64 {
    block0:
        v0.constref<@Record> = const.ref $data;
        v1.constref<[i16; 3]> = const.proj v0 2.i32;
        v2.constref<i16> = const.index v1 2.i32;
        v3.i16 = const.load v2;
        v4.constref<i256> = const.proj v0 3.i32;
        v5.i256 = const.load v4;
        v6.i64 = zext v3 i64;
        v7.i64 = trunc v5 i64;
        v8.i64 = mul v6 v7;
        return v8;
}";
    for level in LEVELS {
        let mut machine = Machine::new(&build(source, level));
        let bump = machine.func("bump");
        // The counter keeps its value across calls.
        for (arg, want) in [(1, 42), (2, 44)] {
            assert_eq!(
                machine.call(&bump, &[Val::I64(arg)])[0].unwrap_i64(),
                want,
                "{level:?} bump({arg})"
            );
        }
        let read = machine.func("read");
        for (arg, want) in [(0, 44), (1, 0)] {
            assert_eq!(
                machine.call(&read, &[Val::I32(arg)])[0].unwrap_i64(),
                want,
                "{level:?} read({arg})"
            );
        }
        let field = machine.func("field");
        assert_eq!(machine.call(&field, &[])[0].unwrap_i64(), 30, "{level:?}");
    }
}
