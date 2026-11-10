//! Tests for the WebAssembly backend.
//!
//! Every module is encoded by the backend, validated with `wasmparser` and
//! executed with `wasmtime`. Arithmetic results are compared with the
//! reference semantics of `sonatina_ir::Immediate`, which the IR interpreter
//! uses.

// Shared with the native backends' tests, which keep the data.
#[path = "../../codegen/tests/alias_execution/mod.rs"]
mod alias_execution;

#[path = "wasm/aggregates.rs"]
mod aggregates;
#[path = "wasm/control_flow.rs"]
mod control_flow;
#[path = "wasm/diagnostics.rs"]
mod diagnostics;
#[path = "wasm/enums.rs"]
mod enums;
#[path = "wasm/harness.rs"]
mod harness;
#[path = "wasm/heap.rs"]
mod heap;
#[path = "wasm/int128.rs"]
mod int128;
#[path = "wasm/memory_and_calls.rs"]
mod memory_and_calls;
#[path = "wasm/memory_runtime.rs"]
mod memory_runtime;
#[path = "wasm/operands.rs"]
mod operands;
#[path = "wasm/shared_oracles.rs"]
mod shared_oracles;
#[path = "wasm/tail_calls.rs"]
mod tail_calls;
#[path = "wasm/wide.rs"]
mod wide;

use harness::{Machine, compile_valid, parse};
use sonatina_ir::Immediate;
use wasmtime::Val;

/// Deterministic pseudo-random numbers, so failures are reproducible.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 ^ (self.0 >> 29)
    }
}

fn mask(width: u32) -> u64 {
    if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn ir_type(width: u32) -> &'static str {
    match width {
        1 => "i1",
        8 => "i8",
        16 => "i16",
        32 => "i32",
        64 => "i64",
        _ => unreachable!(),
    }
}

/// The IR immediate of `width` bits holding the low bits of `bits`.
fn imm(width: u32, bits: u64) -> Immediate {
    match width {
        1 => Immediate::I1(bits & 1 != 0),
        8 => Immediate::I8(bits as i8),
        16 => Immediate::I16(bits as i16),
        32 => Immediate::I32(bits as i32),
        64 => Immediate::I64(bits as i64),
        _ => unreachable!(),
    }
}

/// The value of an immediate as an unsigned integer of its width.
fn bits_of(width: u32, value: Immediate) -> u64 {
    value.as_i256().to_u256().low_u64() & mask(width)
}

fn val(width: u32, bits: u64) -> Val {
    if width == 64 {
        Val::I64(bits as i64)
    } else {
        Val::I32((bits & mask(width)) as u32 as i32)
    }
}

fn bits_from(width: u32, val: &Val) -> u64 {
    match val {
        Val::I32(v) => u64::from(*v as u32),
        Val::I64(v) => *v as u64,
        other => panic!("unexpected result {other:?} for width {width}"),
    }
}

/// Boundary values of a width, then pseudo-random values.
fn operands(width: u32) -> Vec<u64> {
    let top = mask(width);
    let sign = 1u64 << (width - 1);
    let mut values = vec![
        0,
        1,
        2,
        3,
        top,
        top.wrapping_sub(1),
        sign,
        sign.wrapping_sub(1),
        sign + 1,
        sign.wrapping_sub(2),
        top / 3,
        top / 3 * 2,
        0x55,
        0xaa,
        0xff,
        0x100,
        0x7fff,
        0x8000,
        0xffff,
        0x1_0000,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        0x1_0000_0000,
        0x1_0000_0001,
        0x1_ffff_ffff,
        0xffff_ffff_0000_0000,
        0xffff_ffff_ffff_fffe,
        0xdead_beef,
    ];
    values.retain(|v| *v <= top);
    values.sort_unstable();
    values.dedup();
    values
}

fn pairs(width: u32, random: usize) -> Vec<(u64, u64)> {
    let mut pairs = Vec::new();
    if width <= 8 {
        for a in 0..=mask(width) {
            for b in 0..=mask(width) {
                pairs.push((a, b));
            }
        }
        return pairs;
    }
    let edges = operands(width);
    for &a in &edges {
        for &b in &edges {
            pairs.push((a, b));
        }
    }
    let mut rng = Lcg(0x5eed ^ u64::from(width));
    for _ in 0..random {
        pairs.push((rng.next() & mask(width), rng.next() & mask(width)));
    }
    pairs
}

fn binary_function(name: &str, ty: &str, result_ty: &str) -> String {
    format!(
        "func public %{name}(v0.{ty}, v1.{ty}) -> {result_ty} {{
    block0:
        v2.{result_ty} = {name} v0 v1;
        return v2;
}}
"
    )
}

/// `%name(a, b)` returns the wrapped result and the overflow flag.
fn overflow_function(name: &str, ty: &str) -> String {
    format!(
        "func public %{name}(v0.{ty}, v1.{ty}) -> ({ty}, i1) {{
    block0:
        (v2.{ty}, v3.i1) = {name} v0 v1;
        return (v2, v3);
}}
"
    )
}

type Reference = fn(Immediate, Immediate) -> Immediate;
type OverflowReference = fn(Immediate, Immediate) -> (Immediate, bool);

const WRAPPING: [(&str, Reference); 3] = [
    ("add", |a, b| a + b),
    ("sub", |a, b| a - b),
    ("mul", |a, b| a * b),
];

const SATURATING: [(&str, Reference); 6] = [
    ("uaddsat", Immediate::saturating_uadd),
    ("saddsat", Immediate::saturating_sadd),
    ("usubsat", Immediate::saturating_usub),
    ("ssubsat", Immediate::saturating_ssub),
    ("umulsat", Immediate::saturating_umul),
    ("smulsat", Immediate::saturating_smul),
];

const CHECKED: [(&str, OverflowReference); 6] = [
    ("uaddo", Immediate::overflowing_uadd),
    ("saddo", Immediate::overflowing_sadd),
    ("usubo", Immediate::overflowing_usub),
    ("ssubo", Immediate::overflowing_ssub),
    ("umulo", Immediate::overflowing_umul),
    ("smulo", Immediate::overflowing_smul),
];

fn arithmetic_module(width: u32) -> String {
    let ty = ir_type(width);
    let mut source = String::new();
    for (name, _) in WRAPPING.iter().chain(SATURATING.iter()) {
        source += &binary_function(name, ty, ty);
    }
    for (name, _) in CHECKED {
        source += &overflow_function(name, ty);
    }
    source += &format!(
        "func public %snego(v0.{ty}) -> ({ty}, i1) {{
    block0:
        (v1.{ty}, v2.i1) = snego v0;
        return (v1, v2);
}}
func public %neg(v0.{ty}) -> {ty} {{
    block0:
        v1.{ty} = neg v0;
        return v1;
}}
"
    );
    source
}

/// Run the checked, saturating and wrapping arithmetic of one width against
/// the reference semantics. Returns the number of results compared.
fn check_arithmetic(width: u32, random: usize) -> usize {
    let bytes = compile_valid(&parse(&arithmetic_module(width)));
    let mut machine = Machine::new(&bytes);
    let mut compared = 0;
    let pairs = pairs(width, random);

    for (name, reference) in WRAPPING.iter().chain(SATURATING.iter()) {
        let func = machine.func(name);
        for &(a, b) in &pairs {
            let results = machine.call(&func, &[val(width, a), val(width, b)]);
            let expected = bits_of(width, reference(imm(width, a), imm(width, b)));
            assert_eq!(
                bits_from(width, &results[0]),
                expected,
                "{name} i{width}: {a:#x}, {b:#x}"
            );
            compared += 1;
        }
    }
    for (name, reference) in CHECKED {
        let func = machine.func(name);
        for &(a, b) in &pairs {
            let results = machine.call(&func, &[val(width, a), val(width, b)]);
            let (value, overflow) = reference(imm(width, a), imm(width, b));
            assert_eq!(
                (bits_from(width, &results[0]), bits_from(1, &results[1])),
                (bits_of(width, value), u64::from(overflow)),
                "{name} i{width}: {a:#x}, {b:#x}"
            );
            compared += 2;
        }
    }
    let snego = machine.func("snego");
    let neg = machine.func("neg");
    for &a in pairs
        .iter()
        .map(|(a, _)| a)
        .collect::<std::collections::BTreeSet<_>>()
    {
        let results = machine.call(&snego, &[val(width, a)]);
        let (value, overflow) = imm(width, a).overflowing_sneg();
        assert_eq!(
            (bits_from(width, &results[0]), bits_from(1, &results[1])),
            (bits_of(width, value), u64::from(overflow)),
            "snego i{width}: {a:#x}"
        );
        let results = machine.call(&neg, &[val(width, a)]);
        assert_eq!(
            bits_from(width, &results[0]),
            bits_of(width, -imm(width, a)),
            "neg i{width}: {a:#x}"
        );
        compared += 3;
    }
    compared
}

#[test]
fn checked_arithmetic_matrix() {
    let mut total = 0;
    for width in [8, 16, 32, 64] {
        let compared = check_arithmetic(width, 3000);
        eprintln!("i{width}: {compared} arithmetic results compared");
        total += compared;
    }
    eprintln!("checked arithmetic matrix: {total} results compared");
}

#[test]
fn single_bit_arithmetic_matches_the_reference_for_unsigned_forms() {
    // Signed i1 is not compared: the interpreter reads `i1 1` as +1 while the
    // native backend reads it as -1. The wasm backend follows the native one.
    let source = "func public %uaddo(v0.i1, v1.i1) -> (i1, i1) {
    block0:
        (v2.i1, v3.i1) = uaddo v0 v1;
        return (v2, v3);
}
func public %usubo(v0.i1, v1.i1) -> (i1, i1) {
    block0:
        (v2.i1, v3.i1) = usubo v0 v1;
        return (v2, v3);
}
func public %umulo(v0.i1, v1.i1) -> (i1, i1) {
    block0:
        (v2.i1, v3.i1) = umulo v0 v1;
        return (v2, v3);
}
";
    let mut machine = Machine::new(&compile_valid(&parse(source)));
    for (name, reference) in [
        ("uaddo", Immediate::overflowing_uadd as OverflowReference),
        ("usubo", Immediate::overflowing_usub),
        ("umulo", Immediate::overflowing_umul),
    ] {
        let func = machine.func(name);
        for a in 0..2 {
            for b in 0..2 {
                let results = machine.call(&func, &[val(1, a), val(1, b)]);
                let (value, overflow) = reference(imm(1, a), imm(1, b));
                assert_eq!(
                    (bits_from(1, &results[0]), bits_from(1, &results[1])),
                    (bits_of(1, value), u64::from(overflow)),
                    "{name} i1: {a}, {b}"
                );
            }
        }
    }
}

#[test]
fn checked_arithmetic_traps_are_absent() {
    // Overflow is reported through the flag. The extremes never trap, even
    // for the products that would trap a native signed multiply or divide.
    let bytes = compile_valid(&parse(&arithmetic_module(64)));
    let mut machine = Machine::new(&bytes);
    for name in ["smulo", "umulo", "saddo", "ssubo"] {
        let func = machine.func(name);
        for (a, b) in [
            (i64::MIN as u64, u64::MAX),
            (u64::MAX, i64::MIN as u64),
            (i64::MIN as u64, i64::MIN as u64),
            (0, i64::MIN as u64),
        ] {
            machine.call(&func, &[val(64, a), val(64, b)]);
        }
    }
}

const BITWISE: [(&str, Reference); 3] = [
    ("and", |a, b| a & b),
    ("or", |a, b| a | b),
    ("xor", |a, b| a ^ b),
];

const SHIFTS: [(&str, Reference); 3] = [
    ("shl", |value, count| value << count),
    ("shr", |value, count| value >> count),
    ("sar", |value, count| value.ashr(count)),
];

const DIVISIONS: [(&str, Reference); 4] = [
    ("udiv", Immediate::udiv),
    ("sdiv", Immediate::sdiv),
    ("umod", Immediate::urem),
    ("smod", Immediate::srem),
];

const COMPARISONS: [(&str, Reference); 10] = [
    ("eq", Immediate::imm_eq),
    ("ne", Immediate::imm_ne),
    ("lt", Immediate::lt),
    ("gt", Immediate::gt),
    ("le", Immediate::le),
    ("ge", Immediate::ge),
    ("slt", Immediate::slt),
    ("sgt", Immediate::sgt),
    ("sle", Immediate::sle),
    ("sge", Immediate::sge),
];

/// A shift lists the count first in the text form.
fn shift_function(name: &str, ty: &str) -> String {
    format!(
        "func public %{name}(v0.{ty}, v1.{ty}) -> {ty} {{
    block0:
        v2.{ty} = {name} v1 v0;
        return v2;
}}
"
    )
}

#[test]
fn bitwise_shift_division_and_comparison_match_the_reference() {
    let mut total = 0;
    for width in [8, 16, 32, 64] {
        let ty = ir_type(width);
        let mut source = String::new();
        for (name, _) in BITWISE {
            source += &binary_function(name, ty, ty);
        }
        for (name, _) in SHIFTS {
            source += &shift_function(name, ty);
        }
        for (name, _) in DIVISIONS {
            source += &binary_function(name, ty, ty);
        }
        for (name, _) in COMPARISONS {
            source += &binary_function(name, ty, "i1");
        }
        source += &format!(
            "func public %not(v0.{ty}) -> {ty} {{
    block0:
        v1.{ty} = not v0;
        return v1;
}}
func public %is_zero(v0.{ty}) -> i1 {{
    block0:
        v1.i1 = is_zero v0;
        return v1;
}}
"
        );
        let mut machine = Machine::new(&compile_valid(&parse(&source)));
        // Shift counts around the width, plus the general operands.
        let mut shift_pairs = pairs(width, 500);
        for value in operands(width).into_iter().take(8) {
            for count in 0..=(u64::from(width) + 2).min(mask(width)) {
                shift_pairs.push((value, count));
            }
            shift_pairs.push((value, mask(width)));
            shift_pairs.push((value, mask(width) / 2 + 1));
        }
        let general = pairs(width, 1500);

        for (name, reference) in BITWISE.iter().chain(COMPARISONS.iter()) {
            let func = machine.func(name);
            let result_width = if COMPARISONS.iter().any(|(n, _)| n == name) {
                1
            } else {
                width
            };
            for &(a, b) in &general {
                let results = machine.call(&func, &[val(width, a), val(width, b)]);
                let expected = bits_of(result_width, reference(imm(width, a), imm(width, b)));
                assert_eq!(
                    bits_from(width, &results[0]),
                    expected,
                    "{name} i{width}: {a:#x}, {b:#x}"
                );
                total += 1;
            }
        }
        for (name, reference) in SHIFTS {
            let func = machine.func(name);
            for &(a, b) in &shift_pairs {
                let results = machine.call(&func, &[val(width, a), val(width, b)]);
                let expected = bits_of(width, reference(imm(width, a), imm(width, b)));
                assert_eq!(
                    bits_from(width, &results[0]),
                    expected,
                    "{name} i{width}: {a:#x} by {b:#x}"
                );
                total += 1;
            }
        }
        for (name, reference) in DIVISIONS {
            let func = machine.func(name);
            for &(a, b) in general.iter().filter(|(_, b)| *b != 0) {
                let results = machine.call(&func, &[val(width, a), val(width, b)]);
                let expected = bits_of(width, reference(imm(width, a), imm(width, b)));
                assert_eq!(
                    bits_from(width, &results[0]),
                    expected,
                    "{name} i{width}: {a:#x}, {b:#x}"
                );
                total += 1;
            }
        }
        let not = machine.func("not");
        let is_zero = machine.func("is_zero");
        for (a, _) in &general {
            let results = machine.call(&not, &[val(width, *a)]);
            assert_eq!(
                bits_from(width, &results[0]),
                bits_of(width, !imm(width, *a)),
                "not i{width}: {a:#x}"
            );
            let results = machine.call(&is_zero, &[val(width, *a)]);
            assert_eq!(
                bits_from(width, &results[0]),
                u64::from(*a == 0),
                "is_zero i{width}: {a:#x}"
            );
            total += 2;
        }
    }
    eprintln!("bitwise, shift, division and comparison: {total} results compared");
}

#[test]
fn division_edge_cases_do_not_trap_except_by_zero() {
    for (width, min) in [(32, 0x8000_0000u64), (64, 1 << 63)] {
        let ty = ir_type(width);
        let source = binary_function("sdiv", ty, ty) + &binary_function("smod", ty, ty);
        let mut machine = Machine::new(&compile_valid(&parse(&source)));
        let minus_one = mask(width);
        let sdiv = machine.func("sdiv");
        let smod = machine.func("smod");
        let quotient = machine.call(&sdiv, &[val(width, min), val(width, minus_one)]);
        assert_eq!(bits_from(width, &quotient[0]), min, "MIN / -1 wraps to MIN");
        let remainder = machine.call(&smod, &[val(width, min), val(width, minus_one)]);
        assert_eq!(bits_from(width, &remainder[0]), 0, "MIN % -1 is zero");
        assert!(
            machine
                .try_call(&sdiv, &[val(width, 1), val(width, 0)])
                .is_err()
        );
    }
}

#[test]
fn bswap_reverses_bytes() {
    let source = "func public %bswap16(v0.i16) -> i16 {
    block0:
        v1.i16 = bswap v0;
        return v1;
}
func public %bswap32(v0.i32) -> i32 {
    block0:
        v1.i32 = bswap v0;
        return v1;
}
func public %bswap64(v0.i64) -> i64 {
    block0:
        v1.i64 = bswap v0;
        return v1;
}
func public %bswap8(v0.i8) -> i8 {
    block0:
        v1.i8 = bswap v0;
        return v1;
}
";
    let mut machine = Machine::new(&compile_valid(&parse(source)));
    let mut rng = Lcg(7);
    for (name, width) in [
        ("bswap8", 8),
        ("bswap16", 16),
        ("bswap32", 32),
        ("bswap64", 64),
    ] {
        let func = machine.func(name);
        for _ in 0..200 {
            let a = rng.next() & mask(width);
            let results = machine.call(&func, &[val(width, a)]);
            assert_eq!(
                bits_from(width, &results[0]),
                bits_of(width, imm(width, a).bswap()),
                "{name}: {a:#x}"
            );
        }
    }
}

#[test]
fn bit_counts_count_zeros_at_each_width() {
    let widths = [1u32, 8, 16, 32, 64];
    let mut source = String::new();
    for width in widths {
        let t = ir_type(width);
        for op in ["clz", "ctz"] {
            source += &format!(
                "func public %{op}{width}(v0.{t}) -> {t} {{
    block0:
        v1.{t} = {op} v0;
        return v1;
}}
"
            );
        }
    }
    let mut machine = Machine::new(&compile_valid(&parse(&source)));
    for width in widths {
        for a in operands(width) {
            let (leading, trailing) = if a == 0 {
                (u64::from(width), u64::from(width))
            } else {
                (
                    u64::from(a.leading_zeros() - (64 - width)),
                    u64::from(a.trailing_zeros()),
                )
            };
            for (op, expected) in [("clz", leading), ("ctz", trailing)] {
                let func = machine.func(&format!("{op}{width}"));
                let results = machine.call(&func, &[val(width, a)]);
                assert_eq!(
                    bits_from(width, &results[0]),
                    expected,
                    "{op}{width}: {a:#x}"
                );
            }
        }
    }
}

#[test]
fn freeze_returns_its_argument() {
    let widths = [1u32, 8, 16, 32, 64];
    let mut source = String::new();
    for width in widths {
        let t = ir_type(width);
        source += &format!(
            "func public %freeze{width}(v0.{t}) -> {t} {{
    block0:
        v1.{t} = freeze v0;
        return v1;
}}
"
        );
    }
    let mut machine = Machine::new(&compile_valid(&parse(&source)));
    for width in widths {
        let func = machine.func(&format!("freeze{width}"));
        for a in operands(width) {
            let results = machine.call(&func, &[val(width, a)]);
            assert_eq!(bits_from(width, &results[0]), a, "freeze{width}: {a:#x}");
        }
    }
}

#[test]
fn extensions_and_truncations_match_the_reference() {
    let widths = [1u32, 8, 16, 32, 64];
    let mut source = String::new();
    let mut cases = Vec::new();
    for &from in &widths {
        for &to in &widths {
            let (f, t) = (ir_type(from), ir_type(to));
            if to > from {
                for op in ["zext", "sext"] {
                    source += &format!(
                        "func public %{op}_{from}_{to}(v0.{f}) -> {t} {{
    block0:
        v1.{t} = {op} v0 {t};
        return v1;
}}
"
                    );
                    cases.push((op, from, to));
                }
            } else if to < from {
                source += &format!(
                    "func public %trunc_{from}_{to}(v0.{f}) -> {t} {{
    block0:
        v1.{t} = trunc v0 {t};
        return v1;
}}
"
                );
                cases.push(("trunc", from, to));
            }
        }
    }
    let mut machine = Machine::new(&compile_valid(&parse(&source)));
    let mut rng = Lcg(11);
    let mut compared = 0;
    for (op, from, to) in cases {
        let func = machine.func(&format!("{op}_{from}_{to}"));
        let mut inputs = operands(from);
        inputs.extend((0..100).map(|_| rng.next() & mask(from)));
        if from == 1 {
            inputs = vec![0, 1];
        }
        for a in inputs {
            let results = machine.call(&func, &[val(from, a)]);
            let source = imm(from, a);
            let expected = match op {
                "zext" => source.zext(imm(to, 0).ty()),
                "sext" if from == 1 => {
                    // `i1 1` is -1 when sign-extended, as in the native backend.
                    Immediate::from_i256(-sonatina_ir::I256::from(a), imm(to, 0).ty())
                }
                "sext" => source.sext(imm(to, 0).ty()),
                _ => source.trunc(imm(to, 0).ty()),
            };
            assert_eq!(
                bits_from(to, &results[0]),
                bits_of(to, expected),
                "{op} i{from} to i{to}: {a:#x}"
            );
            compared += 1;
        }
    }
    eprintln!("extension and truncation: {compared} results compared");
}

#[test]
fn narrow_parameters_are_canonicalized_at_the_boundary() {
    let source = "func public %add8(v0.i8, v1.i8) -> i8 {
    block0:
        v2.i8 = add v0 v1;
        return v2;
}
func public %lt8(v0.i8, v1.i8) -> i1 {
    block0:
        v2.i1 = lt v0 v1;
        return v2;
}
func public %widen(v0.i8) -> i32 {
    block0:
        v1.i32 = zext v0 i32;
        return v1;
}
";
    let mut machine = Machine::new(&compile_valid(&parse(source)));
    // The host passes bits above the width of the parameter.
    let add8 = machine.func("add8");
    let results = machine.call(&add8, &[Val::I32(0x1ff), Val::I32(0x201)]);
    assert_eq!(bits_from(8, &results[0]), 0, "0xff + 0x01 wraps in i8");
    let lt8 = machine.func("lt8");
    let results = machine.call(&lt8, &[Val::I32(0x100), Val::I32(1)]);
    assert_eq!(bits_from(1, &results[0]), 1, "0 < 1 after canonicalization");
    let widen = machine.func("widen");
    let results = machine.call(&widen, &[Val::I32(-1)]);
    assert_eq!(bits_from(32, &results[0]), 0xff);
}

#[test]
fn bitwise_operations_on_canonical_values_stay_canonical_through_phis() {
    // A negative i8 constant must not leak sign bits into an i32 carrier.
    let source = "func public %pick(v0.i1) -> i32 {
    block0:
        br v0 block1 block2;
    block1:
        jump block3;
    block2:
        jump block3;
    block3:
        v1.i8 = phi (-1.i8 block1) (-128.i8 block2);
        v2.i32 = zext v1 i32;
        return v2;
}
";
    let mut machine = Machine::new(&compile_valid(&parse(source)));
    let pick = machine.func("pick");
    assert_eq!(bits_from(32, &machine.call(&pick, &[Val::I32(1)])[0]), 0xff);
    assert_eq!(bits_from(32, &machine.call(&pick, &[Val::I32(0)])[0]), 0x80);
}
