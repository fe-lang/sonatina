//! 128-bit integers, compared with the reference semantics of `Immediate`.
//!
//! A 128-bit value cannot cross the module boundary, so the functions take and
//! return its 64-bit halves and move it through memory, calls and phis.

use sonatina_codegen::OptLevel;
use sonatina_ir::{Immediate, U256};
use wasmtime::Val;

use super::{aggregates::build_at, harness::Machine};
use crate::Lcg;

const PRELUDE: &str = "func private %pack(v0.i64, v1.i64) -> i128 {
    block0:
        v2.*[i64; 2] = alloca [i64; 2];
        v3.*i64 = gep v2 0.i32 0.i32;
        mstore v3 v0 i64;
        v4.*i64 = gep v2 0.i32 1.i32;
        mstore v4 v1 i64;
        v5.i128 = mload v2 i128;
        return v5;
}
func private %unpack(v0.i128) -> (i64, i64) {
    block0:
        v1.*[i64; 2] = alloca [i64; 2];
        mstore v1 v0 i128;
        v2.i64 = mload v1 i64;
        v3.*i64 = gep v1 0.i32 1.i32;
        v4.i64 = mload v3 i64;
        return (v2, v4);
}
";

const LEVELS: [OptLevel; 2] = [OptLevel::O0, OptLevel::O2];

type Reference = fn(Immediate, Immediate) -> Immediate;
type OverflowReference = fn(Immediate, Immediate) -> (Immediate, bool);

/// Instructions with one 128-bit result, using v4 and v5 and defining v6. A
/// shift takes its count, v5, first.
const VALUES: [(&str, Reference); 24] = [
    ("v6.i128 = add v4 v5;", |a, b| a + b),
    ("v6.i128 = sub v4 v5;", |a, b| a - b),
    ("v6.i128 = mul v4 v5;", |a, b| a * b),
    ("v6.i128 = and v4 v5;", |a, b| a & b),
    ("v6.i128 = or v4 v5;", |a, b| a | b),
    ("v6.i128 = xor v4 v5;", |a, b| a ^ b),
    ("v6.i128 = shl v5 v4;", |a, b| a << b),
    ("v6.i128 = shr v5 v4;", |a, b| a >> b),
    ("v6.i128 = sar v5 v4;", Immediate::ashr),
    ("v6.i128 = udiv v4 v5;", Immediate::udiv),
    ("v6.i128 = sdiv v4 v5;", Immediate::sdiv),
    ("v6.i128 = umod v4 v5;", Immediate::urem),
    ("v6.i128 = smod v4 v5;", Immediate::srem),
    ("v6.i128 = uaddsat v4 v5;", Immediate::saturating_uadd),
    ("v6.i128 = usubsat v4 v5;", Immediate::saturating_usub),
    ("v6.i128 = umulsat v4 v5;", Immediate::saturating_umul),
    ("v6.i128 = saddsat v4 v5;", Immediate::saturating_sadd),
    ("v6.i128 = ssubsat v4 v5;", Immediate::saturating_ssub),
    ("v6.i128 = smulsat v4 v5;", Immediate::saturating_smul),
    ("v6.i128 = neg v4;", |a, _| -a),
    ("v6.i128 = not v4;", |a, _| !a),
    ("v6.i128 = bswap v4;", |a, _| a.bswap()),
    ("v6.i128 = clz v4;", |a, _| {
        Immediate::I128(bits(a).leading_zeros().into())
    }),
    ("v6.i128 = ctz v4;", |a, _| {
        Immediate::I128(bits(a).trailing_zeros().into())
    }),
];

/// Instructions with an `i1` result v6.
const FLAGS: [(&str, Reference); 11] = [
    ("v6.i1 = eq v4 v5;", Immediate::imm_eq),
    ("v6.i1 = ne v4 v5;", Immediate::imm_ne),
    ("v6.i1 = lt v4 v5;", Immediate::lt),
    ("v6.i1 = gt v4 v5;", Immediate::gt),
    ("v6.i1 = le v4 v5;", Immediate::le),
    ("v6.i1 = ge v4 v5;", Immediate::ge),
    ("v6.i1 = slt v4 v5;", Immediate::slt),
    ("v6.i1 = sgt v4 v5;", Immediate::sgt),
    ("v6.i1 = sle v4 v5;", Immediate::sle),
    ("v6.i1 = sge v4 v5;", Immediate::sge),
    ("v6.i1 = is_zero v4;", |a, _| a.is_zero().into()),
];

/// Instructions with a 128-bit result v6 and an overflow flag v7.
const CHECKED: [(&str, OverflowReference); 7] = [
    (
        "(v6.i128, v7.i1) = uaddo v4 v5;",
        Immediate::overflowing_uadd,
    ),
    (
        "(v6.i128, v7.i1) = usubo v4 v5;",
        Immediate::overflowing_usub,
    ),
    (
        "(v6.i128, v7.i1) = umulo v4 v5;",
        Immediate::overflowing_umul,
    ),
    (
        "(v6.i128, v7.i1) = saddo v4 v5;",
        Immediate::overflowing_sadd,
    ),
    (
        "(v6.i128, v7.i1) = ssubo v4 v5;",
        Immediate::overflowing_ssub,
    ),
    (
        "(v6.i128, v7.i1) = smulo v4 v5;",
        Immediate::overflowing_smul,
    ),
    ("(v6.i128, v7.i1) = snego v4;", |a, _| a.overflowing_sneg()),
];

fn bits(value: Immediate) -> u128 {
    value.as_i256().to_u256().low_u128()
}

fn imm(value: u128) -> Immediate {
    Immediate::I128(value as i128)
}

/// A mix of boundary values and random values with a random number of bits.
fn operand(rng: &mut Lcg) -> u128 {
    let random = (u128::from(rng.next()) << 64) | u128::from(rng.next());
    let bit = 1u128 << (rng.next() % 128);
    match rng.next() % 11 {
        0 => 0,
        1 => 1,
        2 => u128::MAX,
        3 => 1 << 127,
        4 => (1 << 127) - 1,
        5 => bit,
        6 => bit - 1,
        7 => u128::from(rng.next() % 1000),
        8 => u128::from(rng.next()),
        9 => u128::from(rng.next() % 1000).wrapping_neg(),
        _ => random.checked_shr((rng.next() % 129) as u32).unwrap_or(0),
    }
}

/// The count operand of a shift: mostly in range, sometimes not.
fn shift_count(rng: &mut Lcg) -> u128 {
    match rng.next() % 8 {
        0 => 128,
        1 => 127,
        2 => u128::MAX,
        3 => 1 << 64,
        4 => 1 << 127,
        5 => u128::from(rng.next() % 3) * 64,
        _ => u128::from(rng.next() % 140),
    }
}

fn halves(value: u128) -> [Val; 2] {
    [Val::I64(value as i64), Val::I64((value >> 64) as i64)]
}

fn from_halves(values: &[Val]) -> u128 {
    u128::from(values[0].unwrap_i64() as u64) | (u128::from(values[1].unwrap_i64() as u64) << 64)
}

fn function(index: usize, instruction: &str, returns: &str, tail: &str) -> String {
    format!(
        "func public %c{index}(v0.i64, v1.i64, v2.i64, v3.i64) -> {returns} {{
    block0:
        v4.i128 = call %pack v0 v1;
        v5.i128 = call %pack v2 v3;
        {instruction}
        {tail}
}}
"
    )
}

#[test]
fn a_128_bit_product_needs_no_multiplication_function() {
    // The product is at most three limb products, built in place; only the
    // checked product calls `i256.mulo`. The name section lists the functions.
    let module = |instruction: &str| {
        let source = format!(
            "{PRELUDE}func public %f(v0.i64, v1.i64, v2.i64, v3.i64) -> (i64, i64) {{
    block0:
        v4.i128 = call %pack v0 v1;
        v5.i128 = call %pack v2 v3;
        {instruction}
        (v8.i64, v9.i64) = call %unpack v6;
        return (v8, v9);
}}"
        );
        build_at(&source, OptLevel::O2)
    };
    let has_helper = |bytes: &[u8]| bytes.windows(9).any(|name| name == b"i256.mulo");
    assert!(!has_helper(&module("v6.i128 = mul v4 v5;")));
    assert!(has_helper(&module("(v6.i128, v7.i1) = umulo v4 v5;")));
}

#[test]
fn every_128_bit_operation_matches_the_reference() {
    // The halves of v6, and v12: whether v6 extended to 256 bits has no bits
    // above 128.
    let unpack = "(v8.i64, v9.i64) = call %unpack v6;
        v10.i256 = zext v6 i256;
        v11.i256 = shr 128.i256 v10;
        v12.i1 = is_zero v11;";
    let mut source = PRELUDE.to_string();
    let mut index = 0;
    for (instruction, _) in VALUES {
        source += &function(
            index,
            instruction,
            "(i64, i64, i1)",
            &format!("{unpack}\n        return (v8, v9, v12);"),
        );
        index += 1;
    }
    for (instruction, _) in FLAGS {
        source += &function(index, instruction, "i1", "return v6;");
        index += 1;
    }
    for (instruction, _) in CHECKED {
        source += &function(
            index,
            instruction,
            "(i64, i64, i1, i1)",
            &format!("{unpack}\n        return (v8, v9, v7, v12);"),
        );
        index += 1;
    }

    let mut rng = Lcg(0x5eed_1281);
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(&source, level));
        let mut call = |index: usize, instruction: &str, rng: &mut Lcg| {
            let (_, text) = instruction
                .split_once("= ")
                .expect("an instruction defines v6");
            let op = text.split(' ').next().expect("an instruction has a name");
            let a = operand(rng);
            let b = if matches!(op, "shl" | "shr" | "sar") {
                shift_count(rng)
            } else {
                operand(rng)
            };
            if matches!(op, "udiv" | "sdiv" | "umod" | "smod") && b == 0 {
                return None;
            }
            let f = machine.func(&format!("c{index}"));
            let args: Vec<Val> = halves(a).into_iter().chain(halves(b)).collect();
            Some((a, b, machine.call(&f, &args)))
        };
        let mut index = 0;
        for (instruction, reference) in VALUES {
            for _ in 0..300 {
                let Some((a, b, got)) = call(index, instruction, &mut rng) else {
                    continue;
                };
                let want = bits(reference(imm(a), imm(b)));
                let what = format!("{instruction} {level:?} a={a:#x} b={b:#x}");
                assert_eq!(from_halves(&got[..2]), want, "{what}");
                assert_ne!(got[2].unwrap_i32(), 0, "{what} (bits above 128)");
            }
            index += 1;
        }
        for (instruction, reference) in FLAGS {
            for _ in 0..300 {
                let Some((a, b, got)) = call(index, instruction, &mut rng) else {
                    continue;
                };
                let want = !reference(imm(a), imm(b)).is_zero();
                let what = format!("{instruction} {level:?} a={a:#x} b={b:#x}");
                assert_eq!(got[0].unwrap_i32() != 0, want, "{what}");
            }
            index += 1;
        }
        for (instruction, reference) in CHECKED {
            for _ in 0..300 {
                let Some((a, b, got)) = call(index, instruction, &mut rng) else {
                    continue;
                };
                let (value, overflow) = reference(imm(a), imm(b));
                let what = format!("{instruction} {level:?} a={a:#x} b={b:#x}");
                assert_eq!(from_halves(&got[..2]), bits(value), "{what}");
                assert_eq!(got[2].unwrap_i32() != 0, overflow, "{what} (flag)");
                assert_ne!(got[3].unwrap_i32(), 0, "{what} (bits above 128)");
            }
            index += 1;
        }
    }
}

#[test]
fn a_loop_carries_a_128_bit_value_in_a_phi() {
    // Fibonacci numbers modulo 2^128: the sums carry between the halves and
    // later wrap.
    let source = format!(
        "{PRELUDE}func public %fib(v0.i64) -> (i64, i64) {{
    block0:
        jump block1;
    block1:
        v1.i128 = phi (0.i128 block0) (v2 block1);
        v2.i128 = phi (1.i128 block0) (v3 block1);
        v4.i64 = phi (0.i64 block0) (v5 block1);
        v3.i128 = add v1 v2;
        v5.i64 = add v4 1.i64;
        v6.i1 = lt v5 v0;
        br v6 block1 block2;
    block2:
        (v7.i64, v8.i64) = call %unpack v3;
        return (v7, v8);
}}"
    );
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(&source, level));
        let fib = machine.func("fib");
        for n in [1u64, 2, 90, 100, 186, 187, 300] {
            let (mut a, mut b, mut sum) = (0u128, 1u128, 0u128);
            for _ in 0..n {
                sum = a.wrapping_add(b);
                (a, b) = (b, sum);
            }
            let got = from_halves(&machine.call(&fib, &[Val::I64(n as i64)]));
            assert_eq!(got, sum, "{level:?} fib({n})");
        }
    }
}

#[test]
fn conversions_extend_and_truncate_128_bit_values() {
    let source = format!(
        "{PRELUDE}func public %convert(v0.i64) -> (i64, i64, i64, i64, i64, i64) {{
    block0:
        v1.i128 = sext v0 i128;
        v2.i128 = zext v0 i128;
        v3.i256 = sext v1 i256;
        v4.i256 = zext v1 i256;
        v5.i256 = shr 128.i256 v3;
        v6.i64 = trunc v5 i64;
        v7.i256 = shr 128.i256 v4;
        v8.i64 = trunc v7 i64;
        v9.i128 = trunc v3 i128;
        v10.i1 = eq v9 v1;
        v11.i64 = zext v10 i64;
        v12.i8 = trunc v1 i8;
        v13.i128 = sext v12 i128;
        (v14.i64, v15.i64) = call %unpack v13;
        (v16.i64, v17.i64) = call %unpack v2;
        return (v6, v8, v11, v15, v14, v17);
}}"
    );
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(&source, level));
        let convert = machine.func("convert");
        for x in [0i64, 7, -5, 0x1ff, i64::MIN, i64::MAX] {
            let got: Vec<i64> = machine
                .call(&convert, &[Val::I64(x)])
                .iter()
                .map(Val::unwrap_i64)
                .collect();
            let fill = x >> 63;
            let byte = i64::from(x as i8);
            // The sign fill above 128 bits, none for `zext`, a `trunc` that
            // undoes the `sext`, the high and low halves of a sign-extended
            // byte, and the high half of a zero-extended value.
            let want = [fill, 0, 1, byte >> 63, byte, 0];
            assert_eq!(got, want, "{level:?} convert({x})");
        }
    }
}

#[test]
fn aggregates_objects_and_constants_hold_128_bit_fields() {
    let source = format!(
        "type @Pair = {{ i8, i128 }};
global private const @Pair $pair = {{7, -2}};
{PRELUDE}func public %fields(v0.i64, v1.i64) -> (i64, i64, i64, i64, i64, i64) {{
    block0:
        v2.i128 = call %pack v0 v1;
        v3.@Pair = insert_value undef.@Pair 1.i32 v2;
        v4.i128 = extract_value v3 1.i32;
        v5.i128 = add v4 1.i128;
        v6.objref<i128> = obj.alloc i128;
        obj.store v6 v5;
        v7.i128 = obj.load v6;
        v8.constref<@Pair> = const.ref $pair;
        v9.constref<i128> = const.proj v8 1.i32;
        v10.i128 = const.load v9;
        v11.[i64; 2] = bitcast v2 [i64; 2];
        v12.i64 = extract_value v11 0.i32;
        v13.i64 = extract_value v11 1.i32;
        (v14.i64, v15.i64) = call %unpack v7;
        (v16.i64, v17.i64) = call %unpack v10;
        return (v14, v15, v16, v17, v13, v12);
}}"
    );
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(&source, level));
        let fields = machine.func("fields");
        for value in [0u128, u128::from(u64::MAX), u128::MAX, 0x1234 << 70] {
            let got: Vec<i64> = machine
                .call(&fields, &halves(value))
                .iter()
                .map(Val::unwrap_i64)
                .collect();
            let next = value.wrapping_add(1);
            let want = [
                next as i64,
                (next >> 64) as i64,
                -2,
                -1,
                (value >> 64) as i64,
                value as i64,
            ];
            assert_eq!(got, want, "{level:?} fields({value:#x})");
        }
    }
}

#[test]
fn br_table_and_modular_arithmetic_take_128_bit_operands() {
    let source = format!(
        "{PRELUDE}func public %select(v0.i64, v1.i64) -> i32 {{
    block0:
        v2.i128 = call %pack v0 v1;
        br_table v2 block3 (1.i128 block1) (18446744073709551617.i128 block2) (-1.i128 block4);
    block1:
        return 10.i32;
    block2:
        return 20.i32;
    block3:
        return 0.i32;
    block4:
        return 99.i32;
}}
func public %modular(v0.i64, v1.i64, v2.i64, v3.i64, v4.i64, v5.i64) -> (i64, i64, i64, i64) {{
    block0:
        v6.i128 = call %pack v0 v1;
        v7.i128 = call %pack v2 v3;
        v8.i128 = call %pack v4 v5;
        v9.i128 = evm_add_mod v6 v7 v8;
        v10.i128 = evm_mul_mod v6 v7 v8;
        (v11.i64, v12.i64) = call %unpack v9;
        (v13.i64, v14.i64) = call %unpack v10;
        return (v11, v12, v13, v14);
}}"
    );
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(&source, level));
        let select = machine.func("select");
        for (value, want) in [
            (1u128, 10),
            ((1 << 64) + 1, 20),
            (1 << 64, 0),
            (u128::MAX, 99),
        ] {
            let got = machine.call(&select, &halves(value))[0].unwrap_i32();
            assert_eq!(got, want, "{level:?} select({value:#x})");
        }
        let modular = machine.func("modular");
        let max = u128::MAX;
        for (a, b, n) in [
            (max, max, max - 1),
            (max, max, 1 << 127),
            (5, 7, 0),
            ((1 << 100) + 3, 1 << 90, (1 << 64) + 7),
        ] {
            let args: Vec<Val> = [a, b, n].into_iter().flat_map(halves).collect();
            let got = machine.call(&modular, &args);
            // The sum and product are exact, and zero for a zero modulus.
            let (a, b, n) = (U256::from(a), U256::from(b), U256::from(n));
            let reduce = |value: U256| {
                if n.is_zero() {
                    0
                } else {
                    (value % n).low_u128()
                }
            };
            let want = [reduce(a + b), reduce(a * b)];
            assert_eq!(
                [from_halves(&got[..2]), from_halves(&got[2..])],
                want,
                "{level:?} modular({a:#x}, {b:#x}, {n:#x})"
            );
        }
    }
}

#[test]
fn a_128_bit_address_or_index_traps_when_it_does_not_fit() {
    let source = format!(
        "{PRELUDE}func public %index(v0.i64, v1.i64, v2.*[i64; 4]) -> i64 {{
    block0:
        v3.i128 = call %pack v0 v1;
        v4.*i64 = gep v2 0.i32 v3;
        v5.i64 = mload v4 i64;
        v6.i128 = ptr_to_int v4 i128;
        v7.i128 = add v6 8.i128;
        v8.*i64 = int_to_ptr v7 *i64;
        v9.i64 = mload v8 i64;
        v10.i64 = add v5 v9;
        return v10;
}}"
    );
    for level in LEVELS {
        let mut machine = Machine::new(&build_at(&source, level));
        let out = machine.memory_size();
        machine.grow_memory(1);
        let words: Vec<u8> = [10u64, 20, 30, 40]
            .iter()
            .flat_map(|word| word.to_le_bytes())
            .collect();
        machine.write(out, &words);
        let index = machine.func("index");
        let call = |machine: &mut Machine, value: u128, base: usize| {
            let args: Vec<Val> = halves(value)
                .into_iter()
                .chain([Val::I32(base as i32)])
                .collect();
            machine.try_call(&index, &args)
        };
        assert_eq!(call(&mut machine, 1, out).unwrap()[0].unwrap_i64(), 50);
        // The index is signed.
        let back = call(&mut machine, u128::MAX, out + 8).unwrap();
        assert_eq!(back[0].unwrap_i64(), 30, "{level:?}");
        // An index with bits in the high half does not fit in 32 bits.
        for value in [1 << 64, 1 << 127, u128::MAX >> 1] {
            assert!(
                call(&mut machine, value, out).is_err(),
                "{level:?} {value:#x}"
            );
        }
    }
}
