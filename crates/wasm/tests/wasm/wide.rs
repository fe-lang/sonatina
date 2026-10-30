//! 256-bit integers, compared with `U256` and `I256` arithmetic.

use sonatina_codegen::OptLevel;
use sonatina_ir::{I256, U256};
use wasmtime::Val;

use super::{aggregates::build_at, harness::Machine};
use crate::Lcg;

const PRELUDE: &str = "func private %pack(v0.i64, v1.i64, v2.i64, v3.i64) -> i256 {
    block0:
        v4.*[i64; 4] = alloca [i64; 4];
        v5.*i64 = gep v4 0.i32 0.i32;
        mstore v5 v0 i64;
        v6.*i64 = gep v4 0.i32 1.i32;
        mstore v6 v1 i64;
        v7.*i64 = gep v4 0.i32 2.i32;
        mstore v7 v2 i64;
        v8.*i64 = gep v4 0.i32 3.i32;
        mstore v8 v3 i64;
        v9.i256 = mload v4 i256;
        return v9;
}
func private %unpack(v0.i256) -> (i64, i64, i64, i64) {
    block0:
        v1.*[i64; 4] = alloca [i64; 4];
        mstore v1 v0 i256;
        v2.i64 = mload v1 i64;
        v3.*i64 = gep v1 0.i32 1.i32;
        v4.i64 = mload v3 i64;
        v5.*i64 = gep v1 0.i32 2.i32;
        v6.i64 = mload v5 i64;
        v7.*i64 = gep v1 0.i32 3.i32;
        v8.i64 = mload v7 i64;
        return (v2, v4, v6, v8);
}
";

fn limbs(value: U256) -> [u64; 4] {
    value.0
}

fn from_limbs(limbs: &[u64]) -> U256 {
    let mut bytes = [0u8; 32];
    for (index, limb) in limbs.iter().enumerate() {
        bytes[8 * index..8 * index + 8].copy_from_slice(&limb.to_le_bytes());
    }
    U256::from_little_endian(&bytes)
}

fn is_negative(value: U256) -> bool {
    value.bit(255)
}

fn magnitude(value: U256) -> U256 {
    if is_negative(value) {
        (!value).overflowing_add(U256::one()).0
    } else {
        value
    }
}

fn negate(value: U256) -> U256 {
    (!value).overflowing_add(U256::one()).0
}

/// A mix of boundary values and random values with a random number of bits.
fn operand(rng: &mut Lcg) -> U256 {
    let random = |rng: &mut Lcg| from_limbs(&[rng.next(), rng.next(), rng.next(), rng.next()]);
    match rng.next() % 12 {
        0 => U256::zero(),
        1 => U256::one(),
        2 => U256::MAX,
        3 => U256::one() << 255,
        4 => (U256::one() << 255) - 1,
        5 => U256::one() << (rng.next() % 256) as usize,
        6 => {
            (U256::one() << (rng.next() % 256) as usize)
                .overflowing_sub(U256::one())
                .0
        }
        7 => U256::from(rng.next() % 1000),
        8 => U256::from(rng.next()),
        9 => negate(U256::from(rng.next() % 1000)),
        _ => {
            let value = random(rng);
            let bits = rng.next() % 257;
            if bits == 256 {
                value
            } else {
                value & ((U256::one() << bits as usize) - 1)
            }
        }
    }
}

/// The count operand of a shift: mostly in range, sometimes not.
fn shift_count(rng: &mut Lcg) -> U256 {
    match rng.next() % 8 {
        0 => U256::from(256),
        1 => U256::from(255),
        2 => U256::MAX,
        3 => U256::one() << 64,
        4 => U256::from(rng.next() % 4) * 64,
        _ => U256::from(rng.next() % 300),
    }
}

enum Shape {
    /// Four limbs out.
    Value,
    /// Four limbs and a flag out.
    ValueFlag,
    /// One flag out.
    Flag,
}

struct Case {
    name: &'static str,
    /// The instruction line, using v8 and v9 and defining v10 (and v11). For
    /// shifts, v8 is the value and v9 the count (the instruction takes the
    /// count first).
    instruction: &'static str,
    shape: Shape,
    /// Operands that the reference cannot take.
    skip: fn(U256, U256) -> bool,
    /// The result limbs and flag.
    reference: fn(U256, U256) -> (U256, bool),
}

fn never(_: U256, _: U256) -> bool {
    false
}

fn zero_divisor(_: U256, b: U256) -> bool {
    b.is_zero()
}

fn signed(value: U256) -> I256 {
    I256::from_u256(value)
}

fn signed_overflow(sub: bool, a: U256, b: U256, r: U256) -> bool {
    let (sa, sb, sr) = (is_negative(a), is_negative(b), is_negative(r));
    if sub {
        sa != sb && sr != sa
    } else {
        sa == sb && sr != sa
    }
}

fn mul_wide(a: U256, b: U256) -> (U256, bool) {
    let full = a.full_mul(b);
    let low = from_limbs(&full.0[..4]);
    let high = full.0[4] | full.0[5] | full.0[6] | full.0[7];
    (low, high != 0)
}

fn cases() -> Vec<Case> {
    vec![
        Case {
            name: "add",
            instruction: "v10.i256 = add v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (a.overflowing_add(b).0, false),
        },
        Case {
            name: "sub",
            instruction: "v10.i256 = sub v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (a.overflowing_sub(b).0, false),
        },
        Case {
            name: "and",
            instruction: "v10.i256 = and v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (a & b, false),
        },
        Case {
            name: "or",
            instruction: "v10.i256 = or v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (a | b, false),
        },
        Case {
            name: "xor",
            instruction: "v10.i256 = xor v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (a ^ b, false),
        },
        Case {
            name: "not",
            instruction: "v10.i256 = not v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, _| (!a, false),
        },
        Case {
            name: "bswap",
            instruction: "v10.i256 = bswap v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, _| {
                let bytes = a.to_big_endian();
                (U256::from_little_endian(&bytes), false)
            },
        },
        Case {
            name: "evm_clz",
            instruction: "v10.i256 = evm_clz v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, _| (U256::from(a.leading_zeros()), false),
        },
        Case {
            name: "freeze",
            instruction: "v10.i256 = freeze v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, _| (a, false),
        },
        Case {
            name: "neg",
            instruction: "v10.i256 = neg v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, _| (negate(a), false),
        },
        Case {
            name: "uaddo",
            instruction: "(v10.i256, v11.i1) = uaddo v8 v9;",
            shape: Shape::ValueFlag,
            skip: never,
            reference: |a, b| a.overflowing_add(b),
        },
        Case {
            name: "usubo",
            instruction: "(v10.i256, v11.i1) = usubo v8 v9;",
            shape: Shape::ValueFlag,
            skip: never,
            reference: |a, b| a.overflowing_sub(b),
        },
        Case {
            name: "saddo",
            instruction: "(v10.i256, v11.i1) = saddo v8 v9;",
            shape: Shape::ValueFlag,
            skip: never,
            reference: |a, b| {
                let r = a.overflowing_add(b).0;
                (r, signed_overflow(false, a, b, r))
            },
        },
        Case {
            name: "ssubo",
            instruction: "(v10.i256, v11.i1) = ssubo v8 v9;",
            shape: Shape::ValueFlag,
            skip: never,
            reference: |a, b| {
                let r = a.overflowing_sub(b).0;
                (r, signed_overflow(true, a, b, r))
            },
        },
        Case {
            name: "snego",
            instruction: "(v10.i256, v11.i1) = snego v8;",
            shape: Shape::ValueFlag,
            skip: never,
            reference: |a, _| (negate(a), a == U256::one() << 255),
        },
        Case {
            name: "mul",
            instruction: "v10.i256 = mul v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (mul_wide(a, b).0, false),
        },
        Case {
            name: "umulo",
            instruction: "(v10.i256, v11.i1) = umulo v8 v9;",
            shape: Shape::ValueFlag,
            skip: never,
            reference: mul_wide,
        },
        Case {
            name: "smulo",
            instruction: "(v10.i256, v11.i1) = smulo v8 v9;",
            shape: Shape::ValueFlag,
            skip: never,
            reference: |a, b| {
                let (product, overflow) = mul_wide(magnitude(a), magnitude(b));
                let negative = is_negative(a) != is_negative(b);
                let limit = U256::one() << 255;
                let too_big = if negative {
                    product > limit
                } else {
                    product >= limit
                };
                let result = if negative { negate(product) } else { product };
                (result, overflow || too_big)
            },
        },
        Case {
            name: "udiv",
            instruction: "v10.i256 = udiv v8 v9;",
            shape: Shape::Value,
            skip: zero_divisor,
            reference: |a, b| (a / b, false),
        },
        Case {
            name: "umod",
            instruction: "v10.i256 = umod v8 v9;",
            shape: Shape::Value,
            skip: zero_divisor,
            reference: |a, b| (a % b, false),
        },
        Case {
            name: "sdiv",
            instruction: "v10.i256 = sdiv v8 v9;",
            shape: Shape::Value,
            skip: zero_divisor,
            reference: |a, b| (signed(a).overflowing_div(signed(b)).0.to_u256(), false),
        },
        Case {
            name: "smod",
            instruction: "v10.i256 = smod v8 v9;",
            shape: Shape::Value,
            skip: zero_divisor,
            reference: |a, b| (signed(a).overflowing_rem(signed(b)).0.to_u256(), false),
        },
        Case {
            name: "shl",
            instruction: "v10.i256 = shl v9 v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, n| {
                (
                    if n < U256::from(256) {
                        a << n.as_usize()
                    } else {
                        U256::zero()
                    },
                    false,
                )
            },
        },
        Case {
            name: "shr",
            instruction: "v10.i256 = shr v9 v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, n| {
                (
                    if n < U256::from(256) {
                        a >> n.as_usize()
                    } else {
                        U256::zero()
                    },
                    false,
                )
            },
        },
        Case {
            name: "sar",
            instruction: "v10.i256 = sar v9 v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, n| {
                let negative = is_negative(a);
                let base = if negative { !a } else { a };
                let shifted = if n < U256::from(256) {
                    base >> n.as_usize()
                } else {
                    U256::zero()
                };
                (if negative { !shifted } else { shifted }, false)
            },
        },
        Case {
            name: "eq",
            instruction: "v10.i1 = eq v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), a == b),
        },
        Case {
            name: "ne",
            instruction: "v10.i1 = ne v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), a != b),
        },
        Case {
            name: "lt",
            instruction: "v10.i1 = lt v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), a < b),
        },
        Case {
            name: "le",
            instruction: "v10.i1 = le v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), a <= b),
        },
        Case {
            name: "gt",
            instruction: "v10.i1 = gt v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), a > b),
        },
        Case {
            name: "ge",
            instruction: "v10.i1 = ge v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), a >= b),
        },
        Case {
            name: "slt",
            instruction: "v10.i1 = slt v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), signed_lt(a, b)),
        },
        Case {
            name: "sle",
            instruction: "v10.i1 = sle v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), !signed_lt(b, a)),
        },
        Case {
            name: "sgt",
            instruction: "v10.i1 = sgt v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), signed_lt(b, a)),
        },
        Case {
            name: "sge",
            instruction: "v10.i1 = sge v8 v9;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, b| (U256::zero(), !signed_lt(a, b)),
        },
        Case {
            name: "is_zero",
            instruction: "v10.i1 = is_zero v8;",
            shape: Shape::Flag,
            skip: never,
            reference: |a, _| (U256::zero(), a.is_zero()),
        },
    ]
}

fn signed_lt(a: U256, b: U256) -> bool {
    match (is_negative(a), is_negative(b)) {
        (true, false) => true,
        (false, true) => false,
        _ => a < b,
    }
}

fn module_for(case: &Case) -> String {
    let (returns, tail) = match case.shape {
        Shape::Value => (
            "(i64, i64, i64, i64)",
            "(v11.i64, v12.i64, v13.i64, v14.i64) = call %unpack v10;\n        return (v11, v12, v13, v14);",
        ),
        Shape::ValueFlag => (
            "(i64, i64, i64, i64, i1)",
            "(v21.i64, v22.i64, v23.i64, v24.i64) = call %unpack v10;\n        return (v21, v22, v23, v24, v11);",
        ),
        Shape::Flag => ("i1", "return v10;"),
    };
    format!(
        "{PRELUDE}func public %f(v0.i64, v1.i64, v2.i64, v3.i64, v4.i64, v5.i64, v6.i64, v7.i64) -> {returns} {{
    block0:
        v8.i256 = call %pack v0 v1 v2 v3;
        v9.i256 = call %pack v4 v5 v6 v7;
        {}
        {tail}
}}",
        case.instruction
    )
}

fn arguments(a: U256, b: U256) -> Vec<Val> {
    limbs(a)
        .into_iter()
        .chain(limbs(b))
        .map(|limb| Val::I64(limb as i64))
        .collect()
}

fn run_case(case: &Case, level: OptLevel, rng: &mut Lcg, count: usize) {
    let source = module_for(case);
    let mut machine = Machine::new(&build_at(&source, level));
    let f = machine.func("f");
    let mut pairs = Vec::new();
    for _ in 0..count {
        let b = if matches!(case.name, "shl" | "shr" | "sar") {
            shift_count(rng)
        } else {
            operand(rng)
        };
        pairs.push((operand(rng), b));
    }
    for (a, b) in pairs {
        if (case.skip)(a, b) {
            continue;
        }
        let (want, flag) = (case.reference)(a, b);
        let got = machine.call(&f, &arguments(a, b));
        let what = format!("{} {:?} a={a:#x} b={b:#x}", case.name, level);
        match case.shape {
            Shape::Value => {
                let limbs: Vec<u64> = got.iter().map(|v| v.unwrap_i64() as u64).collect();
                assert_eq!(from_limbs(&limbs), want, "{what}");
            }
            Shape::ValueFlag => {
                let limbs: Vec<u64> = got[..4].iter().map(|v| v.unwrap_i64() as u64).collect();
                assert_eq!(from_limbs(&limbs), want, "{what}");
                assert_eq!(got[4].unwrap_i32() != 0, flag, "{what} (flag)");
            }
            Shape::Flag => assert_eq!(got[0].unwrap_i32() != 0, flag, "{what}"),
        }
    }
}

#[test]
fn every_256_bit_operation_matches_the_reference() {
    let mut rng = Lcg(0x5eed_2561);
    for case in cases() {
        for level in [OptLevel::O0, OptLevel::O2] {
            run_case(&case, level, &mut rng, 400);
        }
    }
}

#[test]
fn division_by_zero_traps_and_leaves_the_instance_usable() {
    let source = format!(
        "{PRELUDE}func public %f(v0.i64, v1.i64) -> i64 {{
    block0:
        v2.i256 = zext v0 i256;
        v3.i256 = zext v1 i256;
        v4.i256 = udiv v2 v3;
        v5.i64 = trunc v4 i64;
        return v5;
}}"
    );
    let mut machine = Machine::new(&build_at(&source, OptLevel::O2));
    let f = machine.func("f");
    assert!(machine.try_call(&f, &[Val::I64(5), Val::I64(0)]).is_err());
    assert_eq!(
        machine.call(&f, &[Val::I64(91), Val::I64(7)])[0].unwrap_i64(),
        13
    );
}

/// `(a + b) mod n` or `(a * b) mod n` in full precision, and zero if `n` is
/// zero.
fn modular_reference(product: bool, a: U256, b: U256, n: U256) -> U256 {
    if n.is_zero() {
        return U256::zero();
    }
    let wide = |x: U256| x.full_mul(U256::one());
    let modulus = wide(n);
    let value = if product {
        a.full_mul(b)
    } else {
        wide(a) + wide(b)
    };
    U256::try_from(value % modulus).expect("a remainder below a 256-bit modulus fits")
}

/// A modulus: boundary values and random values.
fn modulus(rng: &mut Lcg) -> U256 {
    match rng.next() % 8 {
        0 => U256::zero(),
        1 => U256::one(),
        2 => U256::MAX,
        3 => (U256::one() << 255) + U256::from(rng.next() % 3),
        4 => U256::from(rng.next() | 1),
        5 => U256::one() << (rng.next() % 256) as usize,
        _ => operand(rng),
    }
}

#[test]
fn addmod_and_mulmod_match_the_exact_result() {
    let source = format!(
        "{PRELUDE}func public %f(v0.i64, v1.i64, v2.i64, v3.i64, v4.i64, v5.i64, v6.i64, v7.i64, v8.i64, v9.i64, v10.i64, v11.i64) -> (i64, i64, i64, i64, i64, i64, i64, i64) {{
    block0:
        v12.i256 = call %pack v0 v1 v2 v3;
        v13.i256 = call %pack v4 v5 v6 v7;
        v14.i256 = call %pack v8 v9 v10 v11;
        v15.i256 = evm_add_mod v12 v13 v14;
        v16.i256 = evm_mul_mod v12 v13 v14;
        (v17.i64, v18.i64, v19.i64, v20.i64) = call %unpack v15;
        (v21.i64, v22.i64, v23.i64, v24.i64) = call %unpack v16;
        return (v17, v18, v19, v20, v21, v22, v23, v24);
}}"
    );
    let mut rng = Lcg(0x5eed_3d0d);
    for level in [OptLevel::O0, OptLevel::O2] {
        let mut machine = Machine::new(&build_at(&source, level));
        let f = machine.func("f");
        for _ in 0..300 {
            let (a, b, n) = (operand(&mut rng), operand(&mut rng), modulus(&mut rng));
            let arguments: Vec<Val> = limbs(a)
                .into_iter()
                .chain(limbs(b))
                .chain(limbs(n))
                .map(|limb| Val::I64(limb as i64))
                .collect();
            let got = machine.call(&f, &arguments);
            let read = |range: std::ops::Range<usize>| {
                let limbs: Vec<u64> = got[range].iter().map(|v| v.unwrap_i64() as u64).collect();
                from_limbs(&limbs)
            };
            let what = format!("{level:?} a={a:#x} b={b:#x} n={n:#x}");
            assert_eq!(
                read(0..4),
                modular_reference(false, a, b, n),
                "addmod {what}"
            );
            assert_eq!(
                read(4..8),
                modular_reference(true, a, b, n),
                "mulmod {what}"
            );
        }
    }
}
