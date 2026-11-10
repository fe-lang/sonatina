//! 256-bit integers, compared with `U256` and `I256` arithmetic.

use sonatina_codegen::OptLevel;
use sonatina_ir::{I256, Immediate, Type, U256};
use wasmtime::{Func, Val};

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

type Reference = fn(Immediate, Immediate) -> Immediate;

/// The interpreter's result of a 256-bit operation.
fn interpret(op: Reference, a: U256, b: U256) -> U256 {
    op(Immediate::I256(signed(a)), Immediate::I256(signed(b)))
        .as_i256()
        .to_u256()
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
            name: "clz",
            instruction: "v10.i256 = clz v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, _| (U256::from(a.leading_zeros()), false),
        },
        Case {
            name: "ctz",
            instruction: "v10.i256 = ctz v8;",
            shape: Shape::Value,
            skip: never,
            reference: |a, _| (U256::from(a.trailing_zeros()), false),
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
            name: "uaddsat",
            instruction: "v10.i256 = uaddsat v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (interpret(Immediate::saturating_uadd, a, b), false),
        },
        Case {
            name: "usubsat",
            instruction: "v10.i256 = usubsat v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (interpret(Immediate::saturating_usub, a, b), false),
        },
        Case {
            name: "umulsat",
            instruction: "v10.i256 = umulsat v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (interpret(Immediate::saturating_umul, a, b), false),
        },
        Case {
            name: "saddsat",
            instruction: "v10.i256 = saddsat v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (interpret(Immediate::saturating_sadd, a, b), false),
        },
        Case {
            name: "ssubsat",
            instruction: "v10.i256 = ssubsat v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (interpret(Immediate::saturating_ssub, a, b), false),
        },
        Case {
            name: "smulsat",
            instruction: "v10.i256 = smulsat v8 v9;",
            shape: Shape::Value,
            skip: never,
            reference: |a, b| (interpret(Immediate::saturating_smul, a, b), false),
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
fn products_of_extended_values_match_the_reference() {
    // Values extended from 64 bits have one limb that is not zero, so their
    // product is built in place; `wide` mixes in a full value, which calls
    // the multiplication function.
    let source = format!(
        "{PRELUDE}func public %narrow(v0.i64, v1.i64) -> (i64, i64, i64, i64) {{
    block0:
        v2.i256 = zext v0 i256;
        v3.i256 = zext v1 i256;
        v4.i256 = mul v2 v3;
        (v5.i64, v6.i64, v7.i64, v8.i64) = call %unpack v4;
        return (v5, v6, v7, v8);
}}
func public %wide(v0.i64, v1.i64, v2.i64, v3.i64, v4.i64) -> (i64, i64, i64, i64) {{
    block0:
        v5.i256 = call %pack v0 v1 v2 v3;
        v6.i256 = zext v4 i256;
        v7.i256 = mul v5 v6;
        (v8.i64, v9.i64, v10.i64, v11.i64) = call %unpack v7;
        return (v8, v9, v10, v11);
}}"
    );
    let mut rng = Lcg(0x5eed_3013);
    for level in [OptLevel::O0, OptLevel::O2] {
        let mut machine = Machine::new(&build_at(&source, level));
        let (narrow, wide) = (machine.func("narrow"), machine.func("wide"));
        let result = |values: Vec<Val>| {
            let limbs: Vec<u64> = values.iter().map(|v| v.unwrap_i64() as u64).collect();
            from_limbs(&limbs)
        };
        for _ in 0..400 {
            let (a, b) = (operand(&mut rng), operand(&mut rng).low_u64());
            let low = a.low_u64();
            let got = machine.call(&narrow, &[Val::I64(low as i64), Val::I64(b as i64)]);
            let want = U256::from(low) * U256::from(b);
            assert_eq!(result(got), want, "{level:?}: {low:#x} * {b:#x}");
            let mut args: Vec<Val> = limbs(a).map(|limb| Val::I64(limb as i64)).into();
            args.push(Val::I64(b as i64));
            let want = a.overflowing_mul(U256::from(b)).0;
            assert_eq!(
                result(machine.call(&wide, &args)),
                want,
                "{level:?}: {a:#x} * {b:#x}"
            );
        }
    }
}

#[test]
fn shifts_by_a_constant_match_the_reference() {
    // A constant count is shifted in place, limb by limb, at 256 bits and at
    // 128 bits, where the low half of the wider shift is the result.
    let counts = [
        0, 1, 31, 32, 63, 64, 65, 127, 128, 129, 191, 192, 193, 255, 256, 300,
    ];
    let mut rng = Lcg(0x5eed_5417);
    let low = (U256::one() << 128) - 1;
    for (bits, left) in [(256, true), (256, false), (128, true), (128, false)] {
        let op = if left { "shl" } else { "shr" };
        let mut source = PRELUDE.to_string();
        for count in counts {
            let shift = if bits == 256 {
                format!("v9.i256 = {op} {count}.i256 v8;")
            } else {
                format!(
                    "v20.i128 = trunc v8 i128;
        v21.i128 = {op} {count}.i128 v20;
        v9.i256 = zext v21 i256;"
                )
            };
            source += &format!(
                "func public %by{count}(v0.i64, v1.i64, v2.i64, v3.i64) -> (i64, i64, i64, i64) {{
    block0:
        v8.i256 = call %pack v0 v1 v2 v3;
        {shift}
        (v11.i64, v12.i64, v13.i64, v14.i64) = call %unpack v9;
        return (v11, v12, v13, v14);
}}
"
            );
        }
        for level in [OptLevel::O0, OptLevel::O2] {
            let mut machine = Machine::new(&build_at(&source, level));
            for count in counts {
                let f = machine.func(&format!("by{count}"));
                for _ in 0..40 {
                    let a = operand(&mut rng);
                    let value = if bits == 256 { a } else { a & low };
                    let want = match (count < bits, left) {
                        (false, _) => U256::zero(),
                        (true, true) => value << count,
                        (true, false) => value >> count,
                    };
                    let want = if bits == 256 { want } else { want & low };
                    let args: Vec<Val> = limbs(a).map(|limb| Val::I64(limb as i64)).into();
                    let got: Vec<u64> = machine
                        .call(&f, &args)
                        .iter()
                        .map(|v| v.unwrap_i64() as u64)
                        .collect();
                    assert_eq!(
                        from_limbs(&got),
                        want,
                        "{level:?}: i{bits} {op} {count} of {a:#x}"
                    );
                }
            }
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

#[test]
fn a_dividend_below_the_divisor_is_the_remainder() {
    let source = format!(
        "{PRELUDE}func public %f(v0.i64, v1.i64, v2.i64, v3.i64, v4.i64, v5.i64, v6.i64, v7.i64) -> (i64, i64, i64, i64, i64, i64, i64, i64) {{
    block0:
        v8.i256 = call %pack v0 v1 v2 v3;
        v9.i256 = call %pack v4 v5 v6 v7;
        v10.i256 = udiv v8 v9;
        v11.i256 = umod v8 v9;
        (v12.i64, v13.i64, v14.i64, v15.i64) = call %unpack v10;
        (v16.i64, v17.i64, v18.i64, v19.i64) = call %unpack v11;
        return (v12, v13, v14, v15, v16, v17, v18, v19);
}}"
    );
    let big = U256::one() << 200;
    // Below the divisor, equal to it and just above it, with operands that
    // do not fit in 64 bits.
    let pairs = [
        (big, big + 1),
        (big - 1, big),
        (U256::MAX - 1, U256::MAX),
        (U256::from(5), big),
        (U256::from(u64::MAX), U256::one() << 64),
        (big, big),
        (big + 1, big),
        (U256::MAX, U256::one() << 64),
    ];
    for level in [OptLevel::O0, OptLevel::O2] {
        let mut machine = Machine::new(&build_at(&source, level));
        let f = machine.func("f");
        for (a, b) in pairs {
            let got: Vec<u64> = machine
                .call(&f, &arguments(a, b))
                .iter()
                .map(|v| v.unwrap_i64() as u64)
                .collect();
            let what = format!("{level:?} a={a:#x} b={b:#x}");
            assert_eq!(from_limbs(&got[..4]), a / b, "udiv {what}");
            assert_eq!(from_limbs(&got[4..]), a % b, "umod {what}");
        }
    }
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

/// Divisors at the boundaries of the division paths: one limb with and
/// without a top half, each number of limbs, top bits set and clear, and a
/// top limb of 2^63 over limbs of ones, whose digit estimates are too large.
fn boundary_divisors() -> Vec<U256> {
    let one = U256::one();
    let mut values = vec![one, U256::from(2), U256::from(3), U256::exp10(18)];
    for bits in [32, 63, 64, 127, 128, 191, 192, 255] {
        let power = one << bits;
        values.extend([power - 1, power, power + 1]);
    }
    values.push(U256::MAX);
    for limbs in 2..=4 {
        values.push((one << (64 * limbs - 1)) + (one << (64 * (limbs - 1))) - 1);
    }
    values
}

/// Dividends around `divisor`, around its multiples by whole limbs, and with
/// each number of limbs: the top limb full, its top bit alone and its low bit
/// alone.
fn boundary_dividends(divisor: U256) -> Vec<U256> {
    let one = U256::one();
    let around = |value: U256| {
        [
            value.overflowing_sub(one).0,
            value,
            value.overflowing_add(one).0,
        ]
    };
    let mut values = vec![U256::zero(), U256::MAX, U256::MAX - divisor];
    values.extend(around(divisor));
    for limbs in 1..=4 {
        let (top, low) = (one << (64 * limbs - 1), one << (64 * (limbs - 1)));
        values.extend([top - 1, top, top + low - 1, low, low + 1]);
    }
    for shift in [64, 128, 192] {
        let multiple = divisor << shift;
        if !multiple.is_zero() {
            values.extend(around(multiple));
        }
    }
    values
}

/// Dividends and divisors, limbs least significant first, that take the
/// corrections the boundary values do not. A reciprocal's digit is one or two
/// too large in its 64-bit division, a digit from the reciprocal is one too
/// small, and a digit of a four-limb divisor is two too large.
const CORRECTIONS: [([u64; 4], [u64; 4]); 11] = [
    // One-limb divisors: the reciprocal's digit one and two too large, and
    // the digit one too small.
    ([1 << 63, 0x7f, 0, 0], [0x0869_76fa_fb17_ff72, 0, 0, 0]),
    (
        [
            u64::MAX,
            u64::MAX,
            0x0000_000c_5617_6cc7,
            0x4bca_5383_6843_83c7,
        ],
        [0x214a_dd5c_fd1c_fa70, 0, 0, 0],
    ),
    (
        [u64::MAX >> 1, u64::MAX >> 1, 0, 0],
        [0x0455_4a0d_4be2, 0, 0, 0],
    ),
    // Longer divisors: the same corrections.
    (
        [u64::MAX, u64::MAX >> 1, 0, 0],
        [1 << 63, 0x1f83_cce4_5314_83bb, 0, 0],
    ),
    (
        [0x1af2_2353_ecfb, 0, 0x1c72_a2a6_ddd7_0e78, 0x0001_960f_d2b9],
        [1 << 42, u64::MAX, 0x02d4, 0],
    ),
    (
        [u64::MAX >> 1, u64::MAX >> 2, 0x001f_ffff_ffff, 0],
        [1 << 63, 1 << 33, 0, 0],
    ),
    ([1 << 63, u64::MAX, u64::MAX, 0], [0x003f_ffff, 0x40, 1, 0]),
    (
        [0, u64::MAX, u64::MAX, u64::MAX >> 1],
        [0x0001_a6d7_29e6, 0x0001_dd3c, 0x0200_0000, 0x40],
    ),
    // A four-limb divisor's digit two too large.
    (
        [u64::MAX >> 1, 0x1f, 1 << 41, u64::MAX],
        [u64::MAX >> 1, u64::MAX, 0x0fff_ffff, 1],
    ),
    // Knuth's cases for the step that adds the divisor back, at 64-bit digits.
    ([0, u64::MAX - 1, 1 << 63, 0], [u64::MAX, 1 << 63, 0, 0]),
    ([3, 0, 1 << 63, 0], [1, 0, 1 << 61, 0]),
];

/// Factors and moduli, limbs least significant first, whose products take
/// the corrections the boundary values do not. For a modulus of one limb and
/// of three, a reciprocal's digit is one or two too large. For a modulus of
/// two, three and four limbs, a digit from the reciprocal is one too small.
const MODULAR_CORRECTIONS: [[[u64; 4]; 3]; 6] = [
    [
        [0x6505_0aca_ed42_0d73, 0x1fff_ffff, 0, 0],
        [0x2aa4_102c, 0x0001_ffff_ffff, 0, 0],
        [0x8516_5e1f_f89b_d2bc, 0, 0, 0],
    ],
    [
        [u64::MAX >> 1, 0x0377_d62c_cc8d, 0x1fff_ffff_ffff, 0],
        [u64::MAX, 0, 0, 0],
        [0xdc62_0d88_0d9b_f7b1, u64::MAX, 0x024d_47bc, 0],
    ],
    [
        [0xec, 0, 0, 0],
        [u64::MAX >> 1, 0x03d6_cc98_53a7, u64::MAX, 0],
        [1 << 63, u64::MAX >> 1, 1 << 27, 0],
    ],
    [
        [u64::MAX, 0x3c63_bff9_4b0d_7f01, 0, 0],
        [1 << 38, 0, 0, 0],
        [1 << 61, 1 << 23, 0, 0],
    ],
    [
        [0x0001_ffff_ffff, 1 << 43, 0, u64::MAX],
        [0xc067_7ac4_e994_7bda, u64::MAX >> 1, 1 << 63, u64::MAX >> 1],
        [1 << 63, 0x78ae_d28d_c24c_dcee, 0x916f_940f_2167_eb5d, 0],
    ],
    [
        [0, u64::MAX, 0x0007_ffff, 0],
        [0, 1 << 51, u64::MAX, u64::MAX >> 1],
        [1 << 63, 1 << 63, 1 << 63, 0x45e8_9e03_98db_453f],
    ],
];

/// A value of up to four limbs, each a boundary pattern or random. Such
/// operands take the corrections of long division far more often than uniform
/// ones.
fn patterned(rng: &mut Lcg) -> U256 {
    let mut limbs = [0u64; 4];
    let count = (rng.next() % 5) as usize;
    for limb in &mut limbs[..count] {
        let bit = 1u64 << (rng.next() % 64);
        *limb = match rng.next() % 8 {
            0 => 0,
            1 => u64::MAX,
            2 => 1 << 63,
            3 => u64::MAX >> 1,
            4 => bit,
            5 => bit - 1,
            6 => rng.next() >> (rng.next() % 64),
            _ => rng.next(),
        };
    }
    from_limbs(&limbs)
}

/// A module that divides and reduces values of `ty`, an instance of it, and
/// the reference results. The operands are the low bits of 256-bit values and
/// the results are zero-extended.
struct Divider {
    machine: Machine,
    divide: Func,
    modular: Func,
    ty: Type,
    level: OptLevel,
}

impl Divider {
    fn new(ty: Type, level: OptLevel) -> Self {
        let (name, narrow, widen) = match ty {
            Type::I128 => (
                "i128",
                "v1.i128 = trunc v0 i128;\n        return v1;",
                "v1.i256 = zext v0 i256;\n        (v2.i64, v3.i64, v4.i64, v5.i64) = call %unpack v1;",
            ),
            _ => (
                "i256",
                "return v0;",
                "(v2.i64, v3.i64, v4.i64, v5.i64) = call %unpack v0;",
            ),
        };
        let source = format!(
            "{PRELUDE}func private %narrow(v0.i256) -> {name} {{
    block0:
        {narrow}
}}
func private %out(v0.{name}) -> (i64, i64, i64, i64) {{
    block0:
        {widen}
        return (v2, v3, v4, v5);
}}
func public %divide(v0.i64, v1.i64, v2.i64, v3.i64, v4.i64, v5.i64, v6.i64, v7.i64) -> (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) {{
    block0:
        v8.i256 = call %pack v0 v1 v2 v3;
        v9.i256 = call %pack v4 v5 v6 v7;
        v10.{name} = call %narrow v8;
        v11.{name} = call %narrow v9;
        v12.{name} = udiv v10 v11;
        v13.{name} = umod v10 v11;
        v14.{name} = sdiv v10 v11;
        v15.{name} = smod v10 v11;
        (v16.i64, v17.i64, v18.i64, v19.i64) = call %out v12;
        (v20.i64, v21.i64, v22.i64, v23.i64) = call %out v13;
        (v24.i64, v25.i64, v26.i64, v27.i64) = call %out v14;
        (v28.i64, v29.i64, v30.i64, v31.i64) = call %out v15;
        return (v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31);
}}
func public %modular(v0.i64, v1.i64, v2.i64, v3.i64, v4.i64, v5.i64, v6.i64, v7.i64, v8.i64, v9.i64, v10.i64, v11.i64) -> (i64, i64, i64, i64, i64, i64, i64, i64) {{
    block0:
        v12.i256 = call %pack v0 v1 v2 v3;
        v13.i256 = call %pack v4 v5 v6 v7;
        v14.i256 = call %pack v8 v9 v10 v11;
        v15.{name} = call %narrow v12;
        v16.{name} = call %narrow v13;
        v17.{name} = call %narrow v14;
        v18.{name} = evm_add_mod v15 v16 v17;
        v19.{name} = evm_mul_mod v15 v16 v17;
        (v20.i64, v21.i64, v22.i64, v23.i64) = call %out v18;
        (v24.i64, v25.i64, v26.i64, v27.i64) = call %out v19;
        return (v20, v21, v22, v23, v24, v25, v26, v27);
}}"
        );
        let mut machine = Machine::new(&build_at(&source, level));
        let (divide, modular) = (machine.func("divide"), machine.func("modular"));
        Self {
            machine,
            divide,
            modular,
            ty,
            level,
        }
    }

    fn immediate(&self, value: U256) -> Immediate {
        Immediate::from_i256(signed(value), self.ty)
    }

    fn call(&mut self, func: Func, operands: &[U256]) -> Vec<U256> {
        let arguments: Vec<Val> = operands
            .iter()
            .flat_map(|&operand| limbs(operand))
            .map(|limb| Val::I64(limb as i64))
            .collect();
        let limbs: Vec<u64> = self
            .machine
            .call(&func, &arguments)
            .iter()
            .map(|value| value.unwrap_i64() as u64)
            .collect();
        limbs.chunks(4).map(from_limbs).collect()
    }

    /// `udiv`, `umod`, `sdiv` and `smod`, unless the divisor is zero.
    fn division(&mut self, a: U256, b: U256) {
        let (x, y) = (self.immediate(a), self.immediate(b));
        if y.is_zero() {
            return;
        }
        let got = self.call(self.divide, &[a, b]);
        let references: [(&str, Reference); 4] = [
            ("udiv", Immediate::udiv),
            ("umod", Immediate::urem),
            ("sdiv", Immediate::sdiv),
            ("smod", Immediate::srem),
        ];
        for ((name, reference), got) in references.into_iter().zip(got) {
            let want = reference(x, y).zext(Type::I256).as_i256().to_u256();
            let (ty, level) = (self.ty, self.level);
            assert_eq!(got, want, "{name} {ty:?} {level:?} a={a:#x} b={b:#x}");
        }
    }

    /// `evm_add_mod` and `evm_mul_mod`.
    fn modular(&mut self, a: U256, b: U256, n: U256) {
        let got = self.call(self.modular, &[a, b, n]);
        let [x, y, m] =
            [a, b, n].map(|value| self.immediate(value).zext(Type::I256).as_i256().to_u256());
        for (product, got) in [false, true].into_iter().zip(got) {
            let name = if product { "mulmod" } else { "addmod" };
            let (ty, level) = (self.ty, self.level);
            assert_eq!(
                got,
                modular_reference(product, x, y, m),
                "{name} {ty:?} {level:?} a={a:#x} b={b:#x} n={n:#x}"
            );
        }
    }
}

fn dividers() -> impl Iterator<Item = Divider> {
    [Type::I256, Type::I128]
        .into_iter()
        .flat_map(|ty| [OptLevel::O0, OptLevel::O2].map(|level| Divider::new(ty, level)))
}

#[test]
fn division_matches_the_reference_at_the_boundaries_of_its_paths() {
    for mut divider in dividers() {
        for divisor in boundary_divisors() {
            for dividend in boundary_dividends(divisor) {
                divider.division(dividend, divisor);
                // Signed division divides the magnitudes.
                divider.division(negate(dividend), divisor);
                divider.division(dividend, negate(divisor));
            }
        }
        for (dividend, divisor) in CORRECTIONS {
            divider.division(from_limbs(&dividend), from_limbs(&divisor));
        }
    }
}

#[test]
fn division_matches_the_reference_for_operands_of_mixed_lengths() {
    let mut rng = Lcg(0x5eed_d1f1);
    for mut divider in dividers() {
        for round in 0..3000 {
            let (a, mut b) = if round % 2 == 0 {
                (patterned(&mut rng), patterned(&mut rng))
            } else {
                (operand(&mut rng), operand(&mut rng))
            };
            if round % 16 == 0 {
                // A divisor next to the dividend.
                b = a.overflowing_add(U256::from(rng.next() % 3)).0;
            }
            divider.division(a, b);
        }
    }
}

#[test]
fn addmod_and_mulmod_match_the_reference_at_the_boundaries_and_for_mixed_lengths() {
    let mut rng = Lcg(0x5eed_30d5);
    let one = U256::one();
    for mut divider in dividers() {
        for n in boundary_divisors().into_iter().chain([U256::zero()]) {
            let operands = [
                U256::zero(),
                one,
                n.overflowing_sub(one).0,
                n,
                n.overflowing_add(one).0,
                U256::MAX - n,
                U256::MAX,
                one << 255,
                (one << 128) + 1,
                U256::from(u64::MAX),
            ];
            for a in operands {
                for b in operands {
                    divider.modular(a, b, n);
                }
            }
        }
        for [a, b, n] in MODULAR_CORRECTIONS {
            divider.modular(from_limbs(&a), from_limbs(&b), from_limbs(&n));
        }
        for round in 0..2000 {
            let (a, b, n) = if round % 2 == 0 {
                (
                    patterned(&mut rng),
                    patterned(&mut rng),
                    patterned(&mut rng),
                )
            } else {
                (operand(&mut rng), operand(&mut rng), modulus(&mut rng))
            };
            divider.modular(a, b, n);
        }
    }
}
