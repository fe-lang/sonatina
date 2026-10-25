//! Differential tests of native i256 operations against `U256`/`U512`
//! reference arithmetic.

use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};
use sonatina_ir::U256;

use super::parse_verified_native_module;

type Apply = unsafe extern "C" fn(*const u8, *const u8, *const u8, *mut u8) -> u8;

/// A value from its 64-bit limbs, least significant first.
fn word(limbs: [u64; 4]) -> U256 {
    limbs.iter().rev().fold(U256::zero(), |value, &limb| {
        (value << 64) | U256::from(limb)
    })
}

fn signed_min() -> U256 {
    U256::one() << 255
}

fn negative(value: U256) -> bool {
    value.bit(255)
}

fn neg(value: U256) -> U256 {
    value.overflowing_neg().0
}

fn abs(value: U256) -> U256 {
    if negative(value) { neg(value) } else { value }
}

fn signed_lt(lhs: U256, rhs: U256) -> bool {
    (lhs ^ signed_min()) < (rhs ^ signed_min())
}

/// Operands that cross every limb and carry boundary, signed extremes, and
/// deterministic random values of one to four significant limbs.
fn operands() -> Vec<U256> {
    let mut values = vec![
        U256::zero(),
        U256::one(),
        U256::from(2),
        U256::from(3),
        U256::from(7),
        U256::MAX,
        U256::MAX - 1,
        U256::MAX - 6,
        signed_min(),
        signed_min() - 1,
        signed_min() + 1,
        word([u64::MAX, u64::MAX, u64::MAX, 0]),
        word([0, u64::MAX, 0, u64::MAX]),
        word([u64::MAX, 0, u64::MAX, 0]),
        word([1, 0, 0, 1]),
        word([0, 0, 1, 0]),
        word([u64::MAX, u64::MAX, 0, 0]),
    ];
    for bit in [63, 64, 65, 127, 128, 129, 191, 192, 193, 254] {
        let power = U256::one() << bit;
        values.extend([power - 1, power, power + 1]);
    }
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for limbs in 1..=4 {
        for _ in 0..5 {
            let mut limbs_of_value = [0u64; 4];
            for limb in &mut limbs_of_value[..limbs] {
                *limb = next();
            }
            values.push(word(limbs_of_value));
        }
    }
    values
}

fn shift_amounts() -> Vec<U256> {
    let mut amounts: Vec<U256> = [
        0u64, 1, 7, 13, 63, 64, 65, 100, 127, 128, 129, 191, 192, 193, 254, 255, 256, 257, 300,
    ]
    .into_iter()
    .map(U256::from)
    .collect();
    amounts.extend([
        U256::from(u64::MAX),
        U256::one() << 64,
        (U256::one() << 64) + 7,
        U256::one() << 128,
        U256::one() << 255,
        U256::MAX,
    ]);
    amounts
}

fn bytes(value: U256) -> [u8; 32] {
    value.to_little_endian()
}

fn compile(body: &str, level: OptLevel) -> sonatina_codegen::isa::cranelift::CraneliftJitArtifact {
    let source = format!(
        "func public %apply(v0.*i256, v1.*i256, v2.*i256, v3.*i256) -> i8 {{
block0:
    v4.i256 = mload v0 i256;
    v5.i256 = mload v1 i256;
    v6.i256 = mload v2 i256;
{body}
}}
"
    );
    Compile::new(
        parse_verified_native_module(&source),
        CraneliftJitBackend::new(),
    )
    .with_opt_level(level)
    .compile()
    .unwrap_or_else(|errors| panic!("{body}\n{errors:?}"))
}

/// Runs `body` on every `(a, b, c)` case and compares its stored result
/// and returned flag with `expected`.
fn check(body: &str, cases: &[[U256; 3]], expected: impl Fn([U256; 3]) -> (U256, bool)) {
    check_at(&[OptLevel::O0, OptLevel::O2], body, cases, expected);
}

fn check_at(
    levels: &[OptLevel],
    body: &str,
    cases: &[[U256; 3]],
    expected: impl Fn([U256; 3]) -> (U256, bool),
) {
    for &level in levels {
        let artifact = compile(body, level);
        let apply: Apply =
            unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
        for &case in cases {
            let [a, b, c] = case.map(bytes);
            let mut result = [0xa5u8; 32];
            let flag = unsafe { apply(a.as_ptr(), b.as_ptr(), c.as_ptr(), result.as_mut_ptr()) };
            let (value, expected_flag) = expected(case);
            assert_eq!(
                U256::from_little_endian(&result),
                value,
                "{body}\n{level:?} {case:x?}"
            );
            assert_eq!(flag, u8::from(expected_flag), "{body}\n{level:?} {case:x?}");
        }
    }
}

fn pairs(lhs: &[U256], rhs: &[U256]) -> Vec<[U256; 3]> {
    lhs.iter()
        .flat_map(|&a| rhs.iter().map(move |&b| [a, b, U256::zero()]))
        .collect()
}

fn binary(op: &str) -> String {
    format!("    v7.i256 = {op} v4 v5;\n    mstore v3 v7 i256;\n    return 0.i8;")
}

fn flag(op: &str) -> String {
    format!(
        "    v7.i1 = {op} v4 v5;\n    mstore v3 0.i256 i256;\n    v8.i8 = zext v7 i8;\n    return v8;"
    )
}

fn overflowing(op: &str) -> String {
    format!(
        "    (v7.i256, v8.i1) = {op} v4 v5;\n    mstore v3 v7 i256;\n    v9.i8 = zext v8 i8;\n    return v9;"
    )
}

#[test]
fn i256_arithmetic_matches_reference() {
    let values = operands();
    let cases = pairs(&values, &values);
    check(&binary("add"), &cases, |[a, b, _]| {
        (a.overflowing_add(b).0, false)
    });
    check(&binary("sub"), &cases, |[a, b, _]| {
        (a.overflowing_sub(b).0, false)
    });
    check(&binary("mul"), &cases, |[a, b, _]| {
        (a.overflowing_mul(b).0, false)
    });
    check(&binary("and"), &cases, |[a, b, _]| (a & b, false));
    check(&binary("or"), &cases, |[a, b, _]| (a | b, false));
    check(&binary("xor"), &cases, |[a, b, _]| (a ^ b, false));
    let unary =
        |op: &str| format!("    v7.i256 = {op} v4;\n    mstore v3 v7 i256;\n    return 0.i8;");
    check(&unary("neg"), &cases, |[a, _, _]| (neg(a), false));
    check(&unary("not"), &cases, |[a, _, _]| (!a, false));
    check(&unary("bswap"), &cases, |[a, _, _]| {
        (U256::from_big_endian(&a.to_little_endian()), false)
    });
}

#[test]
fn i256_comparisons_match_reference() {
    let values = operands();
    let cases = pairs(&values, &values);
    let compare = |op: &str, expected: fn(U256, U256) -> bool| {
        check(&flag(op), &cases, |[a, b, _]| {
            (U256::zero(), expected(a, b))
        });
    };
    compare("eq", |a, b| a == b);
    compare("ne", |a, b| a != b);
    compare("lt", |a, b| a < b);
    compare("gt", |a, b| a > b);
    compare("le", |a, b| a <= b);
    compare("ge", |a, b| a >= b);
    compare("slt", signed_lt);
    compare("sgt", |a, b| signed_lt(b, a));
    compare("sle", |a, b| !signed_lt(b, a));
    compare("sge", |a, b| !signed_lt(a, b));
    check(
        "    v7.i1 = is_zero v4;\n    mstore v3 0.i256 i256;\n    v8.i8 = zext v7 i8;\n    return v8;",
        &cases,
        |[a, _, _]| (U256::zero(), a.is_zero()),
    );
}

/// The wrapping signed product, whether the exact product is negative, and
/// whether it overflows.
fn signed_product(a: U256, b: U256) -> (U256, bool, bool) {
    let (magnitude, wide) = abs(a).overflowing_mul(abs(b));
    let negative = negative(a) != negative(b);
    let overflow = wide
        || if negative {
            magnitude > signed_min()
        } else {
            magnitude >= signed_min()
        };
    let product = if negative { neg(magnitude) } else { magnitude };
    (product, negative, overflow)
}

#[test]
fn i256_overflow_and_saturating_ops_match_reference() {
    let values = operands();
    let cases = pairs(&values, &values);
    let sadd_overflow = |a: U256, b: U256| {
        let sum = a.overflowing_add(b).0;
        negative(a) == negative(b) && negative(sum) != negative(a)
    };
    let ssub_overflow = |a: U256, b: U256| {
        let difference = a.overflowing_sub(b).0;
        negative(a) != negative(b) && negative(difference) != negative(a)
    };
    let bound = |negative: bool| {
        if negative {
            signed_min()
        } else {
            signed_min() - 1
        }
    };
    check(&overflowing("uaddo"), &cases, |[a, b, _]| {
        a.overflowing_add(b)
    });
    check(&overflowing("usubo"), &cases, |[a, b, _]| {
        a.overflowing_sub(b)
    });
    check(&overflowing("umulo"), &cases, |[a, b, _]| {
        a.overflowing_mul(b)
    });
    check(&overflowing("saddo"), &cases, |[a, b, _]| {
        (a.overflowing_add(b).0, sadd_overflow(a, b))
    });
    check(&overflowing("ssubo"), &cases, |[a, b, _]| {
        (a.overflowing_sub(b).0, ssub_overflow(a, b))
    });
    check(&overflowing("smulo"), &cases, |[a, b, _]| {
        let (product, _, overflow) = signed_product(a, b);
        (product, overflow)
    });
    check(
        "    (v7.i256, v8.i1) = snego v4;\n    mstore v3 v7 i256;\n    v9.i8 = zext v8 i8;\n    return v9;",
        &cases,
        |[a, _, _]| (neg(a), a == signed_min()),
    );
    check(&binary("uaddsat"), &cases, |[a, b, _]| {
        (a.checked_add(b).unwrap_or(U256::MAX), false)
    });
    check(&binary("usubsat"), &cases, |[a, b, _]| {
        (a.checked_sub(b).unwrap_or_default(), false)
    });
    check(&binary("umulsat"), &cases, |[a, b, _]| {
        (a.checked_mul(b).unwrap_or(U256::MAX), false)
    });
    check(&binary("saddsat"), &cases, |[a, b, _]| {
        let sum = a.overflowing_add(b).0;
        (
            if sadd_overflow(a, b) {
                bound(negative(a))
            } else {
                sum
            },
            false,
        )
    });
    check(&binary("ssubsat"), &cases, |[a, b, _]| {
        let difference = a.overflowing_sub(b).0;
        (
            if ssub_overflow(a, b) {
                bound(negative(a))
            } else {
                difference
            },
            false,
        )
    });
    check(&binary("smulsat"), &cases, |[a, b, _]| {
        let (product, negative, overflow) = signed_product(a, b);
        (if overflow { bound(negative) } else { product }, false)
    });
}

fn shifted(op: &str, value: U256, amount: U256) -> U256 {
    let fill = if op == "sar" && negative(value) {
        U256::MAX
    } else {
        U256::zero()
    };
    if amount >= U256::from(256) {
        return fill;
    }
    let amount = amount.as_usize();
    match op {
        "shl" => value << amount,
        "shr" => value >> amount,
        "sar" if negative(value) => !(!value >> amount),
        "sar" => value >> amount,
        _ => unreachable!(),
    }
}

#[test]
fn i256_shifts_match_reference_for_variable_and_constant_amounts() {
    let values = operands();
    let amounts = shift_amounts();
    for op in ["shl", "shr", "sar"] {
        check(
            &format!("    v7.i256 = {op} v5 v4;\n    mstore v3 v7 i256;\n    return 0.i8;"),
            &pairs(&values, &amounts),
            |[value, amount, _]| (shifted(op, value, amount), false),
        );
        for &amount in &amounts {
            // The optimizer's demanded-bits analysis panics on constant
            // shift amounts above `u64::MAX`, so those run unoptimized.
            let levels: &[OptLevel] = if amount > U256::from(u64::MAX) {
                &[OptLevel::O0]
            } else {
                &[OptLevel::O0, OptLevel::O2]
            };
            check_at(
                levels,
                &format!(
                    "    v7.i256 = {op} 0x{amount:x}.i256 v4;\n    mstore v3 v7 i256;\n    return 0.i8;"
                ),
                &pairs(&values, &[U256::zero()]),
                |[value, _, _]| (shifted(op, value, amount), false),
            );
        }
    }
}

/// Division by zero is undefined in the IR; the native lowering gives an
/// all-ones quotient and the dividend as the remainder.
fn divided(op: &str, a: U256, b: U256) -> U256 {
    let (quotient, remainder) = if b.is_zero() {
        (U256::MAX, abs_if(op, a))
    } else {
        let (lhs, rhs) = if op.starts_with('s') {
            (abs(a), abs(b))
        } else {
            (a, b)
        };
        (lhs / rhs, lhs % rhs)
    };
    match op {
        "udiv" => quotient,
        "umod" => remainder,
        "sdiv" if negative(a) != negative(b) => neg(quotient),
        "sdiv" => quotient,
        "smod" if negative(a) => neg(remainder),
        "smod" => remainder,
        _ => unreachable!(),
    }
}

fn abs_if(op: &str, value: U256) -> U256 {
    if op.starts_with('s') {
        abs(value)
    } else {
        value
    }
}

#[test]
fn i256_division_matches_reference() {
    let mut values = operands();
    // Divisors of every limb count and numerators just above them.
    values.extend([
        word([0x8000_0000_0000_0000, 0, 0, 0]),
        word([0, 0x8000_0000_0000_0000, 0, 0]),
        word([u64::MAX, 0x7fff_ffff_ffff_ffff, 0, 0]),
        word([1, 0, 0x8000_0000_0000_0000, 0]),
        word([0, 0, 0, 0x8000_0000_0000_0001]),
        word([u64::MAX, u64::MAX, u64::MAX, 1]),
        word([0, 0, 1, 1]),
    ]);
    let cases = pairs(&values, &values);
    for op in ["udiv", "umod", "sdiv", "smod"] {
        check(&binary(op), &cases, |[a, b, _]| (divided(op, a, b), false));
    }
}

#[test]
fn i256_values_cross_calls_and_loop_phis() {
    // `forward` passes its incoming arguments on swapped and one of them
    // twice; the loop rotates two i256 phis through a call per iteration.
    let source = r#"
func inline(never) private %combine(v0.i256, v1.i256, v2.i256) -> i256 {
block0:
    v3.i256 = sub v0 v1;
    v4.i256 = mul v3 v2;
    return v4;
}
func inline(never) private %forward(v0.i256, v1.i256) -> i256 {
block0:
    v2.i256 = call %combine v1 v0 v0;
    v3.i256 = call %combine v2 v1 3.i256;
    return v3;
}
func public %apply(v0.*i256, v1.*i256, v2.*i256, v3.*i256) -> i8 {
block0:
    v4.i256 = mload v0 i256;
    v5.i256 = mload v1 i256;
    v6.i256 = mload v2 i256;
    v7.i256 = call %forward v4 v5;
    jump block1;
block1:
    v10.i256 = phi (v7 block0) (v12 block1);
    v11.i256 = phi (v6 block0) (v10 block1);
    v13.i64 = phi (0.i64 block0) (v14 block1);
    v12.i256 = call %combine v10 v11 undef.i256;
    v15.i256 = add v12 v11;
    v14.i64 = add v13 1.i64;
    v16.i1 = lt v14 5.i64;
    br v16 block1 block2;
block2:
    v17.i256 = add v15 v10;
    mstore v3 v17 i256;
    return 0.i8;
}
"#;
    let combine = |a: U256, b: U256, c: U256| a.overflowing_sub(b).0.overflowing_mul(c).0;
    let values = operands();
    let cases: Vec<_> = values
        .iter()
        .zip(values.iter().rev())
        .zip(values.iter().skip(7).cycle())
        .map(|((&a, &b), &c)| [a, b, c])
        .collect();
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let apply: Apply =
            unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
        for &[a, b, c] in &cases {
            let first = combine(b, a, a);
            let (mut current, mut previous) = (combine(first, b, U256::from(3)), c);
            let mut sum = U256::zero();
            for _ in 0..5 {
                // Undef reads as zero.
                let next = combine(current, previous, U256::zero());
                sum = next.overflowing_add(previous).0;
                (current, previous) = (next, current);
            }
            let expected = sum.overflowing_add(previous).0;
            let [a_bytes, b_bytes, c_bytes] = [a, b, c].map(bytes);
            let mut result = [0u8; 32];
            unsafe {
                apply(
                    a_bytes.as_ptr(),
                    b_bytes.as_ptr(),
                    c_bytes.as_ptr(),
                    result.as_mut_ptr(),
                )
            };
            assert_eq!(
                U256::from_little_endian(&result),
                expected,
                "{level:?} {a:x} {b:x} {c:x}"
            );
        }
    }
}
