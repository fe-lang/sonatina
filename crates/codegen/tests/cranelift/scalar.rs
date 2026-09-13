#[cfg(unix)]
use std::{env, os::unix::process::ExitStatusExt, process::Command};

use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};
use sonatina_ir::{I256, Immediate, Type, U256};

use super::parse_verified_native_module;

fn check_scalar_cases(op: &str, ty: Type, cases: &[(Immediate, Immediate, Immediate, bool)]) {
    let ty_name = format!("{ty:?}").to_lowercase();
    let overflow_op = matches!(
        op,
        "uaddo" | "saddo" | "usubo" | "ssubo" | "umulo" | "smulo" | "snego"
    );
    let result_ty = if matches!(
        op,
        "eq" | "ne" | "lt" | "gt" | "le" | "ge" | "slt" | "sgt" | "sle" | "sge" | "is_zero"
    ) {
        Type::I1
    } else {
        ty
    };
    let result_name = format!("{result_ty:?}").to_lowercase();
    let expression = match op {
        "snego" => format!("(v5.{ty_name}, v6.i1) = snego v3;"),
        _ if overflow_op => format!("(v5.{ty_name}, v6.i1) = {op} v3 v4;"),
        "not" | "neg" | "is_zero" => format!("v5.{result_name} = {op} v3;"),
        "shl" | "shr" | "sar" => format!("v5.{ty_name} = {op} v4 v3;"),
        _ => format!("v5.{result_name} = {op} v3 v4;"),
    };
    let status = if overflow_op {
        "v7.i8 = zext v6 i8;\n    return v7;"
    } else {
        "return 0.i8;"
    };
    let source = format!(
        r#"func public %apply(v0.*{ty_name}, v1.*{ty_name}, v2.*{result_name}) -> i8 {{
block0:
    v3.{ty_name} = mload v0 {ty_name};
    v4.{ty_name} = mload v1 {ty_name};
    {expression}
    mstore v2 v5 {result_name};
    {status}
}}
"#
    );
    for level in [OptLevel::O0, OptLevel::O2] {
        let module = parse_verified_native_module(&source);
        let size = module.ctx.size_of(result_ty).unwrap();
        let artifact = Compile::new(module, CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .unwrap_or_else(|errors| panic!("{op} {ty_name} {level:?}: {errors:?}"));
        let apply: unsafe extern "C" fn(*const u8, *const u8, *mut u8) -> u8 =
            unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
        for &(lhs, rhs, expected, overflow) in cases {
            let lhs_bytes = lhs.zext(Type::I256).as_i256().to_u256().to_little_endian();
            let rhs_bytes = rhs.zext(Type::I256).as_i256().to_u256().to_little_endian();
            let expected_bytes = expected
                .zext(Type::I256)
                .as_i256()
                .to_u256()
                .to_little_endian();
            let mut result = [0xa5u8; 32];
            let status =
                unsafe { apply(lhs_bytes.as_ptr(), rhs_bytes.as_ptr(), result.as_mut_ptr()) };
            assert_eq!(
                &result[..size],
                &expected_bytes[..size],
                "{op} {lhs:?} {rhs:?} {level:?}"
            );
            assert_eq!(status, u8::from(overflow), "{op} {lhs:?} {rhs:?} {level:?}");
            assert!(result[size..].iter().all(|&byte| byte == 0xa5));
        }
    }
}

#[test]
fn integer_operations_match_ir_at_every_width() {
    for ty in [
        Type::I1,
        Type::I8,
        Type::I16,
        Type::I32,
        Type::I64,
        Type::I128,
        Type::I256,
    ] {
        let mut values = vec![
            Immediate::zero(ty),
            Immediate::one(ty),
            Immediate::all_one(ty),
            Immediate::signed_min(ty),
            Immediate::signed_max(ty),
        ];
        if ty != Type::I1 {
            values.extend([2, -2, 17, -17].map(|n| Immediate::from_i256(I256::from(n), ty)));
            let mut state = 0x7ab9_63d2_108e_f541u64;
            for _ in 0..8 {
                let bytes: [u8; 32] = std::array::from_fn(|_| {
                    state ^= state << 13;
                    state ^= state >> 7;
                    state ^= state << 17;
                    state as u8
                });
                values.push(Immediate::from_i256(
                    I256::from(U256::from_little_endian(&bytes)),
                    ty,
                ));
            }
        }
        for op in [
            "add", "sub", "mul", "neg", "not", "and", "or", "xor", "udiv", "sdiv", "umod", "smod",
            "eq", "ne", "lt", "gt", "le", "ge", "slt", "sgt", "sle", "sge", "is_zero", "uaddo",
            "saddo", "usubo", "ssubo", "umulo", "smulo", "snego", "uaddsat", "saddsat", "usubsat",
            "ssubsat", "umulsat", "smulsat",
        ] {
            if ty == Type::I1 && op.ends_with("sat") {
                continue;
            }
            let mut cases = Vec::new();
            for &lhs in &values {
                for &rhs in &values {
                    if matches!(op, "udiv" | "sdiv" | "umod" | "smod") && rhs.is_zero() {
                        continue;
                    }
                    let expected = match op {
                        "uaddo" => lhs.overflowing_uadd(rhs),
                        "saddo" => lhs.overflowing_sadd(rhs),
                        "usubo" => lhs.overflowing_usub(rhs),
                        "ssubo" => lhs.overflowing_ssub(rhs),
                        "umulo" => lhs.overflowing_umul(rhs),
                        "smulo" => lhs.overflowing_smul(rhs),
                        "snego" => lhs.overflowing_sneg(),
                        _ => (
                            match op {
                                "add" => lhs + rhs,
                                "sub" => lhs - rhs,
                                "mul" => lhs * rhs,
                                "neg" => -lhs,
                                "not" => !lhs,
                                "and" => lhs & rhs,
                                "or" => lhs | rhs,
                                "xor" => lhs ^ rhs,
                                "udiv" => lhs.udiv(rhs),
                                "sdiv" => lhs.sdiv(rhs),
                                "umod" => lhs.urem(rhs),
                                "smod" => lhs.srem(rhs),
                                "eq" => lhs.imm_eq(rhs),
                                "ne" => lhs.imm_ne(rhs),
                                "lt" => lhs.lt(rhs),
                                "gt" => lhs.gt(rhs),
                                "le" => lhs.le(rhs),
                                "ge" => lhs.ge(rhs),
                                "slt" => lhs.slt(rhs),
                                "sgt" => lhs.sgt(rhs),
                                "sle" => lhs.sle(rhs),
                                "sge" => lhs.sge(rhs),
                                "is_zero" => lhs.is_zero().into(),
                                "uaddsat" => lhs.saturating_uadd(rhs),
                                "saddsat" => lhs.saturating_sadd(rhs),
                                "usubsat" => lhs.saturating_usub(rhs),
                                "ssubsat" => lhs.saturating_ssub(rhs),
                                "umulsat" => lhs.saturating_umul(rhs),
                                "smulsat" => lhs.saturating_smul(rhs),
                                _ => unreachable!(),
                            },
                            false,
                        ),
                    };
                    cases.push((lhs, rhs, expected.0, expected.1));
                }
            }
            check_scalar_cases(op, ty, &cases);
        }
    }
}

#[test]
fn boolean_producers_remain_canonical_through_calls_and_control_flow() {
    let source = r#"
func private %identity(v0.i1) -> i1 {
block0:
    return v0;
}
func public %apply(v0.*i1, v1.*i1, v2.*i1) -> i8 {
block0:
    v3.i1 = mload v0 i1;
    v4.i1 = mload v1 i1;
    v5.i1 = add v3 v4;
    v6.i1 = call %identity v5;
    v7.i1 = eq v6 0.i1;
    br v6 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v8.i1 = phi (1.i1 block1) (0.i1 block2);
    mstore v2 v6 i1;
    v9.i1 = eq v8 v6;
    v10.i8 = zext v7 i8;
    v11.i8 = zext v9 i8;
    v12.i8 = mul v11 2.i8;
    v13.i8 = add v12 v10;
    return v13;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap();
        let apply: unsafe extern "C" fn(*const u8, *const u8, *mut u8) -> u8 =
            unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
        // Noncanonical memory bytes must be truncated to their low bit on load.
        for lhs in [0u8, 1, 2, 3, 254, 255] {
            for rhs in [0u8, 1, 2, 3, 254, 255] {
                let expected = (lhs ^ rhs) & 1;
                let mut stored = 0xa5;
                let status = unsafe { apply(&lhs, &rhs, &mut stored) };
                assert_eq!(stored, expected, "{lhs} {rhs} {level:?}");
                assert_eq!(status, 2 + (1 - expected), "{lhs} {rhs} {level:?}");
            }
        }
    }
}

#[test]
fn boolean_not_preserves_one_bit() {
    check_scalar_cases(
        "not",
        Type::I1,
        &[
            (false.into(), false.into(), true.into(), false),
            (true.into(), false.into(), false.into(), false),
        ],
    );
}

#[test]
fn scalar_shifts_preserve_overshift_semantics() {
    for (ty, width) in [
        (Type::I1, 1),
        (Type::I8, 8),
        (Type::I16, 16),
        (Type::I32, 32),
        (Type::I64, 64),
        (Type::I128, 128),
    ] {
        for op in ["shl", "shr", "sar"] {
            let mut cases = Vec::new();
            let counts = if ty == Type::I1 {
                vec![U256::zero(), U256::one()]
            } else {
                vec![
                    U256::zero(),
                    U256::from(width - 1),
                    U256::from(width),
                    U256::from(width + 1),
                    U256::from(255u16),
                ]
            };
            for lhs in [
                Immediate::zero(ty),
                Immediate::one(ty),
                Immediate::signed_min(ty),
                Immediate::all_one(ty),
            ] {
                for &count in &counts {
                    let rhs = Immediate::from_i256(I256::from(count), ty);
                    let expected = match op {
                        "shl" if count >= U256::from(width) => Immediate::zero(ty),
                        "shl" => lhs << rhs,
                        "shr" => lhs.lshr(rhs),
                        "sar" => lhs.ashr(rhs),
                        _ => unreachable!(),
                    };
                    cases.push((lhs, rhs, expected, false));
                }
                if ty == Type::I128 {
                    let rhs = Immediate::I128(1 << 64);
                    let expected = if op == "sar" {
                        lhs.ashr(rhs)
                    } else {
                        Immediate::zero(ty)
                    };
                    cases.push((lhs, rhs, expected, false));
                }
            }
            check_scalar_cases(op, ty, &cases);
        }
    }
}

#[test]
fn scalar_signed_division_wraps_overflow() {
    for ty in [Type::I8, Type::I16, Type::I32, Type::I64, Type::I128] {
        let min = Immediate::signed_min(ty);
        let minus_one = Immediate::all_one(ty);
        let cases = [
            (min, minus_one),
            (min, Immediate::one(ty)),
            (minus_one, minus_one),
            (
                Immediate::from_i256(I256::from(-17), ty),
                Immediate::from_i256(I256::from(3), ty),
            ),
        ]
        .map(|(lhs, rhs)| (lhs, rhs, lhs.sdiv(rhs), false));
        check_scalar_cases("sdiv", ty, &cases);
    }
}

#[test]
fn signed_i128_edge_operations_compile_and_execute() {
    let values = [
        i128::MIN,
        i128::MIN + 1,
        -(1 << 96),
        -(1 << 64),
        -3,
        -1,
        0,
        1,
        3,
        1 << 63,
        1 << 64,
        (1 << 96) + 1,
        i128::MAX - 1,
        i128::MAX,
    ];
    for op in [
        "snego", "saddsat", "ssubsat", "smulsat", "smulo", "umulo", "umulsat", "sdiv",
    ] {
        let mut cases = Vec::new();
        for lhs in values {
            for rhs in values {
                let (expected, overflow) = match op {
                    "snego" => lhs.overflowing_neg(),
                    "saddsat" => (lhs.saturating_add(rhs), false),
                    "ssubsat" => (lhs.saturating_sub(rhs), false),
                    "smulsat" => (lhs.saturating_mul(rhs), false),
                    "smulo" => lhs.overflowing_mul(rhs),
                    "umulo" => {
                        let (value, overflow) = (lhs as u128).overflowing_mul(rhs as u128);
                        (value as i128, overflow)
                    }
                    "umulsat" => ((lhs as u128).saturating_mul(rhs as u128) as i128, false),
                    "sdiv" if rhs == 0 => continue,
                    "sdiv" => (lhs.wrapping_div(rhs), false),
                    _ => unreachable!(),
                };
                cases.push((lhs.into(), rhs.into(), expected.into(), overflow));
            }
        }
        check_scalar_cases(op, Type::I128, &cases);
    }
}

#[test]
fn i128_division_and_remainder_preserve_all_bits() {
    let mut values = vec![
        0u128,
        1,
        2,
        3,
        (1 << 63) - 1,
        1 << 63,
        (1 << 64) - 1,
        1 << 64,
        (1 << 64) + 1,
        (1 << 96) + 17,
        i128::MAX as u128,
        i128::MIN as u128,
        (i128::MIN + 1) as u128,
        u128::MAX - 1,
        u128::MAX,
    ];
    let mut state = 0x9e37_79b9_7f4a_7c15_a076_1d64_78bd_642fu128;
    values.extend((0..32).map(|_| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    }));
    for op in ["udiv", "sdiv", "umod", "smod"] {
        let mut cases = Vec::new();
        for &lhs in &values {
            for &rhs in values.iter().filter(|&&rhs| rhs != 0) {
                let expected = match op {
                    "udiv" => (lhs / rhs) as i128,
                    "umod" => (lhs % rhs) as i128,
                    "sdiv" => (lhs as i128).wrapping_div(rhs as i128),
                    "smod" => (lhs as i128).wrapping_rem(rhs as i128),
                    _ => unreachable!(),
                };
                cases.push((
                    (lhs as i128).into(),
                    (rhs as i128).into(),
                    expected.into(),
                    false,
                ));
            }
        }
        check_scalar_cases(op, Type::I128, &cases);
    }
}

#[cfg(unix)]
#[test]
fn i128_division_by_zero_traps() {
    const CHILD_CASE: &str = "SONATINA_I128_ZERO_DIVISOR_CASE";
    if let Ok(case) = env::var(CHILD_CASE) {
        let (op, level) = case.split_once(':').unwrap();
        let level = match level {
            "O0" => OptLevel::O0,
            "O2" => OptLevel::O2,
            _ => unreachable!(),
        };
        let source = format!(
            r#"func public %divide(v0.*i128, v1.*i128, v2.*i128) {{
block0:
    v3.i128 = mload v0 i128;
    v4.i128 = mload v1 i128;
    v5.i128 = {op} v3 v4;
    mstore v2 v5 i128;
    return;
}}
"#
        );
        let module = parse_verified_native_module(&source);
        let artifact = Compile::new(module, CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .expect("zero-divisor test should compile");
        let divide: unsafe extern "C" fn(*const u8, *const u8, *mut u8) =
            unsafe { std::mem::transmute(artifact.function_address("divide").unwrap()) };
        let mut result = [0u8; 16];
        unsafe {
            divide(
                1u128.to_le_bytes().as_ptr(),
                [0u8; 16].as_ptr(),
                result.as_mut_ptr(),
            )
        };
        return;
    }

    // A native trap terminates the process. Isolate it from the test runner
    // and distinguish the expected trap signal from a Rust assertion failure.
    for op in ["udiv", "sdiv", "umod", "smod"] {
        for level in [OptLevel::O0, OptLevel::O2] {
            let output = Command::new(env::current_exe().unwrap())
                .args([
                    "--exact",
                    "scalar::i128_division_by_zero_traps",
                    "--nocapture",
                ])
                .env(CHILD_CASE, format!("{op}:{level:?}"))
                .output()
                .expect("trap subprocess should run");
            assert!(
                matches!(output.status.signal(), Some(4 | 5 | 8)),
                "{op} {level:?}: expected a trap, got {}\n{}\n{}",
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
}
