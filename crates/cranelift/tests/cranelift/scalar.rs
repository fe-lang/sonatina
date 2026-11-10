#[cfg(unix)]
use std::{env, os::unix::process::ExitStatusExt, process::Command};

use sonatina_codegen::{Compile, compile::OptLevel};
use sonatina_cranelift::CraneliftJitBackend;
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
        "not" | "neg" | "bswap" | "clz" | "ctz" | "is_zero" => {
            format!("v5.{result_name} = {op} v3;")
        }
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

/// An immediate zero-extended to a word.
fn word(imm: Immediate) -> U256 {
    imm.zext(Type::I256).as_i256().to_u256()
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
            "ssubsat", "umulsat", "smulsat", "bswap", "clz", "ctz",
        ] {
            if ty == Type::I1 && (op.ends_with("sat") || op == "bswap") {
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
                                "bswap" => lhs.bswap(),
                                // Leading zeros within the type: those of the
                                // zero-extended word, less those of all ones.
                                "clz" => {
                                    let zeros = word(lhs).leading_zeros()
                                        - word(Immediate::all_one(ty)).leading_zeros();
                                    Immediate::from_i256(I256::from(zeros), ty)
                                }
                                // Trailing zeros within the type: those of the
                                // word with a set bit just above the type's.
                                "ctz" => {
                                    let stop =
                                        word(Immediate::all_one(ty)).overflowing_add(1.into()).0;
                                    let zeros = (word(lhs) | stop).trailing_zeros();
                                    Immediate::from_i256(I256::from(zeros), ty)
                                }
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
fn i128_shifts_by_constant_counts_match_ir() {
    let values = [
        Immediate::I128(0x0123_4567_89ab_cdef_fedc_ba98_7654_3210),
        Immediate::I128(-0x0123_4567_89ab_cdef_fedc_ba98_7654_3210),
        Immediate::signed_min(Type::I128),
        Immediate::all_one(Type::I128),
        Immediate::one(Type::I128),
    ];
    for op in ["shl", "shr", "sar"] {
        for count in [0u32, 1, 17, 63, 64, 65, 100, 127, 128, 200] {
            let source = format!(
                r#"func public %apply(v0.*i128, v1.*i128) {{
block0:
    v2.i128 = mload v0 i128;
    v3.i128 = {op} {count}.i128 v2;
    mstore v1 v3 i128;
    return;
}}
"#
            );
            for level in [OptLevel::O0, OptLevel::O2] {
                let artifact = Compile::new(
                    parse_verified_native_module(&source),
                    CraneliftJitBackend::new(),
                )
                .with_opt_level(level)
                .compile()
                .unwrap_or_else(|errors| panic!("{op} {count} {level:?}: {errors:?}"));
                let apply: unsafe extern "C" fn(*const i128, *mut i128) =
                    unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
                let rhs = Immediate::I128(count.into());
                for value in values {
                    let expected = match op {
                        "shl" if count >= 128 => Immediate::zero(Type::I128),
                        "shl" => value << rhs,
                        "shr" => value.lshr(rhs),
                        _ => value.ashr(rhs),
                    };
                    let Immediate::I128(input) = value else {
                        unreachable!()
                    };
                    let mut result = 0;
                    unsafe { apply(&input, &mut result) };
                    assert_eq!(
                        Immediate::I128(result),
                        expected,
                        "{op} {count} {value:?} {level:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn i128_products_with_word_operands_match_ir() {
    // Operands whose high limb is known zero, from a zero extension, a mask
    // or a choice of small constants, multiply as one limb.
    let values: [u128; 7] = [0, 1, 6, u64::MAX as u128, 1 << 64, 3 << 100, u128::MAX];
    for (op, narrow, narrowed) in [
        (
            "umulo",
            "v5.i128 = zext v4 i128;",
            (|a| a & u64::MAX as u128) as fn(u128) -> u128,
        ),
        (
            "umulo",
            "v5.i128 = and v2 18446744073709551615.i128;",
            |a| a & u64::MAX as u128,
        ),
        ("umulo", "v5.i128 = select v6 2.i128 6.i128;", |a| {
            if a & 1 == 1 { 2 } else { 6 }
        }),
        ("umulsat", "v5.i128 = zext v4 i128;", |a| {
            a & u64::MAX as u128
        }),
    ] {
        let (results, status) = if op == "umulo" {
            ("(v7.i128, v8.i1)", "v9.i8 = zext v8 i8;\n    return v9;")
        } else {
            ("v7.i128", "return 0.i8;")
        };
        let source = format!(
            r#"func public %apply(v0.*i128, v1.*i128, v10.*i128) -> i8 {{
block0:
    v2.i128 = mload v0 i128;
    v3.i128 = mload v1 i128;
    v4.i64 = trunc v2 i64;
    v6.i1 = trunc v2 i1;
    {narrow}
    {results} = {op} v5 v3;
    mstore v10 v7 i128;
    {status}
}}
"#
        );
        for level in [OptLevel::O0, OptLevel::O2] {
            let artifact = Compile::new(
                parse_verified_native_module(&source),
                CraneliftJitBackend::new(),
            )
            .with_opt_level(level)
            .compile()
            .unwrap_or_else(|errors| panic!("{source} {level:?}: {errors:?}"));
            let apply: unsafe extern "C" fn(*const u128, *const u128, *mut u128) -> u8 =
                unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
            for a in values {
                for b in values {
                    let (product, overflow) = narrowed(a).overflowing_mul(b);
                    let expected = match op {
                        "umulo" => (product, overflow),
                        _ => (if overflow { u128::MAX } else { product }, false),
                    };
                    let mut result = 0;
                    let status = unsafe { apply(&a, &b, &mut result) };
                    assert_eq!(
                        (result, status == 1),
                        expected,
                        "{source} {level:?} {a:x} {b:x}"
                    );
                }
            }
        }
    }
}

#[test]
fn i128_truncations_take_the_low_bits() {
    let source = r#"func public %apply(v0.*i64, v1.*i64, v2.*i128, v3.*[i64; 9]) {
block0:
    v4.i64 = mload v0 i64;
    v5.i64 = mload v1 i64;
    v6.i128 = mload v2 i128;
    v7.i128 = zext v4 i128;
    v8.i128 = zext v5 i128;
    v9.i128 = mul v7 v8;
    v10.i64 = trunc v9 i64;
    v11.i128 = shr 64.i128 v9;
    v12.i64 = trunc v11 i64;
    v13.i64 = trunc v6 i64;
    v14.i32 = trunc v6 i32;
    v15.i64 = zext v14 i64;
    v16.i8 = trunc v6 i8;
    v17.i64 = zext v16 i64;
    v18.i128 = shr 70.i128 v6;
    v19.i64 = trunc v18 i64;
    v20.i128 = sar 64.i128 v6;
    v21.i64 = trunc v20 i64;
    v22.i128 = shl 3.i128 v6;
    v23.i64 = trunc v22 i64;
    v24.i128 = add v6 v9;
    v25.i64 = trunc v24 i64;
    v26.[i64; 9] = insert_value undef.[i64; 9] 0.i256 v10;
    v27.[i64; 9] = insert_value v26 1.i256 v12;
    v28.[i64; 9] = insert_value v27 2.i256 v13;
    v29.[i64; 9] = insert_value v28 3.i256 v15;
    v30.[i64; 9] = insert_value v29 4.i256 v17;
    v31.[i64; 9] = insert_value v30 5.i256 v19;
    v32.[i64; 9] = insert_value v31 6.i256 v21;
    v33.[i64; 9] = insert_value v32 7.i256 v23;
    v34.[i64; 9] = insert_value v33 8.i256 v25;
    mstore v3 v34 [i64; 9];
    return;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let apply: unsafe extern "C" fn(*const u64, *const u64, *const i128, *mut [u64; 9]) =
            unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
        for (a, b, wide) in [
            (u64::MAX, u64::MAX, -1i128),
            (
                0xfedc_ba98_7654_3210,
                0x0123_4567_89ab_cdef,
                -0x0123_4567_89ab_cdef_fedc_ba98_7654_3211,
            ),
            (3, 5, 0x7fff_0000_0000_0000_8000_0000_0000_00ff),
        ] {
            let product = u128::from(a) * u128::from(b);
            let expected = [
                product as u64,
                (product >> 64) as u64,
                wide as u64,
                u64::from(wide as u32),
                u64::from(wide as u8),
                ((wide as u128) >> 70) as u64,
                (wide >> 64) as u64,
                (wide << 3) as u64,
                wide.wrapping_add(product as i128) as u64,
            ];
            let mut result = [0; 9];
            unsafe { apply(&a, &b, &wide, &mut result) };
            assert_eq!(result, expected, "{a:#x} {b:#x} {wide:#x} {level:?}");
        }
    }
}

#[test]
fn i128_limb_carry_chains_match_ir() {
    // Three-limb addition and subtraction in Fe's spelling: each limb widens
    // to i128, adds or subtracts the previous limb's carry (high word) or
    // borrow (bit 127), and splits. The last sum adds a full limb as its
    // third term, which is no carry.
    let source = r#"func public %apply(v0.*[i64; 3], v1.*[i64; 3], v2.*[i64; 10]) {
block0:
    v3.[i64; 3] = mload v0 [i64; 3];
    v4.[i64; 3] = mload v1 [i64; 3];
    v5.i64 = extract_value v3 0.i256;
    v6.i64 = extract_value v3 1.i256;
    v7.i64 = extract_value v3 2.i256;
    v8.i64 = extract_value v4 0.i256;
    v9.i64 = extract_value v4 1.i256;
    v10.i64 = extract_value v4 2.i256;
    v11.i128 = zext v5 i128;
    v12.i128 = zext v6 i128;
    v13.i128 = zext v7 i128;
    v14.i128 = zext v8 i128;
    v15.i128 = zext v9 i128;
    v16.i128 = zext v10 i128;
    v17.i128 = add v11 v14;
    v18.i64 = trunc v17 i64;
    v19.i128 = shr 64.i128 v17;
    v20.i64 = trunc v19 i64;
    v21.i128 = add v12 v15;
    v22.i128 = zext v20 i128;
    v23.i128 = add v21 v22;
    v24.i64 = trunc v23 i64;
    v25.i128 = shr 64.i128 v23;
    v26.i64 = trunc v25 i64;
    v27.i128 = zext v26 i128;
    v28.i128 = add v13 v16;
    v29.i128 = add v27 v28;
    v30.i64 = trunc v29 i64;
    v31.i128 = shr 64.i128 v29;
    v32.i64 = trunc v31 i64;
    v33.i128 = sub v11 v14;
    v34.i64 = trunc v33 i64;
    v35.i128 = shr 127.i128 v33;
    v36.i64 = trunc v35 i64;
    v37.i128 = sub v12 v15;
    v38.i128 = zext v36 i128;
    v39.i128 = sub v37 v38;
    v40.i64 = trunc v39 i64;
    v41.i128 = shr 127.i128 v39;
    v42.i64 = trunc v41 i64;
    v43.i128 = sub v13 v16;
    v44.i128 = zext v42 i128;
    v45.i128 = sub v43 v44;
    v46.i64 = trunc v45 i64;
    v47.i128 = shr 127.i128 v45;
    v48.i64 = trunc v47 i64;
    v49.i128 = add v28 v11;
    v50.i128 = shr 64.i128 v49;
    v51.i64 = trunc v50 i64;
    v52.[i64; 10] = insert_value undef.[i64; 10] 0.i256 v18;
    v53.[i64; 10] = insert_value v52 1.i256 v24;
    v54.[i64; 10] = insert_value v53 2.i256 v30;
    v55.[i64; 10] = insert_value v54 3.i256 v32;
    v56.[i64; 10] = insert_value v55 4.i256 v34;
    v57.[i64; 10] = insert_value v56 5.i256 v40;
    v58.[i64; 10] = insert_value v57 6.i256 v46;
    v59.[i64; 10] = insert_value v58 7.i256 v48;
    v60.[i64; 10] = insert_value v59 8.i256 v51;
    v61.i64 = trunc v49 i64;
    v62.[i64; 10] = insert_value v60 9.i256 v61;
    mstore v2 v62 [i64; 10];
    return;
}
"#;
    let low_words = |words: [u64; 3]| u128::from(words[0]) | (u128::from(words[1]) << 64);
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let apply: unsafe extern "C" fn(*const [u64; 3], *const [u64; 3], *mut [u64; 10]) =
            unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
        for (a, b) in [
            ([0, 0, 0], [0, 0, 0]),
            ([u64::MAX; 3], [1, 0, 0]),
            ([u64::MAX; 3], [u64::MAX; 3]),
            ([0, 0, 0], [1, 0, 0]),
            ([5, 0, 7], [6, 0, 7]),
            (
                [
                    0x0123_4567_89ab_cdef,
                    0xfedc_ba98_7654_3210,
                    0x8000_0000_0000_0001,
                ],
                [
                    0xfedc_ba98_7654_3211,
                    0x0123_4567_89ab_cdef,
                    0x8000_0000_0000_0000,
                ],
            ),
        ] {
            // Two words of each operand, then the third with the carry or
            // borrow out of the second.
            let (low_a, low_b) = (low_words(a), low_words(b));
            let (low_sum, carry) = low_a.overflowing_add(low_b);
            let top = u128::from(a[2]) + u128::from(b[2]) + u128::from(carry);
            let (low_difference, borrow) = low_a.overflowing_sub(low_b);
            let top_difference = i128::from(a[2]) - i128::from(b[2]) - i128::from(borrow);
            let third_term = u128::from(a[2]) + u128::from(b[2]) + u128::from(a[0]);
            let expected = [
                low_sum as u64,
                (low_sum >> 64) as u64,
                top as u64,
                (top >> 64) as u64,
                low_difference as u64,
                (low_difference >> 64) as u64,
                top_difference as u64,
                u64::from(top_difference < 0),
                (third_term >> 64) as u64,
                third_term as u64,
            ];
            let mut result = [0; 10];
            unsafe { apply(&a, &b, &mut result) };
            assert_eq!(result, expected, "{a:x?} {b:x?} {level:?}");
        }
    }
}

#[test]
fn lone_limb_carries_match_ir() {
    // A limb that adds only the previous limb's carry, or subtracts only its
    // borrow, takes it as a flag with a zero addend; zero less a borrow
    // passes it through.
    let source = r#"func public %apply(v0.*[i64; 3], v1.*[i64; 6]) {
block0:
    v2.[i64; 3] = mload v0 [i64; 3];
    v3.i64 = extract_value v2 0.i256;
    v4.i64 = extract_value v2 1.i256;
    v5.i64 = extract_value v2 2.i256;
    v6.i128 = zext v3 i128;
    v7.i128 = zext v4 i128;
    v8.i128 = zext v5 i128;
    v9.i128 = add v6 v7;
    v10.i128 = shr 64.i128 v9;
    v11.i64 = trunc v10 i64;
    v12.i128 = zext v11 i128;
    v13.i128 = add v8 v12;
    v14.i64 = trunc v13 i64;
    v15.i128 = shr 64.i128 v13;
    v16.i64 = trunc v15 i64;
    v17.i128 = sub v6 v7;
    v18.i128 = shr 127.i128 v17;
    v19.i64 = trunc v18 i64;
    v20.i128 = zext v19 i128;
    v21.i128 = sub v8 v20;
    v22.i64 = trunc v21 i64;
    v23.i128 = shr 127.i128 v21;
    v24.i64 = trunc v23 i64;
    v29.i128 = sub 0.i128 v20;
    v30.i64 = trunc v29 i64;
    v31.i128 = shr 127.i128 v29;
    v32.i64 = trunc v31 i64;
    v25.[i64; 6] = insert_value undef.[i64; 6] 0.i256 v14;
    v26.[i64; 6] = insert_value v25 1.i256 v16;
    v27.[i64; 6] = insert_value v26 2.i256 v22;
    v28.[i64; 6] = insert_value v27 3.i256 v24;
    v33.[i64; 6] = insert_value v28 4.i256 v30;
    v34.[i64; 6] = insert_value v33 5.i256 v32;
    mstore v1 v34 [i64; 6];
    return;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let apply: unsafe extern "C" fn(*const [u64; 3], *mut [u64; 6]) =
            unsafe { std::mem::transmute(artifact.function_address("apply").unwrap()) };
        for words in [
            [u64::MAX, 1, u64::MAX],
            [u64::MAX, 1, 5],
            [0, 1, 0],
            [0, 1, 9],
            [3, 2, u64::MAX],
            [2, 3, u64::MAX],
        ] {
            let [a, b, c] = words;
            let (_, carry) = a.overflowing_add(b);
            let (sum, carry_out) = c.overflowing_add(u64::from(carry));
            let (_, borrow) = a.overflowing_sub(b);
            let (difference, borrow_out) = c.overflowing_sub(u64::from(borrow));
            let expected = [
                sum,
                u64::from(carry_out),
                difference,
                u64::from(borrow_out),
                0u64.wrapping_sub(u64::from(borrow)),
                u64::from(borrow),
            ];
            let mut result = [0; 6];
            unsafe { apply(&words, &mut result) };
            assert_eq!(result, expected, "{words:?} {level:?}");
        }
    }
}

#[test]
fn freeze_passes_values_through_and_fixes_undef() {
    let source = r#"func public %frozen(v0.i64, v1.*i256, v2.*i256) -> i64 {
block0:
    v3.i64 = freeze v0;
    v4.i256 = mload v1 i256;
    v5.i256 = freeze v4;
    mstore v2 v5 i256;
    v6.i64 = freeze undef.i64;
    v7.i64 = sub v6 v6;
    v8.i64 = add v3 v7;
    return v8;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let frozen: unsafe extern "C" fn(i64, *const u64, *mut u64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("frozen").unwrap()) };
        let input = [1u64, 2, 3, u64::MAX];
        let mut output = [0u64; 4];
        let result = unsafe { frozen(-7, input.as_ptr(), output.as_mut_ptr()) };
        assert_eq!((result, output), (-7, input), "{level:?}");
    }
}

#[test]
fn shifts_by_masked_counts_match_wrapping_shifts() {
    // Counts masked below the width skip the oversized fallback.
    let source = r#"func public %shifts(v0.i64, v1.i64) -> i64 {
block0:
    v2.i64 = and v1 63.i64;
    v3.i64 = shl v2 v0;
    v4.i64 = shr v2 v0;
    v5.i64 = sar v2 v0;
    v6.i64 = xor v3 v4;
    v7.i64 = xor v6 v5;
    return v7;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let shifts: unsafe extern "C" fn(i64, i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("shifts").unwrap()) };
        for value in [0, 1, -1, i64::MIN, 0x0123_4567_89ab_cdef] {
            for count in [0, 1, 7, 63, 64, 65, 127, -1] {
                let bits = (count & 63) as u32;
                let expected = value.wrapping_shl(bits)
                    ^ (value as u64).wrapping_shr(bits) as i64
                    ^ value.wrapping_shr(bits);
                assert_eq!(
                    unsafe { shifts(value, count) },
                    expected,
                    "{level:?} {value} {count}"
                );
            }
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

#[test]
fn wide_division_operand_classes_preserve_signed_and_unsigned_results() {
    for (ty, width) in [(Type::I128, 128), (Type::I256, 256)] {
        let mut values = vec![
            Immediate::zero(ty),
            Immediate::one(ty),
            Immediate::all_one(ty),
            Immediate::signed_min(ty),
            Immediate::signed_max(ty),
        ];
        for bit in [
            1, 2, 62, 63, 64, 65, 126, 127, 128, 129, 190, 191, 192, 193, 254, 255,
        ] {
            if bit < width {
                let value = U256::one() << bit;
                values.extend(
                    [value - 1, value, value + 1]
                        .map(|value| Immediate::from_i256(I256::from(value), ty)),
                );
            }
        }
        for op in ["udiv", "umod", "sdiv", "smod"] {
            let mut cases = Vec::new();
            for &lhs in &values {
                for &rhs in values.iter().filter(|rhs| !rhs.is_zero()) {
                    let expected = match op {
                        "udiv" => lhs.udiv(rhs),
                        "umod" => lhs.urem(rhs),
                        "sdiv" => lhs.sdiv(rhs),
                        "smod" => lhs.srem(rhs),
                        _ => unreachable!(),
                    };
                    cases.push((lhs, rhs, expected, false));
                }
            }
            check_scalar_cases(op, ty, &cases);
        }
    }
}

#[test]
fn branches_on_a_pointer_null_test() {
    let source = r#"func public %is_null(v0.*i8) -> i8 {
block0:
    v1.i1 = is_zero v0;
    br v1 block1 block2;

block1:
    return 1.i8;

block2:
    return 0.i8;
}
"#;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap();
        let address = artifact.function_address("is_null").unwrap();
        let is_null: unsafe extern "C" fn(*const u8) -> u8 =
            unsafe { std::mem::transmute(address) };
        let byte = 0u8;
        assert_eq!(unsafe { is_null(std::ptr::null()) }, 1, "{level:?}");
        assert_eq!(unsafe { is_null(&byte) }, 0, "{level:?}");
    }
}

#[test]
fn black_box_returns_its_operand_at_every_width() {
    for (ty, literal) in [
        ("i1", "1"),
        ("i8", "-85"),
        ("i16", "-21555"),
        ("i32", "-1412567278"),
        ("i64", "-6066930334832433271"),
        ("i128", "-111914144268397404893097173176100974321"),
        (
            "i256",
            "-38082381820413527299138373923093541917439398027851369961089083197252413128367",
        ),
    ] {
        let source = format!(
            r#"func public %matches() -> i8 {{
block0:
    v0.{ty} = black_box {literal}.{ty};
    v1.i1 = eq v0 {literal}.{ty};
    v2.i8 = zext v1 i8;
    return v2;
}}
"#
        );
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
            let artifact = Compile::new(
                parse_verified_native_module(&source),
                CraneliftJitBackend::new(),
            )
            .with_opt_level(level)
            .compile()
            .unwrap_or_else(|errors| panic!("{ty} {level:?}: {errors:?}"));
            let matches: unsafe extern "C" fn() -> u8 =
                unsafe { std::mem::transmute(artifact.function_address("matches").unwrap()) };
            assert_eq!(unsafe { matches() }, 1, "{ty} {level:?}");
        }
    }
}

#[test]
fn selects_choose_at_every_width() {
    for (ty, size) in [("i8", 1), ("i64", 8), ("i128", 16), ("i256", 32)] {
        let source = format!(
            r#"func public %choose(v0.i8, v1.*{ty}, v2.*{ty}, v3.*{ty}) {{
block0:
    v4.i1 = ne v0 0.i8;
    v5.{ty} = mload v1 {ty};
    v6.{ty} = mload v2 {ty};
    v7.{ty} = select v4 v5 v6;
    mstore v3 v7 {ty};
    return;
}}
"#
        );
        for level in [OptLevel::O0, OptLevel::O2] {
            let artifact = Compile::new(
                parse_verified_native_module(&source),
                CraneliftJitBackend::new(),
            )
            .with_opt_level(level)
            .compile()
            .unwrap_or_else(|errors| panic!("{ty} {level:?}: {errors:?}"));
            let choose: unsafe extern "C" fn(u8, *const u8, *const u8, *mut u8) =
                unsafe { std::mem::transmute(artifact.function_address("choose").unwrap()) };
            let a: [u8; 32] = std::array::from_fn(|i| 0x11 + i as u8);
            let b: [u8; 32] = std::array::from_fn(|i| 0xc0 - i as u8);
            for cond in [0u8, 1, 2, 255] {
                let mut result = [0xa5u8; 32];
                unsafe { choose(cond, a.as_ptr(), b.as_ptr(), result.as_mut_ptr()) };
                let chosen = if cond != 0 { &a } else { &b };
                assert_eq!(&result[..size], &chosen[..size], "{ty} {cond} {level:?}");
                assert!(result[size..].iter().all(|&byte| byte == 0xa5));
            }
        }
    }
}
