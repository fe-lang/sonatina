use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};
use sonatina_ir::{I256, Immediate, Type, U256};

use super::{parse_native_module, parse_verified_native_module};

#[test]
fn wide_division_loops_compose_with_each_other_and_sonatina_phi_edges() {
    for (width, ty) in [(128, Type::I128), (256, Type::I256)] {
        for (div, rem) in [("udiv", "umod"), ("sdiv", "smod")] {
            let source = format!(
                r#"
func public %iterate(v0.*i{width}, v1.*i{width}, v2.i64, v3.*i{width}) {{
block0:
    v4.i{width} = mload v0 i{width};
    v5.i{width} = mload v1 i{width};
    jump block1;
block1:
    v6.i{width} = phi (v4 block0) (v10 block1);
    v7.i64 = phi (0.i64 block0) (v11 block1);
    v8.i{width} = {div} v6 v5;
    v9.i{width} = {rem} v6 v5;
    v10.i{width} = add v8 v9;
    v11.i64 = add v7 1.i64;
    v12.i1 = lt v11 v2;
    br v12 block1 block2;
block2:
    mstore v3 v10 i{width};
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
                .unwrap();
                let iterate: unsafe extern "C" fn(*const u8, *const u8, i64, *mut u8) =
                    unsafe { std::mem::transmute(artifact.function_address("iterate").unwrap()) };
                for lhs in [
                    Immediate::signed_min(ty),
                    Immediate::all_one(ty),
                    Immediate::signed_max(ty),
                ] {
                    for rhs in [3, -7, -1].map(|n| Immediate::from_i256(I256::from(n), ty)) {
                        for count in [1, 2, 5] {
                            let mut expected = lhs;
                            for _ in 0..count {
                                expected = if div == "sdiv" {
                                    expected.sdiv(rhs) + expected.srem(rhs)
                                } else {
                                    expected.udiv(rhs) + expected.urem(rhs)
                                };
                            }
                            let lhs = lhs.zext(Type::I256).as_i256().to_u256().to_little_endian();
                            let rhs = rhs.zext(Type::I256).as_i256().to_u256().to_little_endian();
                            let expected = expected
                                .zext(Type::I256)
                                .as_i256()
                                .to_u256()
                                .to_little_endian();
                            let mut output = [0xa5; 32];
                            unsafe {
                                iterate(lhs.as_ptr(), rhs.as_ptr(), count, output.as_mut_ptr())
                            };
                            assert_eq!(
                                &output[..width / 8],
                                &expected[..width / 8],
                                "i{width} {div} {level:?} {count}"
                            );
                            assert!(output[width / 8..].iter().all(|&byte| byte == 0xa5));
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn loop_carried_i256_survives_next_result_slot_write() {
    let source = r#"
func public %previous(v0.*i256, v1.i64, v2.*i256) {
block0:
    v3.i256 = mload v0 i256;
    jump block1;
block1:
    v4.i256 = phi (v3 block0) (v6 block1);
    v5.i64 = phi (0.i64 block0) (v7 block1);
    v6.i256 = add v4 1.i256;
    mstore v2 v4 i256;
    v7.i64 = add v5 1.i64;
    v8.i1 = lt v7 v1;
    br v8 block1 block2;
block2:
    return;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(parse_native_module(source), CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .expect("i256 loop should compile");
        let previous: unsafe extern "C" fn(*const u8, i64, *mut u8) =
            unsafe { std::mem::transmute(artifact.function_address("previous").unwrap()) };
        for start in [U256::zero(), (U256::one() << 128) - U256::one()] {
            for count in [1, 2, 7] {
                let mut result = [0u8; 32];
                unsafe {
                    previous(
                        start.to_little_endian().as_ptr(),
                        count,
                        result.as_mut_ptr(),
                    )
                };
                assert_eq!(
                    U256::from_little_endian(&result),
                    start + U256::from(count - 1)
                );
            }
        }
    }
}

#[test]
fn wide_phi_swaps_capture_all_inputs_before_writing_destinations() {
    // The 15-byte array exercises every storage chunk size, including tails.
    for (ty, size) in [("i256", 32), ("[i8; 15]", 15)] {
        let source = format!(
            r#"
func public %swap(v0.*{ty}, v1.*{ty}, v2.*{ty}, v3.i64) {{
block0:
    v4.{ty} = mload v0 {ty};
    v5.{ty} = mload v1 {ty};
    jump block1;
block1:
    v6.{ty} = phi (v4 block0) (v7 block1);
    v7.{ty} = phi (v5 block0) (v6 block1);
    v8.i64 = phi (0.i64 block0) (v9 block1);
    v9.i64 = add v8 1.i64;
    v10.i1 = lt v9 v3;
    br v10 block1 block2;
block2:
    mstore v2 v6 {ty};
    return;
}}
"#
        );
        for level in [OptLevel::O0, OptLevel::O2] {
            let artifact = Compile::new(parse_native_module(&source), CraneliftJitBackend::new())
                .with_opt_level(level)
                .compile()
                .expect("wide phi swap should compile");
            let swap: unsafe extern "C" fn(*const u8, *const u8, *mut u8, i64) =
                unsafe { std::mem::transmute(artifact.function_address("swap").unwrap()) };
            let lhs = [0x12u8; 32];
            let rhs = [0xabu8; 32];
            for count in [1, 2, 3, 4, 7] {
                let mut result = [0u8; 32];
                unsafe { swap(lhs.as_ptr(), rhs.as_ptr(), result.as_mut_ptr(), count) };
                let expected = if count % 2 == 1 { &lhs } else { &rhs };
                assert_eq!(&result[..size], &expected[..size], "{ty} {level:?} {count}");
            }
        }
    }
}

#[test]
fn looping_entry_blocks_enter_through_a_prologue() {
    let source = r#"
type @Pair = { i256, i256 };
func inline(never) private %triple(v0.*i256, v1.*i64) -> @Pair {
block0:
    v2.i64 = mload v1 i64;
    v3.i64 = add v2 1.i64;
    mstore v1 v3 i64;
    v4.i256 = mload v0 i256;
    v5.i256 = mul v4 3.i256;
    mstore v0 v5 i256;
    v6.i1 = lt v3 4.i64;
    br v6 block0 block1;
block1:
    v7.i1 = gt v5 100.i256;
    br v7 block2 block3;
block2:
    jump block3;
block3:
    v8.i256 = phi (v5 block1) (v4 block2);
    v9.@Pair = insert_value undef.@Pair 0.i8 v8;
    v10.@Pair = insert_value v9 1.i8 v5;
    return v10;
}
func public %run(v0.*i256, v1.*i64, v2.*i256) {
block0:
    v3.@Pair = call %triple v0 v1;
    v4.i256 = extract_value v3 0.i8;
    v5.i256 = extract_value v3 1.i8;
    v6.i256 = sub v5 v4;
    mstore v2 v6 i256;
    return;
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
        let run: unsafe extern "C" fn(*mut u8, *mut i64, *mut u8) =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        // Four iterations triple the value; the last two exceed 100.
        for (initial, expected) in [(1u64, 0u64), (5, 405 - 135)] {
            let mut value = U256::from(initial).to_little_endian();
            let mut counter = 0i64;
            let mut output = [0xa5; 32];
            unsafe { run(value.as_mut_ptr(), &mut counter, output.as_mut_ptr()) };
            assert_eq!(counter, 4, "{level:?}");
            assert_eq!(
                value,
                U256::from(initial * 81).to_little_endian(),
                "{level:?}"
            );
            assert_eq!(output, U256::from(expected).to_little_endian(), "{level:?}");
        }
    }
}

#[test]
fn aggregate_phi_rotations_copy_through_a_temporary() {
    // Three phis rotate each loop iteration: every destination is another
    // copy's source, so the edge saves one phi before overwriting it.
    for (ty, size) in [("[i64; 20]", 160), ("[i8; 15]", 15)] {
        let source = format!(
            r#"
func public %rotate(v0.*{ty}, v1.*{ty}, v2.*{ty}, v3.i64, v4.*{ty}) {{
block0:
    v5.{ty} = mload v0 {ty};
    v6.{ty} = mload v1 {ty};
    v7.{ty} = mload v2 {ty};
    jump block1;
block1:
    v8.{ty} = phi (v5 block0) (v9 block1);
    v9.{ty} = phi (v6 block0) (v10 block1);
    v10.{ty} = phi (v7 block0) (v8 block1);
    v11.i64 = phi (0.i64 block0) (v12 block1);
    v12.i64 = add v11 1.i64;
    v13.i1 = lt v12 v3;
    br v13 block1 block2;
block2:
    mstore v4 v8 {ty};
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
            .unwrap();
            let rotate: unsafe extern "C" fn(*const u8, *const u8, *const u8, i64, *mut u8) =
                unsafe { std::mem::transmute(artifact.function_address("rotate").unwrap()) };
            let inputs: [Vec<u8>; 3] = std::array::from_fn(|i| vec![0x11 * (i as u8 + 1); size]);
            for count in 1..=7 {
                let mut output = vec![0; size];
                unsafe {
                    rotate(
                        inputs[0].as_ptr(),
                        inputs[1].as_ptr(),
                        inputs[2].as_ptr(),
                        count,
                        output.as_mut_ptr(),
                    )
                };
                // After `count` iterations the first phi holds input `count - 1`.
                let expected = &inputs[(count as usize - 1) % 3];
                assert_eq!(&output, expected, "{ty} {level:?} {count}");
            }
        }
    }
}

#[test]
fn aggregate_phi_reads_a_view_of_another_phi_before_it_changes() {
    // The backedge sets `v7` to a view into `v6` while replacing `v6`, so
    // (a, b, c) rotates to (b, c, a) only if `v7` copies first.
    let source = r#"
type @Half = {[i64; 20]};
type @Whole = {@Half, @Half};
func public %rotate(v0.*@Whole, v1.*@Half, v2.i64, v3.*@Whole, v4.*@Half) {
block0:
    v5.@Whole = mload v0 @Whole;
    v6.@Half = mload v1 @Half;
    jump block1;
block1:
    v7.@Whole = phi (v5 block0) (v12 block1);
    v8.@Half = phi (v6 block0) (v9 block1);
    v13.i64 = phi (0.i64 block0) (v14 block1);
    v9.@Half = extract_value v7 0.i64;
    v10.@Half = extract_value v7 1.i64;
    v11.@Whole = insert_value undef.@Whole 0.i64 v10;
    v12.@Whole = insert_value v11 1.i64 v8;
    v14.i64 = add v13 1.i64;
    v15.i1 = lt v14 v2;
    br v15 block1 block2;
block2:
    mstore v3 v7 @Whole;
    mstore v4 v8 @Half;
    return;
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
        let rotate: unsafe extern "C" fn(*const i64, *const i64, i64, *mut i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("rotate").unwrap()) };
        let halves: [[i64; 20]; 3] =
            std::array::from_fn(|half| std::array::from_fn(|i| (half * 100 + i) as i64));
        let whole: Vec<i64> = halves[0].iter().chain(&halves[1]).copied().collect();
        for count in 1..=6 {
            let mut state = [0usize, 1, 2];
            for _ in 1..count {
                state.rotate_left(1);
            }
            let mut output_whole = vec![0; 40];
            let mut output_half = [0; 20];
            unsafe {
                rotate(
                    whole.as_ptr(),
                    halves[2].as_ptr(),
                    count,
                    output_whole.as_mut_ptr(),
                    output_half.as_mut_ptr(),
                )
            };
            assert_eq!(output_whole[..20], halves[state[0]], "{level:?} {count}");
            assert_eq!(output_whole[20..], halves[state[1]], "{level:?} {count}");
            assert_eq!(output_half, halves[state[2]], "{level:?} {count}");
        }
    }
}

#[test]
fn aggregate_phi_copies_stay_on_their_edge() {
    // `v5` stays live on the loop exit while the backedge replaces it, and
    // a br_table reaches aggregate phis in several successors. Copies for
    // one edge must not clobber the values another edge carries. The exit
    // starts with a multi-result instruction rather than a phi.
    let source = r#"
func public %select(v0.*[i64; 20], v1.i64, v2.i64, v3.*[i64; 20]) {
block0:
    v4.[i64; 20] = mload v0 [i64; 20];
    jump block1;
block1:
    v5.[i64; 20] = phi (v4 block0) (v8 block1);
    v6.i64 = phi (0.i64 block0) (v9 block1);
    v7.i64 = extract_value v5 0.i64;
    v8.[i64; 20] = insert_value v5 0.i64 v6;
    v9.i64 = add v6 1.i64;
    v10.i1 = lt v9 v1;
    br v10 block1 block2;
block2:
    (v20.i64, v21.i1) = uaddo v2 0.i64;
    br_table v20 block5 (0.i64 block3) (1.i64 block4);
block3:
    jump block6;
block4:
    jump block6;
block5:
    jump block6;
block6:
    v11.[i64; 20] = phi (v5 block3) (v8 block4) (undef.[i64; 20] block5);
    v12.i64 = phi (v7 block3) (v9 block4) (-1.i64 block5);
    v13.[i64; 20] = insert_value v11 19.i64 v12;
    mstore v3 v13 [i64; 20];
    return;
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
        let select: unsafe extern "C" fn(*const i64, i64, i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("select").unwrap()) };
        let input: [i64; 20] = std::array::from_fn(|i| 50 + i as i64);
        for count in [1, 2, 5] {
            for choice in [0, 1, 2] {
                let mut output = [0; 20];
                unsafe { select(input.as_ptr(), count, choice, output.as_mut_ptr()) };
                // The final iteration reads phi `v5`, whose word zero the
                // previous iteration set to `count - 2`.
                let mut last = input;
                if count > 1 {
                    last[0] = count - 2;
                }
                let expected = match choice {
                    0 => {
                        let mut expected = last;
                        expected[19] = last[0];
                        expected
                    }
                    1 => {
                        let mut expected = last;
                        expected[0] = count - 1;
                        expected[19] = count;
                        expected
                    }
                    _ => {
                        let mut expected = [0; 20];
                        expected[19] = -1;
                        expected
                    }
                };
                assert_eq!(output, expected, "{level:?} {count} {choice}");
            }
        }
    }
}

/// Checks `%select`, which loads a `ty` scrutinee through its first argument
/// and dispatches on it with a `br_table`. The `i`th of `keys` returns `i`,
/// `shared` keys branch straight to the merge block and return the second
/// argument, and every other value takes the default and returns -1.
fn check_br_table(ty: Type, keys: &[i128], shared: &[i128], probes: &[i128]) {
    let name = match ty {
        Type::I8 => "i8",
        Type::I32 => "i32",
        Type::I64 => "i64",
        Type::I128 => "i128",
        Type::I256 => "i256",
        _ => unreachable!(),
    };
    let imm = |value: i128| Immediate::from_i256(I256::from(value), ty);
    let default = keys.len() + 1;
    let merge = keys.len() + 2;
    let table: String = keys
        .iter()
        .enumerate()
        .map(|(i, &key)| format!(" ({}.{name} block{})", imm(key), i + 1))
        .chain(
            shared
                .iter()
                .map(|&key| format!(" ({}.{name} block{merge})", imm(key))),
        )
        .collect();
    let blocks: String = (1..=default)
        .map(|block| format!("block{block}:\n    jump block{merge};\n"))
        .collect();
    let inputs: String = (0..keys.len())
        .map(|i| format!(" ({i}.i64 block{})", i + 1))
        .chain((!shared.is_empty()).then(|| " (v1 block0)".to_string()))
        .collect();
    let source = format!(
        "func public %select(v0.*{name}, v1.i64) -> i64 {{
block0:
    v2.{name} = mload v0 {name};
    br_table v2 block{default}{table};
{blocks}block{merge}:
    v3.i64 = phi{inputs} (-1.i64 block{default});
    return v3;
}}
"
    );
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(&source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{source}\n{errors:?}"));
        let select: unsafe extern "C" fn(*const u8, i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("select").unwrap()) };
        for &probe in probes {
            let probe = imm(probe);
            let bytes = probe
                .zext(Type::I256)
                .as_i256()
                .to_u256()
                .to_little_endian();
            let expected = if let Some(i) = keys.iter().position(|&key| imm(key) == probe) {
                i as i64
            } else if shared.iter().any(|&key| imm(key) == probe) {
                77
            } else {
                -1
            };
            let actual = unsafe { select(bytes.as_ptr(), 77) };
            assert_eq!(actual, expected, "{level:?} {name} {probe}\n{source}");
        }
    }
}

#[test]
fn br_table_dense_keys() {
    let probes: Vec<_> = (-3..=20)
        .chain([i32::MIN as i128, i32::MAX as i128])
        .collect();
    check_br_table(Type::I32, &(0..16).collect::<Vec<_>>(), &[16, 17], &probes);
    // In unsigned order the keys are two ranges, 0..=3 and 252..=255.
    check_br_table(
        Type::I8,
        &(-4..=3).collect::<Vec<_>>(),
        &[-128, 127],
        &(-128..=127).collect::<Vec<_>>(),
    );
}

#[test]
fn br_table_holes_in_dense_keys_take_the_default() {
    // Every other value is a key: one jump table covers them, with the
    // default in its holes.
    let keys: Vec<_> = (0..12).map(|key| key * 2).collect();
    check_br_table(Type::I32, &keys, &[25], &(-3..=30).collect::<Vec<_>>());
}

#[test]
fn br_table_sparse_keys() {
    let keys = [
        -5,
        0,
        3,
        1000,
        1 << 40,
        i64::MIN as i128,
        i64::MAX as i128,
        77777,
    ];
    let probes: Vec<_> = keys
        .iter()
        .chain(&[9, 2, -1])
        .flat_map(|&key: &i128| [key - 1, key, key + 1])
        .collect();
    check_br_table(Type::I64, &keys, &[9], &probes);
    let wide = [0, 1, 1 << 64, 1 << 100, -1, i128::MIN];
    let probes: Vec<_> = wide
        .iter()
        .chain(&[2])
        .flat_map(|&key: &i128| [key.wrapping_sub(1), key, key.wrapping_add(1)])
        .collect();
    check_br_table(Type::I128, &wide, &[2], &probes);
}

#[test]
fn br_table_on_i256_switches_on_the_low_limb() {
    // Every key fits the low limb, so a scrutinee with any upper bit set
    // takes the default even when its low limb matches a key.
    let probes: Vec<_> = (-2..=8)
        .chain([(1 << 64) + 2, (1 << 127) + 3, 1 << 64, -(1 << 64) + 1])
        .collect();
    check_br_table(Type::I256, &[0, 1, 2, 3, 5, 1000], &[6], &probes);
}

#[test]
fn br_table_with_only_a_default() {
    for ty in [Type::I64, Type::I256] {
        check_br_table(ty, &[], &[], &[0, 1, -1, 1 << 70]);
    }
}

#[test]
fn br_table_with_few_keys() {
    check_br_table(Type::I8, &[-1, 0], &[5], &(-128..=127).collect::<Vec<_>>());
    check_br_table(
        Type::I128,
        &[1 << 100],
        &[-1],
        &[0, 1, -1, -2, 1 << 100, (1 << 100) + 1, 1 << 36],
    );
    check_br_table(
        Type::I256,
        &[0, 7],
        &[-1],
        &[0, 7, 8, -1, -2, (1 << 64) + 7, 1 << 64],
    );
}
