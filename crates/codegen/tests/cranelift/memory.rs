use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};

use super::{parse_native_module, parse_verified_native_module};

#[test]
fn aggregate_updates_preserve_snapshots_extracted_views_and_arguments() {
    let source = r#"
type @Pair = { i64, i64 };
type @Outer = { @Pair, i64 };
func public %snapshots(v0.i64, v1.i64, v2.*[i64; 6]) {
block0:
    v3.@Pair = insert_value undef.@Pair 0.i64 v0;
    v4.@Pair = insert_value v3 1.i64 v1;
    v5.@Outer = insert_value undef.@Outer 0.i64 v4;
    v6.@Outer = insert_value v5 1.i64 7.i64;
    v7.@Pair = extract_value v6 0.i64;
    v8.@Pair = insert_value v7 0.i64 91.i64;
    v9.@Outer = insert_value v6 0.i64 v8;
    v10.@Outer = insert_value v9 1.i64 93.i64;
    v11.@Pair = extract_value v6 0.i64;
    v12.i64 = extract_value v11 0.i64;
    v13.i64 = extract_value v11 1.i64;
    v14.@Pair = extract_value v10 0.i64;
    v15.i64 = extract_value v14 0.i64;
    v16.i64 = extract_value v14 1.i64;
    v17.i64 = extract_value v6 1.i64;
    v18.i64 = extract_value v10 1.i64;
    v19.[i64; 6] = insert_value undef.[i64; 6] 0.i64 v12;
    v20.[i64; 6] = insert_value v19 1.i64 v13;
    v21.[i64; 6] = insert_value v20 2.i64 v15;
    v22.[i64; 6] = insert_value v21 3.i64 v16;
    v23.[i64; 6] = insert_value v22 4.i64 v17;
    v24.[i64; 6] = insert_value v23 5.i64 v18;
    mstore v2 v24 [i64; 6];
    return;
}
func public %update_argument(v0.@Pair, v1.i64, v2.*@Pair) {
block0:
    v3.@Pair = insert_value v0 0.i64 v1;
    v4.@Pair = insert_value v3 1.i64 99.i64;
    mstore v2 v4 @Pair;
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
        let snapshots: unsafe extern "C" fn(i64, i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("snapshots").unwrap()) };
        let update: unsafe extern "C" fn(*mut i64, i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("update_argument").unwrap()) };
        for mut input in [[11, 22], [-1, i64::MIN], [i64::MAX, 0]] {
            let mut result = [0; 6];
            unsafe { snapshots(input[0], input[1], result.as_mut_ptr()) };
            assert_eq!(result, [input[0], input[1], 91, input[1], 7, 93]);
            let original = input;
            unsafe { update(input.as_mut_ptr(), 73, result.as_mut_ptr()) };
            assert_eq!(input, original);
            assert_eq!(&result[..2], &[73, 99]);
        }
    }
}

#[test]
fn aggregate_construction_preserves_loop_carried_snapshots() {
    let source = r#"
func public %iterate(v0.i64, v1.i64, v2.*[i64; 2], v3.*[i64; 2]) {
block0:
    v4.[i64; 2] = insert_value undef.[i64; 2] 0.i64 v0;
    v5.[i64; 2] = insert_value v4 1.i64 7.i64;
    jump block1;
block1:
    v6.[i64; 2] = phi (v5 block0) (v11 block1);
    v7.i64 = phi (0.i64 block0) (v12 block1);
    v8.i64 = extract_value v6 0.i64;
    v9.i64 = add v8 1.i64;
    v10.[i64; 2] = insert_value v6 0.i64 v9;
    v11.[i64; 2] = insert_value v10 1.i64 v7;
    mstore v2 v6 [i64; 2];
    v12.i64 = add v7 1.i64;
    v13.i1 = lt v12 v1;
    br v13 block1 block2;
block2:
    mstore v3 v11 [i64; 2];
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
        let iterate: unsafe extern "C" fn(i64, i64, *mut i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("iterate").unwrap()) };
        for count in [1, 2, 5] {
            let mut previous = [0; 2];
            let mut current = [0; 2];
            unsafe { iterate(23, count, previous.as_mut_ptr(), current.as_mut_ptr()) };
            assert_eq!(
                previous,
                [23 + count - 1, if count == 1 { 7 } else { count - 2 }]
            );
            assert_eq!(current, [23 + count, count - 1]);
        }
    }
}

#[test]
fn aggregate_construction_repeats_a_preheader_insert_consumer() {
    // The preheader result has one static consumer that executes on every iteration.
    let source = r#"
func public %iterate(v0.i64, v1.i64, v2.*[i64; 2]) {
block0:
    v3.[i64; 2] = insert_value undef.[i64; 2] 0.i64 v0;
    v4.[i64; 2] = insert_value v3 1.i64 7.i64;
    jump block1;
block1:
    v5.i64 = phi (0.i64 block0) (v8 block1);
    v6.i64 = add v0 v5;
    v7.[i64; 2] = insert_value v4 0.i64 v6;
    mstore v2 v7 [i64; 2];
    v8.i64 = add v5 1.i64;
    v9.i1 = lt v8 v1;
    br v9 block1 block2;
block2:
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
        let iterate: unsafe extern "C" fn(i64, i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("iterate").unwrap()) };
        for seed in [-19, 0, 23] {
            for count in [1, 2, 5] {
                let mut output = [0; 2];
                unsafe { iterate(seed, count, output.as_mut_ptr()) };
                assert_eq!(output, [seed + count - 1, 7], "{level:?}, {seed}, {count}");
            }
        }
    }
}

#[test]
fn aggregate_updates_preserve_loaded_wide_snapshots_and_views() {
    let source = r#"
type @Wide = { i256, i256 };
func public %update(v0.*@Wide, v1.*i256, v2.*[i256; 4]) {
block0:
    v3.@Wide = mload v0 @Wide;
    v4.i256 = extract_value v3 0.i64;
    v5.i256 = mload v1 i256;
    v6.@Wide = insert_value v3 0.i64 v5;
    v7.i256 = extract_value v6 0.i64;
    v8.@Wide = insert_value v6 0.i64 v4;
    v9.@Wide = insert_value v8 1.i64 v5;
    mstore v0 v9 @Wide;
    v10.i256 = extract_value v3 1.i64;
    v11.i256 = extract_value v9 1.i64;
    v12.[i256; 4] = insert_value undef.[i256; 4] 0.i64 v4;
    v13.[i256; 4] = insert_value v12 1.i64 v10;
    v14.[i256; 4] = insert_value v13 2.i64 v7;
    v15.[i256; 4] = insert_value v14 3.i64 v11;
    mstore v2 v15 [i256; 4];
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
        let update: unsafe extern "C" fn(*mut u64, *const u64, *mut u64) =
            unsafe { std::mem::transmute(artifact.function_address("update").unwrap()) };
        let original = [[11, 22, 33, 44], [55, 66, 77, 88]];
        for replacement in [[91, 92, 93, 94], [u64::MAX, 0, 1 << 63, 7]] {
            let mut input = original;
            let mut output = [[0; 4]; 4];
            unsafe {
                update(
                    input.as_mut_ptr().cast(),
                    replacement.as_ptr(),
                    output.as_mut_ptr().cast(),
                )
            };
            assert_eq!(input, [original[0], replacement], "{level:?}");
            assert_eq!(
                output,
                [original[0], original[1], replacement, replacement],
                "{level:?}"
            );
        }
    }
}

#[test]
fn object_and_constant_indices_zero_extend_narrow_integers() {
    let values = (0..256)
        .map(|i| (1000 + i).to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!(
        r#"
global private const [i64; 256] $values = [{values}];
func public %read_const(v0.i8) -> i64 {{
block0:
    v1.constref<[i64; 256]> = const.ref $values;
    v2.constref<i64> = const.index v1 v0;
    v3.i64 = const.load v2;
    return v3;
}}
func public %read_object(v0.i8) -> i64 {{
block0:
    v1.objref<[i64; 256]> = obj.alloc [i64; 256];
    v2.objref<i64> = obj.index v1 128.i64;
    obj.store v2 1128.i64;
    v3.objref<i64> = obj.index v1 255.i64;
    obj.store v3 1255.i64;
    v4.objref<i64> = obj.index v1 v0;
    v5.i64 = obj.load v4;
    return v5;
}}
"#
    );
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(parse_native_module(&source), CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .expect("unsigned index functions should compile");
        for name in ["read_const", "read_object"] {
            let read: unsafe extern "C" fn(u8) -> i64 =
                unsafe { std::mem::transmute(artifact.function_address(name).unwrap()) };
            for index in [128, 255] {
                assert_eq!(
                    unsafe { read(index) },
                    1000 + i64::from(index),
                    "{name} {level:?}"
                );
            }
        }
    }
}

#[test]
fn gep_indices_still_sign_extend_narrow_integers() {
    let source = r#"
func public %read(v0.*i64, v1.i8) -> i64 {
block0:
    v2.*i64 = gep v0 v1;
    v3.i64 = mload v2 i64;
    return v3;
}
"#;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(parse_native_module(source), CraneliftJitBackend::new())
            .with_opt_level(level)
            .compile()
            .expect("signed GEP should compile");
        let read: unsafe extern "C" fn(*const i64, i8) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("read").unwrap()) };
        let values = [11i64, 22, 33];
        assert_eq!(unsafe { read(values.as_ptr().add(1), -1) }, 11);
        assert_eq!(unsafe { read(values.as_ptr().add(1), 1) }, 33);
    }
}

#[test]
fn gep_treats_true_as_signed_negative_one() {
    let source = r#"
func public %read(v0.*i64, v1.*i1) -> i64 {
block0:
    v2.i1 = mload v1 i1;
    v3.*i64 = gep v0 v2;
    v4.i64 = mload v3 i64;
    return v4;
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
        let read: unsafe extern "C" fn(*const i64, *const u8) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("read").unwrap()) };
        let values = [11i64, 22, 33];
        assert_eq!(unsafe { read(values.as_ptr().add(1), &1) }, 11);
        assert_eq!(unsafe { read(values.as_ptr().add(1), &0) }, 22);
    }
}

#[test]
fn undef_aggregates_read_as_zero_in_every_position() {
    let source = r#"
type @Big = {[i64; 40], i64};
func inline(never) private %ends(v0.[i64; 40]) -> i64 {
block0:
    v1.i64 = extract_value v0 0.i64;
    v2.i64 = extract_value v0 39.i64;
    v3.i64 = add v1 v2;
    return v3;
}
func public %read(v0.i1, v1.*[i64; 40], v2.*[i64; 40], v3.*i64) {
block0:
    v4.i64 = call %ends undef.[i64; 40];
    mstore v3 v4 i64;
    v5.[i64; 40] = extract_value undef.@Big 0.i64;
    mstore v1 v5 [i64; 40];
    br v0 block1 block2;
block1:
    jump block3;
block2:
    v6.[i64; 40] = mload v2 [i64; 40];
    jump block3;
block3:
    v7.[i64; 40] = phi (undef.[i64; 40] block1) (v6 block2);
    mstore v2 v7 [i64; 40];
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
        let read: unsafe extern "C" fn(bool, *mut i64, *mut i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("read").unwrap()) };
        for take_undef in [false, true] {
            let mut extracted = [-1i64; 40];
            let mut merged: [i64; 40] = std::array::from_fn(|i| i as i64 + 1);
            let original = merged;
            let mut sum = -1;
            unsafe {
                read(
                    take_undef,
                    extracted.as_mut_ptr(),
                    merged.as_mut_ptr(),
                    &mut sum,
                )
            };
            assert_eq!(sum, 0, "{level:?}");
            assert_eq!(extracted, [0; 40], "{level:?}");
            assert_eq!(
                merged,
                if take_undef { [0; 40] } else { original },
                "{level:?} {take_undef}"
            );
        }
    }
}

#[test]
fn shared_frame_slots_keep_live_views_loop_values_and_call_arguments() {
    // A loop temporary and a call result would reuse `v5`'s slot if its view
    // `v6`, live across the loop, did not keep it alive.
    let reverse: String = (0..32)
        .map(|index| {
            let source = if index == 0 {
                "undef.[i64; 32]".to_string()
            } else {
                format!("v{}", index * 2)
            };
            format!(
                "    v{}.i64 = extract_value v0 {}.i64;\n    v{}.[i64; 32] = insert_value {source} {index}.i64 v{};\n",
                index * 2 + 1,
                31 - index,
                index * 2 + 2,
                index * 2 + 1
            )
        })
        .collect();
    let source = format!(
        r#"
type @Big = {{[i64; 32], [i64; 32]}};
func inline(never) private %reverse(v0.[i64; 32]) -> [i64; 32] {{
block0:
{reverse}    return v64;
}}
func public %mix(v0.*@Big, v1.*@Big, v2.i64, v3.*[i64; 32], v4.*[i64; 32]) {{
block0:
    v5.@Big = mload v0 @Big;
    v6.[i64; 32] = extract_value v5 1.i64;
    v7.@Big = mload v1 @Big;
    v8.[i64; 32] = extract_value v7 0.i64;
    v9.[i64; 32] = call %reverse v8;
    jump block1;
block1:
    v10.[i64; 32] = phi (v9 block0) (v13 block1);
    v11.i64 = phi (0.i64 block0) (v14 block1);
    v12.@Big = mload v1 @Big;
    v13.[i64; 32] = call %reverse v10;
    v16.[i64; 32] = extract_value v12 1.i64;
    mstore v3 v16 [i64; 32];
    v14.i64 = add v11 1.i64;
    v15.i1 = lt v14 v2;
    br v15 block1 block2;
block2:
    mstore v3 v6 [i64; 32];
    mstore v4 v10 [i64; 32];
    return;
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
        .unwrap();
        let mix: unsafe extern "C" fn(*const i64, *const i64, i64, *mut i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("mix").unwrap()) };
        let first: Vec<i64> = (0..64).collect();
        let second: Vec<i64> = (0..64).map(|i| 1000 + i).collect();
        for count in [1, 2, 3] {
            let mut view = [0; 32];
            let mut carried = [0; 32];
            unsafe {
                mix(
                    first.as_ptr(),
                    second.as_ptr(),
                    count,
                    view.as_mut_ptr(),
                    carried.as_mut_ptr(),
                )
            };
            assert_eq!(view[..], first[32..], "{level:?} {count}");
            let mut expected = second[..32].to_vec();
            if count % 2 == 1 {
                expected.reverse();
            }
            assert_eq!(carried[..], expected[..], "{level:?} {count}");
        }
    }
}

#[test]
fn nested_insert_chains_zero_their_own_unwritten_fields() {
    // The inner chain `v3` becomes a field of the outer chain's continuation
    // `v4`. Only `v3`'s own inserts cover its storage, so it still zeroes
    // the array it leaves undef.
    let source = r#"
type @Inner = {i64, [i64; 20]};
type @Outer = {i64, i64, @Inner};
func public %nest(v0.i64, v1.*@Outer) {
block0:
    v2.@Outer = insert_value undef.@Outer 0.i64 v0;
    v3.@Inner = insert_value undef.@Inner 0.i64 v0;
    v4.@Outer = insert_value v2 2.i64 v3;
    v5.@Outer = insert_value v4 1.i64 v0;
    mstore v1 v5 @Outer;
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
        let nest: unsafe extern "C" fn(i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("nest").unwrap()) };
        let mut output = [-1i64; 23];
        unsafe { nest(9, output.as_mut_ptr()) };
        let mut expected = [0; 23];
        expected[..3].copy_from_slice(&[9, 9, 9]);
        assert_eq!(output, expected, "{level:?}");
    }
}
