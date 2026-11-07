use sonatina_codegen::{Compile, compile::OptLevel};
use sonatina_cranelift::CraneliftJitBackend;

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

#[test]
fn returned_aggregates_live_in_the_return_buffer() {
    // `either` builds both results before choosing one, so only one of them
    // can live in the return buffer. `forward` returns a call result and
    // `rotate` a loop phi, both stored in the buffer directly.
    let source = r#"
type @Pair = {[i64; 32], [i64; 32]};
func inline(never) private %either(v0.i1, v1.[i64; 32], v2.[i64; 32]) -> @Pair {
block0:
    v3.@Pair = insert_value undef.@Pair 0.i64 v1;
    v4.@Pair = insert_value v3 1.i64 v2;
    v5.@Pair = insert_value undef.@Pair 0.i64 v2;
    v6.@Pair = insert_value v5 1.i64 v1;
    br v0 block1 block2;
block1:
    return v4;
block2:
    return v6;
}
func inline(never) private %forward(v0.i1, v1.[i64; 32], v2.[i64; 32]) -> @Pair {
block0:
    v3.@Pair = call %either v0 v1 v2;
    return v3;
}
func inline(never) private %rotate(v0.@Pair, v1.i64) -> @Pair {
block0:
    jump block1;
block1:
    v2.@Pair = phi (v0 block0) (v7 block1);
    v3.i64 = phi (0.i64 block0) (v8 block1);
    v4.[i64; 32] = extract_value v2 0.i64;
    v5.[i64; 32] = extract_value v2 1.i64;
    v6.@Pair = insert_value undef.@Pair 0.i64 v5;
    v7.@Pair = insert_value v6 1.i64 v4;
    v8.i64 = add v3 1.i64;
    v9.i1 = lt v8 v1;
    br v9 block1 block2;
block2:
    return v2;
}
func public %run(v0.i1, v1.*[i64; 32], v2.*[i64; 32], v3.i64, v4.*@Pair, v5.*@Pair) {
block0:
    v6.[i64; 32] = mload v1 [i64; 32];
    v7.[i64; 32] = mload v2 [i64; 32];
    v8.@Pair = call %forward v0 v6 v7;
    mstore v4 v8 @Pair;
    v9.@Pair = call %rotate v8 v3;
    mstore v5 v9 @Pair;
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
        let run: unsafe extern "C" fn(bool, *const i64, *const i64, i64, *mut i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        let a: Vec<i64> = (0..32).collect();
        let b: Vec<i64> = (100..132).collect();
        for first in [false, true] {
            for count in [1, 2, 3] {
                let mut chosen = vec![0; 64];
                let mut rotated = vec![0; 64];
                unsafe {
                    run(
                        first,
                        a.as_ptr(),
                        b.as_ptr(),
                        count,
                        chosen.as_mut_ptr(),
                        rotated.as_mut_ptr(),
                    )
                };
                let (x, y) = if first { (&a, &b) } else { (&b, &a) };
                assert_eq!(chosen[..32], x[..], "{level:?} {first} {count}");
                assert_eq!(chosen[32..], y[..], "{level:?} {first} {count}");
                let (x, y) = if count % 2 == 1 { (x, y) } else { (y, x) };
                assert_eq!(rotated[..32], x[..], "{level:?} {first} {count}");
                assert_eq!(rotated[32..], y[..], "{level:?} {first} {count}");
            }
        }
    }
}

#[test]
fn single_use_loads_copy_from_memory_only_while_it_is_unchanged() {
    // `shift` stores a load over its own source, so the forwarded copy must
    // read every word first. `snapshot` and `rebuild` change the source
    // before a load's only use, and `wrap` calls a function that does, so
    // they keep a snapshot. `load` returns a load straight from memory.
    let source = r#"
type @Pair = {[i64; 32], [i64; 32]};
func inline(never) private %clobber(v0.*[i64; 32]) {
block0:
    mstore v0 undef.[i64; 32] [i64; 32];
    return;
}
func inline(never) private %load(v0.*[i64; 32]) -> [i64; 32] {
block0:
    v1.[i64; 32] = mload v0 [i64; 32];
    return v1;
}
func public %shift(v0.*[i64; 16]) {
block0:
    v1.[i64; 15] = mload v0 [i64; 15];
    v2.*i64 = gep v0 0.i64 1.i64;
    mstore v2 v1 [i64; 15];
    return;
}
func public %snapshot(v0.*[i64; 4], v1.*[i64; 4]) {
block0:
    v2.[i64; 4] = mload v0 [i64; 4];
    mstore v0 undef.[i64; 4] [i64; 4];
    mstore v1 v2 [i64; 4];
    return;
}
func public %rebuild(v0.*[i64; 4], v1.*[i64; 4], v2.*[i64; 4]) {
block0:
    v3.[i64; 4] = mload v0 [i64; 4];
    v4.[i64; 4] = insert_value v3 0.i64 9.i64;
    mstore v1 v4 [i64; 4];
    v5.[i64; 4] = mload v0 [i64; 4];
    mstore v0 undef.[i64; 4] [i64; 4];
    v6.[i64; 4] = insert_value v5 1.i64 9.i64;
    mstore v2 v6 [i64; 4];
    return;
}
func public %wrap(v0.*[i64; 32], v1.*@Pair) {
block0:
    v2.[i64; 32] = call %load v0;
    v3.@Pair = insert_value undef.@Pair 1.i64 v2;
    v4.[i64; 32] = mload v0 [i64; 32];
    call %clobber v0;
    v5.@Pair = insert_value v3 0.i64 v4;
    mstore v1 v5 @Pair;
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
        let shift: unsafe extern "C" fn(*mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("shift").unwrap()) };
        let mut words: [i64; 16] = std::array::from_fn(|i| i as i64 + 1);
        unsafe { shift(words.as_mut_ptr()) };
        let shifted: [i64; 15] = std::array::from_fn(|i| i as i64 + 1);
        assert_eq!(words[0], 1, "{level:?}");
        assert_eq!(words[1..], shifted, "{level:?}");

        let snapshot: unsafe extern "C" fn(*mut i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("snapshot").unwrap()) };
        let mut source_words = [5i64, 6, 7, 8];
        let mut copy = [0i64; 4];
        unsafe { snapshot(source_words.as_mut_ptr(), copy.as_mut_ptr()) };
        assert_eq!(source_words, [0; 4], "{level:?}");
        assert_eq!(copy, [5, 6, 7, 8], "{level:?}");

        let rebuild: unsafe extern "C" fn(*mut i64, *mut i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("rebuild").unwrap()) };
        let mut source_words = [5i64, 6, 7, 8];
        let (mut first, mut second) = ([0i64; 4], [0i64; 4]);
        unsafe {
            rebuild(
                source_words.as_mut_ptr(),
                first.as_mut_ptr(),
                second.as_mut_ptr(),
            )
        };
        assert_eq!(source_words, [0; 4], "{level:?}");
        assert_eq!(first, [9, 6, 7, 8], "{level:?}");
        assert_eq!(second, [5, 9, 7, 8], "{level:?}");

        let wrap: unsafe extern "C" fn(*mut i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("wrap").unwrap()) };
        let original: Vec<i64> = (1..=32).collect();
        let mut memory = original.clone();
        let mut pair = vec![0; 64];
        unsafe { wrap(memory.as_mut_ptr(), pair.as_mut_ptr()) };
        assert_eq!(memory, [0; 32], "{level:?}");
        assert_eq!(pair[..32], original[..], "{level:?}");
        assert_eq!(pair[32..], original[..], "{level:?}");
    }
}

#[test]
fn memory_copies_may_overlap() {
    // `copy_short` stays inline; `copy` calls `memmove`, as its length is
    // dynamic.
    let source = r#"
func public %copy(v0.*i8, v1.*i8, v2.i64) {
block0:
    memcopy v0 v1 v2;
    return;
}
func public %copy_short(v0.*i8, v1.*i8) {
block0:
    memcopy v0 v1 100.i64;
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
        let copy: unsafe extern "C" fn(*mut u8, *const u8, i64) =
            unsafe { std::mem::transmute(artifact.function_address("copy").unwrap()) };
        let copy_short: unsafe extern "C" fn(*mut u8, *const u8) =
            unsafe { std::mem::transmute(artifact.function_address("copy_short").unwrap()) };
        for (dest, src, len, short) in [
            (0, 7, 100, true),
            (7, 0, 100, true),
            (40, 41, 100, true),
            (3, 9, 0, false),
            (0, 7, 100, false),
            (7, 0, 100, false),
            (0, 300, 300, false),
            (300, 0, 300, false),
            (13, 5, 500, false),
        ] {
            let mut bytes: Vec<u8> = (0..1000).map(|i| (i * 7 + 3) as u8).collect();
            let mut expected = bytes.clone();
            expected.copy_within(src..src + len, dest);
            let base = bytes.as_mut_ptr();
            unsafe {
                if short {
                    copy_short(base.add(dest), base.add(src));
                } else {
                    copy(base.add(dest), base.add(src), len as i64);
                }
            }
            assert_eq!(bytes, expected, "{level:?} {dest} {src} {len}");
        }
    }
}

#[test]
fn field_wise_copies_keep_fields_and_zero_padding() {
    // Copies split at narrow fields and overlapping enum payloads, and write
    // zeros to padding. Each copy kind passes the values on: `mload`, phis,
    // object stores and loads, returns and `mstore`. Both types have too many
    // fields to be held in registers.
    let source = r#"
type @Mixed = { i1, i32, i16, i64, i8 };
type @Choice = enum { #Byte(i8), #Word(i64), #Flag(i1, i32) };
func private %pass(v0.@Choice) -> @Choice {
block0:
    return v0;
}
func public %copy(v0.*@Mixed, v1.*@Mixed, v20.*i8, v30.*i8, v4.i64) {
block0:
    v2.*@Choice = bitcast v20 *@Choice;
    v3.*@Choice = bitcast v30 *@Choice;
    v5.@Mixed = mload v0 @Mixed;
    v6.@Choice = mload v2 @Choice;
    jump block1;
block1:
    v7.@Mixed = phi (v5 block0) (v11 block1);
    v8.@Choice = phi (v6 block0) (v12 block1);
    v9.i64 = phi (v4 block0) (v13 block1);
    v10.objref<@Mixed> = obj.alloc @Mixed;
    obj.store v10 v7;
    v11.@Mixed = obj.load v10;
    v12.@Choice = call %pass v8;
    v13.i64 = sub v9 1.i64;
    v14.i1 = gt v13 0.i64;
    br v14 block1 block2;
block2:
    mstore v1 v11 @Mixed;
    mstore v3 v12 @Choice;
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
        let copy: unsafe extern "C" fn(*const u8, *mut u8, *const u8, *mut u8, i64) =
            unsafe { std::mem::transmute(artifact.function_address("copy").unwrap()) };
        // `@Mixed`: i1 at 0, i32 at 4, i16 at 8, i64 at 16, i8 at 24.
        // `@Choice`: an i8 tag, then payloads from 8: `#Flag`'s i1 at 8 and
        // i32 at 12.
        let mut mixed: [u8; 32] = std::array::from_fn(|i| (i * 37 + 11) as u8);
        mixed[0] = 1;
        let mut choice: [u8; 16] = std::array::from_fn(|i| (i * 53 + 5) as u8);
        choice[0] = 2;
        choice[8] = 1;
        let mut expected_mixed = mixed;
        expected_mixed[1..4].fill(0);
        expected_mixed[10..16].fill(0);
        expected_mixed[25..32].fill(0);
        let mut expected_choice = choice;
        expected_choice[1..8].fill(0);
        for rounds in [1, 3] {
            let (mut mixed_out, mut choice_out) = ([0xa5u8; 32], [0xa5u8; 16]);
            unsafe {
                copy(
                    mixed.as_ptr(),
                    mixed_out.as_mut_ptr(),
                    choice.as_ptr(),
                    choice_out.as_mut_ptr(),
                    rounds,
                )
            };
            assert_eq!(mixed_out, expected_mixed, "{level:?} {rounds}");
            assert_eq!(choice_out, expected_choice, "{level:?} {rounds}");
        }
    }
}

#[test]
fn narrow_enum_fields_fill_the_piece_a_wider_variant_shares() {
    // `#Flag`, `#Wrapped` and `#Pair`'s i32 fill the word `#Word` holds at 8, so
    // a word load forwards from their stores. `#Two` has two fields in the word
    // of `@Split`, which keeps them apart. Each writes over stale bytes, which
    // the rest of the piece must not keep, and fields next to it must survive.
    let source = r#"
type @Wrap = { i1 };
type @Value = enum { #Flag(i1), #Wrapped(@Wrap), #Word(i64), #Pair(i32, i64) };
type @Split = enum { #Two(i8, i8), #Word(i64) };
type @Large = enum { #Flag(i1), #Words([i64; 32]) };
func private %pass(v0.@Value) -> @Value {
block0:
    return v0;
}
func public %write_flag(v0.*i8, v1.i1) {
block0:
    v2.*@Value = bitcast v0 *@Value;
    v3.objref<@Value> = obj.from_ptr v2;
    enum.write_variant v3 #Flag (v1);
    return;
}
func public %write_wrapped(v0.*i8, v1.i1) {
block0:
    v2.*@Value = bitcast v0 *@Value;
    v3.objref<@Value> = obj.from_ptr v2;
    v4.@Wrap = insert_value undef.@Wrap 0.i256 v1;
    enum.write_variant v3 #Wrapped (v4);
    return;
}
func public %write_pair(v0.*i8, v1.i32, v2.i64) {
block0:
    v3.*@Value = bitcast v0 *@Value;
    v4.objref<@Value> = obj.from_ptr v3;
    enum.write_variant v4 #Pair (v1, v2);
    return;
}
func public %write_two(v0.*i8, v1.i8, v2.i8) {
block0:
    v3.*@Split = bitcast v0 *@Split;
    v4.objref<@Split> = obj.from_ptr v3;
    enum.write_variant v4 #Two (v1, v2);
    return;
}
func public %write_large(v0.*i8, v1.i1) {
block0:
    v2.*@Large = bitcast v0 *@Large;
    v3.objref<@Large> = obj.from_ptr v2;
    enum.write_variant v3 #Flag (v1);
    return;
}
func public %copy_flag(v0.*i8, v1.i1) -> i1 {
block0:
    v2.*@Value = bitcast v0 *@Value;
    v3.@Value = enum.make @Value #Flag v1;
    v4.@Value = call %pass v3;
    mstore v2 v4 @Value;
    enum.assert_variant v4 #Flag;
    v5.i1 = enum.extract v4 #Flag 0.i256;
    return v5;
}
func public %read_word(v0.*i8) -> i64 {
block0:
    v1.*@Value = bitcast v0 *@Value;
    v2.@Value = mload v1 @Value;
    v3.@Value = call %pass v2;
    enum.assert_variant v3 #Word;
    v4.i64 = enum.extract v3 #Word 0.i256;
    return v4;
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
        let address = |name| artifact.function_address(name).unwrap();
        let write_flag: unsafe extern "C" fn(*mut u8, bool) =
            unsafe { std::mem::transmute(address("write_flag")) };
        let write_wrapped: unsafe extern "C" fn(*mut u8, bool) =
            unsafe { std::mem::transmute(address("write_wrapped")) };
        let write_pair: unsafe extern "C" fn(*mut u8, i32, i64) =
            unsafe { std::mem::transmute(address("write_pair")) };
        let write_two: unsafe extern "C" fn(*mut u8, i8, i8) =
            unsafe { std::mem::transmute(address("write_two")) };
        let write_large: unsafe extern "C" fn(*mut u8, bool) =
            unsafe { std::mem::transmute(address("write_large")) };
        let copy_flag: unsafe extern "C" fn(*mut u8, bool) -> bool =
            unsafe { std::mem::transmute(address("copy_flag")) };
        let read_word: unsafe extern "C" fn(*const u8) -> i64 =
            unsafe { std::mem::transmute(address("read_word")) };

        // An i8 tag at 0, then payloads from 8. A write leaves the padding,
        // and every piece no field of its variant lies in.
        let stale = [0xa5u8; 24];
        let word =
            |bytes: &[u8; 24], at: usize| u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap());
        let mut value = stale;
        unsafe { write_flag(value.as_mut_ptr(), true) };
        assert_eq!(value[0], 0, "{level:?}");
        assert_eq!(value[1..8], stale[1..8], "{level:?}");
        assert_eq!(word(&value, 8), 1, "{level:?}");
        assert_eq!(value[16..], stale[16..], "{level:?}");

        let mut value = stale;
        unsafe { write_wrapped(value.as_mut_ptr(), true) };
        assert_eq!(value[0], 1, "{level:?}");
        assert_eq!(word(&value, 8), 1, "{level:?}");
        assert_eq!(value[16..], stale[16..], "{level:?}");

        let mut value = stale;
        unsafe { write_pair(value.as_mut_ptr(), -2, 0x1122_3344_5566_7788) };
        assert_eq!(value[0], 3, "{level:?}");
        assert_eq!(word(&value, 8), 0xffff_fffe, "{level:?}");
        assert_eq!(word(&value, 16), 0x1122_3344_5566_7788, "{level:?}");

        let mut split = [0xa5u8; 16];
        unsafe { write_two(split.as_mut_ptr(), 7, 9) };
        assert_eq!(split[8..10], [7, 9], "{level:?}");
        assert_eq!(split[10..], [0xa5; 6], "{level:?}");

        // A copy of `@Large` calls `memcpy`, so its field stays narrow.
        let mut large = [0xa5u8; 264];
        unsafe { write_large(large.as_mut_ptr(), true) };
        assert_eq!(large[8..10], [1, 0xa5], "{level:?}");

        // Copies keep both widths: the narrow field and the word it fills.
        for flag in [false, true] {
            let mut value = stale;
            assert_eq!(
                unsafe { copy_flag(value.as_mut_ptr(), flag) },
                flag,
                "{level:?}"
            );
            assert_eq!(value[0], 0, "{level:?}");
            assert_eq!(value[1..8], [0; 7], "{level:?}");
            assert_eq!(word(&value, 8), u64::from(flag), "{level:?}");
        }
        let mut wide = [0u8; 24];
        wide[0] = 2;
        wide[8..16].copy_from_slice(&0x0102_0304_0506_0708u64.to_le_bytes());
        assert_eq!(
            unsafe { read_word(wide.as_ptr()) },
            0x0102_0304_0506_0708,
            "{level:?}"
        );
    }
}

#[test]
fn objects_move_into_and_out_of_calls_without_copies() {
    // `%fill`'s result goes straight into `v1` and `%sum` reads `v1` itself;
    // `%clobber` writes the object it is also passed a copy of, `%swap`
    // reads the object its result is stored into, and `%replaced` reads the
    // old object between a call and the store of its result, as
    // `mem::replace` does, so all three keep copies.
    let source = r#"
func inline(never) private %fill(v0.i64) -> [i64; 32] {
block0:
    v1.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v2.i64 = add v0 1.i64;
    v3.[i64; 32] = insert_value v1 31.i64 v2;
    return v3;
}
func inline(never) private %sum(v0.[i64; 32]) -> i64 {
block0:
    v1.i64 = extract_value v0 0.i64;
    v2.i64 = extract_value v0 31.i64;
    v3.i64 = add v1 v2;
    return v3;
}
func inline(never) private %clobber(v0.[i64; 32], noalias nocapture v1.objref<[i64; 32]>) -> i64 {
block0:
    v2.objref<i64> = obj.index v1 0.i64;
    obj.store v2 99.i64;
    v3.i64 = extract_value v0 0.i64;
    return v3;
}
func inline(never) private %swap(noalias nocapture v0.objref<[i64; 32]>) -> [i64; 32] {
block0:
    v1.objref<i64> = obj.index v0 0.i64;
    v2.i64 = obj.load v1;
    v3.objref<i64> = obj.index v0 31.i64;
    v4.i64 = obj.load v3;
    v5.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v4;
    v6.[i64; 32] = insert_value v5 31.i64 v2;
    return v6;
}
func public %roundtrip(v0.i64) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    v2.[i64; 32] = call %fill v0;
    obj.store v1 v2;
    v3.[i64; 32] = obj.load v1;
    v4.i64 = call %sum v3;
    return v4;
}
func public %replaced(v0.i64) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    v2.[i64; 32] = call %fill v0;
    obj.store v1 v2;
    v3.[i64; 32] = call %fill 1000.i64;
    v4.[i64; 32] = obj.load v1;
    obj.store v1 v3;
    v5.i64 = extract_value v4 0.i64;
    v6.objref<i64> = obj.index v1 0.i64;
    v7.i64 = obj.load v6;
    v8.i64 = mul v7 1000.i64;
    v9.i64 = add v5 v8;
    return v9;
}
func public %aliased(v0.i64) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    v2.[i64; 32] = call %fill v0;
    obj.store v1 v2;
    v3.[i64; 32] = obj.load v1;
    v4.i64 = call %clobber v3 v1;
    v5.[i64; 32] = call %swap v1;
    obj.store v1 v5;
    v6.[i64; 32] = obj.load v1;
    v7.i64 = extract_value v6 0.i64;
    v8.i64 = extract_value v6 31.i64;
    v9.i64 = mul v8 1000.i64;
    v10.i64 = add v4 v9;
    v11.i64 = mul v7 1000000.i64;
    v12.i64 = add v10 v11;
    return v12;
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
        let roundtrip: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("roundtrip").unwrap()) };
        let aliased: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("aliased").unwrap()) };
        let replaced: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("replaced").unwrap()) };
        for value in [0, 5, -7, 1 << 40] {
            assert_eq!(unsafe { roundtrip(value) }, 2 * value + 1, "{level:?}");
            // `%clobber` sees the value before its own write; `%swap` reads
            // the old elements, 99 and value + 1, before its result lands.
            let expected = value + (99 * 1000) + (value + 1) * 1_000_000;
            assert_eq!(unsafe { aliased(value) }, expected, "{level:?}");
            assert_eq!(unsafe { replaced(value) }, value + 1000 * 1000, "{level:?}");
        }
    }
}

#[test]
fn callees_rebuild_objects_in_entry_blocks_that_loop() {
    // `%passes` initializes an object from its argument at the top of its
    // entry block, which it branches back to, and reads an element of the
    // argument before that. Each pass starts from the argument's value, so it
    // cannot build the object in the argument's storage.
    let source = r#"
func inline(never) private %fill(v0.i64) -> [i64; 32] {
block0:
    v1.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v2.[i64; 32] = insert_value v1 31.i64 v0;
    return v2;
}
func inline(never) private %passes(v0.[i64; 32], noalias nocapture v1.objref<[i64; 2]>) -> i64 {
block0:
    v2.i64 = extract_value v0 0.i64;
    v3.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v3 v0;
    v4.objref<i64> = obj.index v3 0.i64;
    v5.i64 = obj.load v4;
    v6.i64 = add v5 1.i64;
    obj.store v4 v6;
    v7.objref<i64> = obj.index v1 1.i64;
    v8.i64 = obj.load v7;
    v9.i64 = add v8 v2;
    obj.store v7 v9;
    v10.objref<i64> = obj.index v1 0.i64;
    v11.i64 = obj.load v10;
    v12.i64 = sub v11 1.i64;
    obj.store v10 v12;
    v13.i1 = eq v12 0.i64;
    br v13 block1 block0;
block1:
    v14.i64 = obj.load v4;
    v15.i64 = mul v9 1000.i64;
    v16.i64 = add v14 v15;
    return v16;
}
func public %looped(v0.i64) -> i64 {
block0:
    v1.[i64; 32] = call %fill v0;
    v2.objref<[i64; 2]> = obj.alloc [i64; 2];
    v3.objref<i64> = obj.index v2 0.i64;
    obj.store v3 3.i64;
    v4.objref<i64> = obj.index v2 1.i64;
    obj.store v4 0.i64;
    v5.i64 = call %passes v1 v2;
    return v5;
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
        let looped: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("looped").unwrap()) };
        for value in [0, 5, -7, 1000] {
            // Three passes each read element 0 as `value` and leave the
            // object's element 0 at `value + 1`.
            assert_eq!(
                unsafe { looped(value) },
                value + 1 + 3 * value * 1000,
                "{level:?}"
            );
        }
    }
}

#[test]
fn callees_build_objects_in_arguments_they_own() {
    // `%consume` and `%consume2` build their objects in their arguments'
    // storage and overwrite them. Callers give up a value or object they do
    // not use afterwards and copy the rest: `%kept` reads its value after
    // the call, `%reused` its object, and `%twice` passes one value twice.
    let source = r#"
func inline(never) private %fill(v0.i64) -> [i64; 32] {
block0:
    v1.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v2.[i64; 32] = insert_value v1 31.i64 v0;
    return v2;
}
func inline(never) private %consume(v0.[i64; 32]) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v1 v0;
    v2.objref<i64> = obj.index v1 0.i64;
    v3.i64 = obj.load v2;
    v4.i64 = add v3 100.i64;
    obj.store v2 v4;
    v5.objref<i64> = obj.index v1 31.i64;
    obj.store v5 0.i64;
    v6.i64 = obj.load v2;
    return v6;
}
func inline(never) private %consume2(v0.[i64; 32], v1.[i64; 32]) -> i64 {
block0:
    v2.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v2 v0;
    v3.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v3 v1;
    v4.objref<i64> = obj.index v2 0.i64;
    obj.store v4 7.i64;
    v5.objref<i64> = obj.index v3 0.i64;
    v6.i64 = obj.load v5;
    return v6;
}
func inline(never) private %peek_first(v0.[i64; 32]) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v1 v0;
    v2.i64 = extract_value v0 31.i64;
    v3.objref<i64> = obj.index v1 31.i64;
    obj.store v3 0.i64;
    v4.i64 = obj.load v3;
    v5.i64 = add v2 v4;
    return v5;
}
func inline(never) private %peek_late(v0.[i64; 32]) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v1 v0;
    v2.objref<i64> = obj.index v1 31.i64;
    obj.store v2 0.i64;
    v3.i64 = extract_value v0 31.i64;
    return v3;
}
func public %peeks(v0.i64) -> i64 {
block0:
    v1.[i64; 32] = call %fill v0;
    v2.i64 = call %peek_first v1;
    v3.[i64; 32] = call %fill v0;
    v4.i64 = call %peek_late v3;
    v5.i64 = mul v4 1000.i64;
    v6.i64 = add v2 v5;
    return v6;
}
func public %given(v0.i64) -> i64 {
block0:
    v1.[i64; 32] = call %fill v0;
    v2.i64 = call %consume v1;
    return v2;
}
func public %kept(v0.i64) -> i64 {
block0:
    v1.[i64; 32] = call %fill v0;
    v2.i64 = call %consume v1;
    v3.i64 = extract_value v1 0.i64;
    v4.i64 = extract_value v1 31.i64;
    v5.i64 = add v2 v3;
    v6.i64 = add v5 v4;
    return v6;
}
func public %reused(v0.i64) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    v2.[i64; 32] = call %fill v0;
    obj.store v1 v2;
    v3.[i64; 32] = obj.load v1;
    v4.i64 = call %consume v3;
    v5.objref<i64> = obj.index v1 31.i64;
    v6.i64 = obj.load v5;
    v7.i64 = add v4 v6;
    return v7;
}
func public %twice(v0.i64) -> i64 {
block0:
    v1.[i64; 32] = call %fill v0;
    v2.i64 = call %consume2 v1 v1;
    return v2;
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
        let function = |name| -> unsafe extern "C" fn(i64) -> i64 {
            unsafe { std::mem::transmute(artifact.function_address(name).unwrap()) }
        };
        for value in [0, 5, -7, 1 << 40] {
            unsafe {
                assert_eq!(function("given")(value), value + 100, "{level:?}");
                assert_eq!(
                    function("kept")(value),
                    value + 100 + 2 * value,
                    "{level:?}"
                );
                assert_eq!(function("reused")(value), value + 100 + value, "{level:?}");
                assert_eq!(function("twice")(value), value, "{level:?}");
                // Each reads its argument's field 31, `value`, before or
                // after zeroing its object's.
                assert_eq!(function("peeks")(value), value + value * 1000, "{level:?}");
            }
        }
    }
}

#[test]
fn in_place_loads_keep_snapshots_of_objects_given_away() {
    // `%consume`, `%consume_read` and `%consume_pair` own their first
    // argument and overwrite an element of it at the index they are passed,
    // so a caller that gives one a load of a local object it no longer uses
    // gives it the object's storage. Other loads of the object keep their
    // snapshots: in `%around`, loads before and after the given one; in
    // `%same_call`, one passed to the same call; in `%sub_object`, a load of
    // the whole object before a row of it is given in another block; and in
    // `%row`, a load of a row before the whole object is given, which
    // survives optimization.
    let source = r#"
func inline(never) private %fill(v0.i64) -> [i64; 32] {
block0:
    v1.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v2.i64 = add v0 1.i64;
    v3.[i64; 32] = insert_value v1 31.i64 v2;
    return v3;
}
func inline(never) private %consume(v0.[i64; 32], v1.i64) -> i64 {
block0:
    v2.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v2 v0;
    v3.objref<i64> = obj.index v2 v1;
    obj.store v3 99.i64;
    v4.i64 = add v1 31.i64;
    v5.objref<i64> = obj.index v2 v4;
    v6.i64 = obj.load v5;
    return v6;
}
func inline(never) private %consume_read(v0.[i64; 32], v1.[i64; 32], v2.i64) -> i64 {
block0:
    v3.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v3 v0;
    v4.objref<i64> = obj.index v3 v2;
    obj.store v4 99.i64;
    v5.i64 = extract_value v1 0.i64;
    return v5;
}
func inline(never) private %consume_pair(v0.[[i64; 32]; 2], v1.i64) -> i64 {
block0:
    v2.objref<[[i64; 32]; 2]> = obj.alloc [[i64; 32]; 2];
    obj.store v2 v0;
    v3.objref<[i64; 32]> = obj.index v2 v1;
    v4.objref<i64> = obj.index v3 v1;
    obj.store v4 99.i64;
    v5.i64 = add v1 31.i64;
    v6.objref<i64> = obj.index v3 v5;
    v7.i64 = obj.load v6;
    return v7;
}
func inline(never) private %init(noalias nocapture v0.objref<[[i64; 32]; 2]>, v1.i64) {
block0:
    v2.[i64; 32] = call %fill v1;
    v3.objref<[i64; 32]> = obj.index v0 0.i64;
    obj.store v3 v2;
    v4.objref<[i64; 32]> = obj.index v0 1.i64;
    obj.store v4 v2;
    return;
}
func inline(never) private %reader(noalias nocapture v0.objref<[[i64; 32]; 2]>, v1.i64) -> i64 {
block0:
    v2.objref<[i64; 32]> = obj.index v0 v1;
    v3.objref<i64> = obj.index v2 0.i64;
    v4.i64 = obj.load v3;
    return v4;
}
func public %around(v0.i64, v1.i64) -> i64 {
block0:
    v2.objref<[i64; 32]> = obj.alloc [i64; 32];
    v3.[i64; 32] = call %fill v0;
    obj.store v2 v3;
    v4.[i64; 32] = obj.load v2;
    v5.[i64; 32] = obj.load v2;
    v6.[i64; 32] = obj.load v2;
    v7.i64 = call %consume v5 v1;
    v8.i64 = extract_value v4 0.i64;
    v9.i64 = extract_value v6 0.i64;
    v10.i64 = mul v8 1000.i64;
    v11.i64 = mul v9 1000000.i64;
    v12.i64 = add v7 v10;
    v13.i64 = add v12 v11;
    return v13;
}
func public %same_call(v0.i64, v1.i64) -> i64 {
block0:
    v2.objref<[i64; 32]> = obj.alloc [i64; 32];
    v3.[i64; 32] = call %fill v0;
    obj.store v2 v3;
    v4.[i64; 32] = obj.load v2;
    v5.[i64; 32] = obj.load v2;
    v6.i64 = call %consume_read v5 v4 v1;
    v7.i64 = extract_value v4 31.i64;
    v8.i64 = mul v7 1000.i64;
    v9.i64 = add v6 v8;
    return v9;
}
func public %sub_object(v0.i64, v1.i64) -> i64 {
block0:
    v2.objref<[[i64; 32]; 2]> = obj.alloc [[i64; 32]; 2];
    v3.[i64; 32] = call %fill v0;
    v4.objref<[i64; 32]> = obj.index v2 0.i64;
    obj.store v4 v3;
    v5.objref<[i64; 32]> = obj.index v2 1.i64;
    obj.store v5 v3;
    v6.[[i64; 32]; 2] = obj.load v2;
    v7.i1 = slt v0 100.i64;
    br v7 block1 block2;
block1:
    v8.objref<[i64; 32]> = obj.index v2 0.i64;
    v9.[i64; 32] = obj.load v8;
    v10.i64 = call %consume v9 v1;
    jump block2;
block2:
    v11.i64 = phi (0.i64 block0) (v10 block1);
    v12.[i64; 32] = extract_value v6 0.i64;
    v13.i64 = extract_value v12 0.i64;
    v14.i64 = mul v13 1000.i64;
    v15.i64 = add v11 v14;
    return v15;
}
func public %row(v0.i64, v1.i64) -> i64 {
block0:
    v2.objref<[[i64; 32]; 2]> = obj.alloc [[i64; 32]; 2];
    call %init v2 v0;
    v3.objref<[i64; 32]> = obj.index v2 v1;
    v4.[i64; 32] = obj.load v3;
    v5.i64 = call %reader v2 v1;
    v6.[[i64; 32]; 2] = obj.load v2;
    v7.i64 = call %consume_pair v6 v1;
    v8.i64 = extract_value v4 0.i64;
    v9.i64 = mul v8 1000.i64;
    v10.i64 = mul v5 1000000.i64;
    v11.i64 = add v7 v9;
    v12.i64 = add v11 v10;
    return v12;
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
        let function = |name| -> unsafe extern "C" fn(i64, i64) -> i64 {
            unsafe { std::mem::transmute(artifact.function_address(name).unwrap()) }
        };
        for value in [0, 5, -7, 1000] {
            // At index 0, each call overwrites element 0 of what it is given
            // and returns element 31, `value + 1`, but `%consume_read`
            // returns its second argument's element 0.
            let given = if value < 100 { value + 1 } else { 0 };
            unsafe {
                assert_eq!(
                    function("around")(value, 0),
                    value + 1 + value * 1000 + value * 1_000_000,
                    "{level:?}"
                );
                assert_eq!(
                    function("same_call")(value, 0),
                    value + (value + 1) * 1000,
                    "{level:?}"
                );
                assert_eq!(
                    function("sub_object")(value, 0),
                    given + value * 1000,
                    "{level:?}"
                );
                assert_eq!(
                    function("row")(value, 0),
                    value + 1 + value * 1000 + value * 1_000_000,
                    "{level:?}"
                );
            }
        }
    }
}

#[test]
fn loads_read_local_objects_in_place_until_written() {
    // `%keep` loads its object, calls a function that cannot reach it, and
    // returns the load: it reads the object in place. `%clobbered` writes
    // its object after the load, so the load keeps its snapshot.
    let source = r#"
func inline(never) private %fill(v0.i64) -> [i64; 32] {
block0:
    v1.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v2.[i64; 32] = insert_value v1 31.i64 v0;
    return v2;
}
func inline(never) private %noise(v0.i64) -> i64 {
block0:
    v1.i64 = mul v0 3.i64;
    return v1;
}
func inline(never) private %keep(v0.i64, v1.i1) -> [i64; 32] {
block0:
    v2.objref<[i64; 32]> = obj.alloc [i64; 32];
    v3.[i64; 32] = call %fill v0;
    obj.store v2 v3;
    v4.[i64; 32] = obj.load v2;
    v5.i64 = call %noise v0;
    br v1 block1 block2;
block1:
    v6.[i64; 32] = insert_value v4 1.i64 v5;
    return v6;
block2:
    return v4;
}
func inline(never) private %clobbered(v0.i64) -> [i64; 32] {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    v2.[i64; 32] = call %fill v0;
    obj.store v1 v2;
    v3.[i64; 32] = obj.load v1;
    v4.objref<i64> = obj.index v1 0.i64;
    obj.store v4 77.i64;
    v5.i64 = obj.load v4;
    v6.[i64; 32] = insert_value v3 1.i64 v5;
    return v6;
}
func public %sums(v0.i64, v1.i1) -> i64 {
block0:
    v2.[i64; 32] = call %keep v0 v1;
    v3.i64 = extract_value v2 0.i64;
    v4.i64 = extract_value v2 1.i64;
    v5.i64 = extract_value v2 31.i64;
    v6.[i64; 32] = call %clobbered v0;
    v7.i64 = extract_value v6 0.i64;
    v8.i64 = extract_value v6 1.i64;
    v9.i64 = mul v4 1000.i64;
    v10.i64 = mul v7 1000000.i64;
    v11.i64 = mul v8 1000000000.i64;
    v12.i64 = add v3 v5;
    v13.i64 = add v12 v9;
    v14.i64 = add v13 v10;
    v15.i64 = add v14 v11;
    return v15;
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
        let sums: unsafe extern "C" fn(i64, bool) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("sums").unwrap()) };
        for value in [0, 5, -7, 1000] {
            for branch in [false, true] {
                // `%clobbered`'s snapshot keeps element 0 at `value` and
                // takes 77 into element 1.
                let noise = if branch { 3 * value } else { 0 };
                let expected = 2 * value + noise * 1000 + value * 1_000_000 + 77 * 1_000_000_000;
                assert_eq!(
                    unsafe { sums(value, branch) },
                    expected,
                    "{level:?} {branch}"
                );
            }
        }
    }
}

#[test]
fn read_only_objects_share_storage_until_a_callee_may_write() {
    // `%reader` only reads through its argument and `%writer` writes
    // element 0. `%read_only`'s object never changes, so it lives in its
    // argument's storage, and `%in_place` reads its argument in place;
    // `%written` and `%snapshot` keep copies their writers cannot change.
    let source = r#"
func inline(never) private %fill(v0.i64) -> [i64; 32] {
block0:
    v1.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    v2.i64 = add v0 3.i64;
    v3.[i64; 32] = insert_value v1 3.i64 v2;
    return v3;
}
func inline(never) private %reader(noalias nocapture v0.objref<[i64; 32]>) -> i64 {
block0:
    v1.objref<i64> = obj.index v0 3.i64;
    v2.i64 = obj.load v1;
    return v2;
}
func inline(never) private %writer(noalias nocapture v0.objref<[i64; 32]>) -> i64 {
block0:
    v1.objref<i64> = obj.index v0 0.i64;
    obj.store v1 55.i64;
    return 0.i64;
}
func inline(never) private %read_only(v0.[i64; 32]) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v1 v0;
    v2.i64 = call %reader v1;
    v3.objref<i64> = obj.index v1 0.i64;
    v4.i64 = obj.load v3;
    v5.i64 = add v2 v4;
    return v5;
}
func inline(never) private %written(v0.[i64; 32]) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v1 v0;
    v2.i64 = call %writer v1;
    v3.i64 = extract_value v0 0.i64;
    v4.objref<i64> = obj.index v1 0.i64;
    v5.i64 = obj.load v4;
    v6.i64 = mul v5 1000.i64;
    v7.i64 = add v3 v6;
    return v7;
}
func inline(never) private %in_place(noalias nocapture v0.objref<[i64; 32]>) -> i64 {
block0:
    v1.[i64; 32] = obj.load v0;
    v2.i64 = call %reader v0;
    v3.i64 = extract_value v1 0.i64;
    v4.i64 = add v2 v3;
    return v4;
}
func inline(never) private %snapshot(noalias nocapture v0.objref<[i64; 32]>) -> i64 {
block0:
    v1.[i64; 32] = obj.load v0;
    v2.i64 = call %writer v0;
    v3.i64 = extract_value v1 0.i64;
    return v3;
}
func public %run(v0.i64) -> i64 {
block0:
    v1.[i64; 32] = call %fill v0;
    v2.i64 = call %read_only v1;
    v3.i64 = call %written v1;
    v4.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v4 v1;
    v5.i64 = call %in_place v4;
    v6.i64 = call %snapshot v4;
    v7.objref<i64> = obj.index v4 0.i64;
    v8.i64 = obj.load v7;
    v9.i64 = mul v3 1000.i64;
    v10.i64 = mul v5 10000000.i64;
    v11.i64 = add v2 v9;
    v12.i64 = add v11 v10;
    v13.i64 = mul v6 3.i64;
    v14.i64 = add v12 v13;
    v15.i64 = mul v8 7.i64;
    v16.i64 = add v14 v15;
    return v16;
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
        let run: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        for value in [0, 5, -7, 100] {
            let read_only = (value + 3) + value;
            let written = value + 55 * 1000;
            let in_place = (value + 3) + value;
            // `%snapshot` saw element 0 before `%writer` set it to 55.
            let expected = read_only + written * 1000 + in_place * 10_000_000 + value * 3 + 55 * 7;
            assert_eq!(unsafe { run(value) }, expected, "{level:?}");
        }
    }
}
