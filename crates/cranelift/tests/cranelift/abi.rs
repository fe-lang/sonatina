use sonatina_codegen::{Compile, compile::OptLevel};
use sonatina_cranelift::CraneliftJitBackend;

use super::parse_verified_native_module;

#[test]
fn direct_i128_arguments_returns_and_internal_calls_preserve_both_words() {
    let source = include_str!("../../test_files/i128_abi.sntn");
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap();
        // Six i128 arguments exhaust the argument registers on both supported
        // hosts, exercising stack arguments as well as the two-word return.
        let mix: unsafe extern "C" fn(i128, i128, i128, i128, i128, i128) -> i128 =
            unsafe { std::mem::transmute(artifact.function_address("mix").unwrap()) };
        let via_pointers: unsafe extern "C" fn(*const i128, *mut i128) =
            unsafe { std::mem::transmute(artifact.function_address("via_pointers").unwrap()) };
        for inputs in [
            [1, 2, 3, 4, 5, 6],
            [i128::MIN, i128::MAX, -1, 1 << 96, -(1 << 80), 1 << 64],
            [i128::MAX, i128::MIN, 1 << 64, -(1 << 96), 0, -17],
        ] {
            let [a, b, c, d, e, f] = inputs;
            let expected = a
                .wrapping_sub(b)
                .wrapping_add(c.wrapping_mul(3))
                .wrapping_sub(d.wrapping_mul(5))
                .wrapping_add(e.wrapping_mul(7))
                .wrapping_sub(f);
            assert_eq!(unsafe { mix(a, b, c, d, e, f) }, expected, "{level:?}");
            let mut output = 0;
            unsafe { via_pointers(inputs.as_ptr(), &mut output) };
            assert_eq!(output, expected, "{level:?}");
        }
    }
}

#[test]
fn small_aggregates_live_in_registers_across_private_calls_and_phis() {
    // `@Opt` (a tag, an i64 and an i32) and `@Quad` (four fields) are held in
    // registers: private functions pass and return their parts, phis carry
    // them, and they reach storage only through `mstore`, the public
    // functions' references and a cast. `%total`'s four results take the
    // return registers and the return area on x86_64.
    let source = r#"
type @Opt = enum { #None, #Some(i64, i32) };
type @Quad = {i8, i64, i16, *i8};
func inline(never) private %wrap(v0.i64, v1.i32) -> @Opt {
block0:
    v2.i1 = eq v0 0.i64;
    br v2 block1 block2;
block1:
    v3.@Opt = enum.make @Opt #None ();
    return v3;
block2:
    v4.@Opt = enum.make @Opt #Some (v0, v1);
    return v4;
}
func inline(never) private %quad(v0.@Opt, v1.*i8) -> @Quad {
block0:
    v2.i1 = enum.is_variant v0 #Some;
    br v2 block1 block2;
block1:
    enum.assert_variant v0 #Some;
    v3.i64 = enum.extract v0 #Some 0.i8;
    v4.i32 = enum.extract v0 #Some 1.i8;
    v5.i16 = trunc v4 i16;
    v6.@Quad = insert_value undef.@Quad 0.i64 1.i8;
    v7.@Quad = insert_value v6 1.i64 v3;
    v8.@Quad = insert_value v7 2.i64 v5;
    v9.@Quad = insert_value v8 3.i64 v1;
    return v9;
block2:
    v10.@Quad = insert_value undef.@Quad 3.i64 v1;
    return v10;
}
func public %sum_quad(v0.@Quad) -> i64 {
block0:
    v1.i8 = extract_value v0 0.i64;
    v2.i64 = extract_value v0 1.i64;
    v3.i16 = extract_value v0 2.i64;
    v4.i64 = sext v1 i64;
    v5.i64 = sext v3 i64;
    v6.i64 = add v2 v4;
    v7.i64 = add v6 v5;
    return v7;
}
func inline(never) private %total(v0.i64, v1.*i8) -> (i64, i64, @Opt) {
block0:
    jump block1;
block1:
    v2.i64 = phi (v0 block0) (v9 block1);
    v3.i64 = phi (0.i64 block0) (v10 block1);
    v4.@Opt = phi (undef.@Opt block0) (v5 block1);
    v5.@Opt = call %wrap v2 7.i32;
    v6.@Quad = call %quad v5 v1;
    v7.i64 = call %sum_quad v6;
    v8.*i8 = extract_value v6 3.i64;
    v9.i64 = sub v2 1.i64;
    v10.i64 = add v3 v7;
    v11.i1 = gt v9 0.i64;
    br v11 block1 block2;
block2:
    v12.i64 = ptr_to_int v8 i64;
    return (v10, v12, v4);
}
func public %run(v0.i64, v1.*i8, v2.*i64) {
block0:
    (v3.i64, v4.i64, v5.@Opt) = call %total v0 v1;
    v6.*i64 = gep v2 1.i64;
    v7.*i64 = gep v2 2.i64;
    mstore v2 v3 i64;
    mstore v6 v4 i64;
    v8.*@Opt = bitcast v7 *@Opt;
    mstore v8 v5 @Opt;
    v9.[i64; 3] = bitcast v5 [i64; 3];
    v10.i64 = extract_value v9 1.i64;
    v11.*i64 = gep v2 5.i64;
    mstore v11 v10 i64;
    return;
}
func public %make_quad(v0.i64, v1.*i8) -> @Quad {
block0:
    v2.@Opt = call %wrap v0 9.i32;
    v3.@Quad = call %quad v2 v1;
    return v3;
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
        let run: unsafe extern "C" fn(i64, *const u8, *mut u8) =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        let make_quad: unsafe extern "C" fn(*mut u8, i64, *const u8) =
            unsafe { std::mem::transmute(artifact.function_address("make_quad").unwrap()) };
        let sum_quad: unsafe extern "C" fn(*const u8) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("sum_quad").unwrap()) };
        let marker = 0x5a5a_u16;
        let pointer = &marker as *const u16 as *const u8;
        // `@Opt`: an i1 tag, the i64 at 8 and the i32 at 16, in 24 bytes.
        let opt = |some: bool, value: i64, small: i32| {
            let mut bytes = [0u8; 24];
            bytes[0] = u8::from(some);
            if some {
                bytes[8..16].copy_from_slice(&value.to_le_bytes());
                bytes[16..20].copy_from_slice(&small.to_le_bytes());
            }
            bytes
        };
        for rounds in [1i64, 3] {
            let mut out = [0xa5u8; 48];
            unsafe { run(rounds, pointer, out.as_mut_ptr()) };
            // Each round adds `rounds - i` (the i64) + 1 (the i8) + 7 (the
            // i16 from 7.i32); the last round wraps 1.
            let expected_total: i64 = (1..=rounds).map(|value| value + 8).sum();
            assert_eq!(&out[..8], &expected_total.to_le_bytes(), "{level:?}");
            assert_eq!(&out[8..16], &(pointer as i64).to_le_bytes(), "{level:?}");
            // The phi's value is the previous round's `@Opt`: undef (zero) for
            // one round, else `#Some(2, 7)`.
            let previous = if rounds == 1 {
                [0u8; 24]
            } else {
                opt(true, 2, 7)
            };
            assert_eq!(&out[16..40], &previous, "{level:?} {rounds}");
            // The cast reads the same `@Opt`'s i64.
            assert_eq!(&out[40..48], &previous[8..16], "{level:?} {rounds}");
        }
        // `@Quad`: the i8 at 0, the i64 at 8, the i16 at 16, the pointer at 24.
        for value in [0i64, 42] {
            let mut bytes = [0xa5u8; 32];
            unsafe { make_quad(bytes.as_mut_ptr(), value, pointer) };
            let mut expected = [0u8; 32];
            if value != 0 {
                expected[0] = 1;
                expected[8..16].copy_from_slice(&value.to_le_bytes());
                expected[16..18].copy_from_slice(&9i16.to_le_bytes());
            }
            expected[24..32].copy_from_slice(&(pointer as i64).to_le_bytes());
            assert_eq!(bytes, expected, "{level:?} {value}");
        }
        let mut quad = [0u8; 32];
        quad[0] = 3;
        quad[8..16].copy_from_slice(&40i64.to_le_bytes());
        quad[16..18].copy_from_slice(&(-5i16).to_le_bytes());
        assert_eq!(unsafe { sum_quad(quad.as_ptr()) }, 38, "{level:?}");
    }
}

#[test]
fn small_aggregates_in_registers_nest_enums_arrays_and_empty_fields() {
    // Each type is held in registers: `@Z`'s empty fields have no parts,
    // `@Outer` nests one Option-like enum in another, `@EZ`'s one field is
    // empty, and `@S` holds an enum after a byte.
    let source = r#"
type @Empty = {};
type @Z = {i64, @Empty, [i8; 0], i32};
type @Inner = enum { #None, #Some(i64) };
type @Outer = enum { #Nothing, #Just(@Inner) };
type @EZ = enum { #A, #B(@Empty) };
type @S = {i8, @Inner};
func inline(never) private %z(v0.@Z, v1.@Empty) -> @Z {
block0:
    v2.i64 = extract_value v0 0.i64;
    v3.@Empty = extract_value v0 1.i64;
    v4.i32 = extract_value v0 3.i64;
    v5.i64 = add v2 1.i64;
    v6.@Z = insert_value v0 0.i64 v5;
    v7.@Z = insert_value v6 1.i64 v1;
    v8.i32 = add v4 2.i32;
    v9.@Z = insert_value v7 3.i64 v8;
    return v9;
}
func inline(never) private %outer(v0.i64) -> @Outer {
block0:
    v1.i1 = eq v0 0.i64;
    br v1 block1 block2;
block1:
    v2.@Inner = enum.make @Inner #None ();
    v3.@Outer = enum.make @Outer #Just (v2);
    return v3;
block2:
    v4.@Inner = enum.make @Inner #Some (v0);
    v5.@Outer = enum.make @Outer #Just (v4);
    return v5;
}
func inline(never) private %unwrap(v0.@Outer) -> i64 {
block0:
    v1.i1 = enum.is_variant v0 #Just;
    br v1 block1 block3;
block1:
    enum.assert_variant v0 #Just;
    v2.@Inner = enum.extract v0 #Just 0.i8;
    v3.i1 = enum.is_variant v2 #Some;
    br v3 block2 block3;
block2:
    enum.assert_variant v2 #Some;
    v4.i64 = enum.extract v2 #Some 0.i8;
    return v4;
block3:
    return -1.i64;
}
func inline(never) private %ez(v0.i1) -> @EZ {
block0:
    br v0 block1 block2;
block1:
    v1.@EZ = enum.make @EZ #A ();
    return v1;
block2:
    v2.@EZ = enum.make @EZ #B (undef.@Empty);
    return v2;
}
func inline(never) private %arr(v0.[i8; 4], v1.i8) -> [i8; 4] {
block0:
    v2.i8 = extract_value v0 3.i64;
    v3.i8 = add v2 v1;
    v4.[i8; 4] = insert_value v0 0.i64 v3;
    return v4;
}
func inline(never) private %s(v0.@S) -> @S {
block0:
    v1.@Inner = extract_value v0 1.i64;
    v2.@S = insert_value v0 0.i64 7.i8;
    v3.i1 = enum.is_variant v1 #None;
    br v3 block1 block2;
block1:
    v4.@Inner = enum.make @Inner #Some (3.i64);
    v5.@S = insert_value v2 1.i64 v4;
    return v5;
block2:
    return v2;
}
func public %run(v0.i64, v1.*i8, v2.i32) -> i64 {
block0:
    v3.@Z = insert_value undef.@Z 0.i64 v0;
    v4.@Z = insert_value v3 3.i64 5.i32;
    v5.@Z = call %z v4 undef.@Empty;
    v6.*@Z = bitcast v1 *@Z;
    mstore v6 v5 @Z;
    v7.@Outer = call %outer v0;
    v8.i64 = call %unwrap v7;
    v9.*i8 = gep v1 16.i64;
    v10.*@Outer = bitcast v9 *@Outer;
    mstore v10 v7 @Outer;
    v11.i1 = eq v0 0.i64;
    v12.@EZ = call %ez v11;
    v13.*i8 = gep v1 40.i64;
    v14.*@EZ = bitcast v13 *@EZ;
    mstore v14 v12 @EZ;
    v15.i8 = trunc v0 i8;
    v16.[i8; 4] = bitcast v2 [i8; 4];
    v17.[i8; 4] = call %arr v16 v15;
    v18.*i8 = gep v1 44.i64;
    v19.*[i8; 4] = bitcast v18 *[i8; 4];
    mstore v19 v17 [i8; 4];
    v20.@Inner = enum.make @Inner #None ();
    v21.@S = insert_value undef.@S 1.i64 v20;
    v22.@S = call %s v21;
    v23.*i8 = gep v1 48.i64;
    v24.*@S = bitcast v23 *@S;
    mstore v24 v22 @S;
    return v8;
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
        let run: unsafe extern "C" fn(i64, *mut u8, i32) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        for value in [0i64, 9] {
            let mut out = [0xa5u8; 72];
            let unwrapped =
                unsafe { run(value, out.as_mut_ptr(), i32::from_le_bytes([1, 2, 3, 4])) };
            assert_eq!(unwrapped, if value == 0 { -1 } else { value }, "{level:?}");
            let mut expected = [0u8; 72];
            // `@Z`: the i64 at 0 and the i32 at 8, in 16 bytes.
            expected[0..8].copy_from_slice(&(value + 1).to_le_bytes());
            expected[8..12].copy_from_slice(&7i32.to_le_bytes());
            // `@Outer` at 16: its tag, then `@Inner`'s tag at 24 and i64 at 32.
            expected[16] = 1;
            expected[24] = u8::from(value != 0);
            if value != 0 {
                expected[32..40].copy_from_slice(&value.to_le_bytes());
            }
            // `@EZ` at 40 is its tag alone.
            expected[40] = u8::from(value != 0);
            expected[41..44].fill(0xa5);
            expected[44..48].copy_from_slice(&[4u8.wrapping_add(value as u8), 2, 3, 4]);
            // `@S` at 48: the i8, then `@Inner`'s tag at 56 and i64 at 64.
            expected[48] = 7;
            expected[56] = 1;
            expected[64..72].copy_from_slice(&3i64.to_le_bytes());
            assert_eq!(out, expected, "{level:?} {value}");
        }
    }
}

#[test]
fn small_aggregates_in_registers_cast_load_constants_and_swap() {
    // `@B`'s i1 fields stay 0 or 1 through a private call, from a truncation
    // and from constant data; casts to and from i256 and between differently
    // split types go through storage; two phis swap `@P`s on every round.
    let source = r#"
type @B = {i1, i8, i1};
type @W = {i64, i64, i64, i64};
type @P = {i32, i32};
type @Q = {i8, i8, i16, i32};
global public const @B $b = {1, 9, 1};
func inline(never) private %flip(v0.@B) -> @B {
block0:
    v1.i1 = extract_value v0 0.i64;
    v2.i1 = extract_value v0 2.i64;
    v3.@B = insert_value v0 0.i64 v2;
    v4.@B = insert_value v3 2.i64 v1;
    return v4;
}
func public %run(v0.i64, v1.*i8, v2.i256) -> i64 {
block0:
    v3.i8 = trunc v0 i8;
    v4.i1 = trunc v3 i1;
    v5.@B = insert_value undef.@B 0.i64 v4;
    v6.@B = insert_value v5 1.i64 v3;
    v7.@B = call %flip v6;
    v8.*@B = bitcast v1 *@B;
    mstore v8 v7 @B;
    v9.i1 = extract_value v7 2.i64;
    v10.i64 = zext v9 i64;
    v11.constref<@B> = const.ref $b;
    v12.@B = const.load v11;
    v13.@B = call %flip v12;
    v14.*i8 = gep v1 4.i64;
    v15.*@B = bitcast v14 *@B;
    mstore v15 v13 @B;
    v16.@W = bitcast v2 @W;
    v17.i64 = extract_value v16 1.i64;
    v18.@W = insert_value v16 0.i64 v17;
    v19.i256 = bitcast v18 i256;
    v20.*i8 = gep v1 8.i64;
    v21.*i256 = bitcast v20 *i256;
    mstore v21 v19 i256;
    v22.@P = insert_value undef.@P 0.i64 1.i32;
    v23.@P = insert_value v22 1.i64 515.i32;
    v24.@Q = bitcast v23 @Q;
    v25.*i8 = gep v1 40.i64;
    v26.*@Q = bitcast v25 *@Q;
    mstore v26 v24 @Q;
    jump block1;
block1:
    v27.@P = phi (v23 block0) (v28 block1);
    v28.@P = phi (v22 block0) (v27 block1);
    v29.i64 = phi (v0 block0) (v30 block1);
    v30.i64 = sub v29 1.i64;
    v31.i1 = sgt v30 0.i64;
    br v31 block1 block2;
block2:
    v32.*i8 = gep v1 48.i64;
    v33.*@P = bitcast v32 *@P;
    mstore v33 v27 @P;
    v34.*i8 = gep v1 56.i64;
    v35.*@P = bitcast v34 *@P;
    mstore v35 v28 @P;
    return v10;
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
        let run: unsafe extern "C" fn(i64, *mut u8, *const u64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        let wide = [11u64, 22, 33, 44];
        let swapped: Vec<u8> = [22u64, 22, 33, 44]
            .iter()
            .flat_map(|limb| limb.to_le_bytes())
            .collect();
        let both = [1u8, 0, 0, 0, 3, 2, 0, 0];
        let first = [1u8, 0, 0, 0, 0, 0, 0, 0];
        for rounds in [2i64, 3, 6] {
            let mut out = [0xa5u8; 64];
            let flag = unsafe { run(rounds, out.as_mut_ptr(), wide.as_ptr()) };
            let bit = (rounds & 1) as u8;
            assert_eq!(flag, i64::from(bit), "{level:?} {rounds}");
            assert_eq!(&out[..3], &[0, rounds as u8, bit], "{level:?} {rounds}");
            assert_eq!(&out[4..7], &[1, 9, 1], "{level:?} {rounds}");
            assert_eq!(&out[8..40], &swapped[..], "{level:?} {rounds}");
            assert_eq!(&out[40..48], &both, "{level:?} {rounds}");
            // The loop body runs `rounds` times, swapping on each entry after
            // the first.
            let (a, b) = if rounds % 2 == 1 {
                (both, first)
            } else {
                (first, both)
            };
            assert_eq!(&out[48..56], &a, "{level:?} {rounds}");
            assert_eq!(&out[56..64], &b, "{level:?} {rounds}");
        }
    }
}

#[test]
fn small_aggregates_in_registers_reach_objects_and_public_functions() {
    // Sonatina functions calling public ones pass and receive `@Pair` through
    // storage. `@Opt` values are stored into an object's field and an enum
    // variant, and a loop carries one beside a `@Big`, which stays in storage.
    let source = r#"
type @Opt = enum { #None, #Some(i64) };
type @Pair = {i8, i64};
type @Big = {i64, i64, i64, i64, i64};
type @Holder = {i8, @Opt, @Big};
type @E = enum { #Empty, #Full(@Opt, i8) };
func public %make(v0.i64) -> @Pair {
block0:
    v1.i1 = ne v0 0.i64;
    v2.i8 = zext v1 i8;
    v3.@Pair = insert_value undef.@Pair 0.i64 v2;
    v4.@Pair = insert_value v3 1.i64 v0;
    return v4;
}
func public %take(v0.@Pair) -> i64 {
block0:
    v1.i8 = extract_value v0 0.i64;
    v2.i1 = ne v1 0.i8;
    br v2 block1 block2;
block1:
    v3.i64 = extract_value v0 1.i64;
    return v3;
block2:
    return 100.i64;
}
func inline(never) private %to_opt(v0.@Pair) -> @Opt {
block0:
    v1.i8 = extract_value v0 0.i64;
    v2.i1 = ne v1 0.i8;
    br v2 block1 block2;
block1:
    v3.i64 = extract_value v0 1.i64;
    v4.@Opt = enum.make @Opt #Some (v3);
    return v4;
block2:
    v5.@Opt = enum.make @Opt #None ();
    return v5;
}
func inline(never) private %to_pair(v0.@Opt) -> @Pair {
block0:
    v1.i1 = enum.is_variant v0 #Some;
    br v1 block1 block2;
block1:
    enum.assert_variant v0 #Some;
    v2.i64 = enum.extract v0 #Some 0.i8;
    v3.@Pair = insert_value undef.@Pair 0.i64 1.i8;
    v4.@Pair = insert_value v3 1.i64 v2;
    return v4;
block2:
    return undef.@Pair;
}
func inline(never) private %fill(v0.objref<@Holder>, v1.@Opt, v2.objref<@E>) {
block0:
    v3.objref<@Opt> = obj.proj v0 1.i64;
    obj.store v3 v1;
    v4.objref<i8> = obj.proj v0 0.i64;
    obj.store v4 3.i8;
    enum.write_variant v2 #Full (v1, 4.i8);
    return;
}
func public %run(v0.i64, v1.*i8, v2.*i8) -> i64 {
block0:
    v3.*@Holder = bitcast v1 *@Holder;
    v4.*@E = bitcast v2 *@E;
    v5.@Pair = call %make v0;
    v6.i64 = call %take v5;
    v7.@Opt = call %to_opt v5;
    v8.objref<@Holder> = obj.from_ptr v3;
    v9.objref<@E> = obj.from_ptr v4;
    call %fill v8 v7 v9;
    v10.@Holder = obj.load v8;
    v11.@Opt = extract_value v10 1.i64;
    v12.@Big = extract_value v10 2.i64;
    jump block1;
block1:
    v13.@Opt = phi (v11 block0) (v17 block1);
    v14.@Big = phi (v12 block0) (v18 block1);
    v15.i64 = phi (v0 block0) (v19 block1);
    v16.i64 = extract_value v14 0.i64;
    v17.@Opt = enum.make @Opt #Some (v16);
    v18.@Big = insert_value v14 0.i64 v15;
    v19.i64 = sub v15 1.i64;
    v20.i1 = sgt v19 0.i64;
    br v20 block1 block2;
block2:
    v21.@Holder = insert_value v10 1.i64 v13;
    v22.@Holder = insert_value v21 2.i64 v14;
    mstore v3 v22 @Holder;
    v23.@Pair = call %to_pair v13;
    v24.i64 = call %take v23;
    v25.i64 = add v6 v24;
    return v25;
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
        let run: unsafe extern "C" fn(i64, *mut u8, *mut u8) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        for value in [0i64, 1, 5] {
            // `@Holder`: the i8 at 0, `@Opt` at 8 (its i64 at 16), `@Big` at 24.
            let mut holder = [0xa5u8; 64];
            for (index, word) in holder[24..].chunks_mut(8).enumerate() {
                word.copy_from_slice(&(index as i64 * 10 + 1).to_le_bytes());
            }
            let mut variant = [0xa5u8; 32];
            let total = unsafe { run(value, holder.as_mut_ptr(), variant.as_mut_ptr()) };
            // The loop body runs `max(value, 1)` times: each entry after the
            // first takes `#Some` of the previous `@Big`'s first word, which
            // the previous entry set to its counter.
            let first = (value != 0).then_some(value);
            let (mut opt, mut big) = (first, [1i64, 11, 21, 31, 41]);
            for counter in (2..=value).rev() {
                opt = Some(big[0]);
                big[0] = counter;
            }
            let taken = |opt: Option<i64>| opt.unwrap_or(100);
            assert_eq!(total, taken(first) + taken(opt), "{level:?} {value}");
            let mut expected = [0u8; 64];
            expected[0] = 3;
            expected[8] = u8::from(opt.is_some());
            expected[16..24].copy_from_slice(&opt.unwrap_or(0).to_le_bytes());
            for (index, word) in big.iter().enumerate() {
                expected[24 + index * 8..32 + index * 8].copy_from_slice(&word.to_le_bytes());
            }
            assert_eq!(holder, expected, "{level:?} {value}");
            // `@E`: its tag, `@Opt` at 8 (its i64 at 16), the i8 at 24.
            let mut expected = [0xa5u8; 32];
            expected[0] = 1;
            expected[8..24].fill(0);
            expected[8] = u8::from(value != 0);
            expected[16..24].copy_from_slice(&value.to_le_bytes());
            expected[24] = 4;
            assert_eq!(variant, expected, "{level:?} {value}");
        }
    }
}
