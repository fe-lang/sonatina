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
