use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};
use sonatina_ir::U256;

use super::parse_verified_native_module;

#[test]
fn direct_i128_arguments_returns_and_internal_calls_preserve_both_words() {
    let source = include_str!("../../test_files/cranelift/i128_abi.sntn");
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
fn private_functions_pass_and_return_i256_in_registers() {
    // Private callees take and return i256 values as limbs. Two results
    // fill the return registers and a third goes through the implicit
    // return area.
    let source = r#"
func inline(never) private %sum_diff(v0.i256, v1.i256) -> (i256, i256) {
block0:
    v2.i256 = add v0 v1;
    v3.i256 = sub v0 v1;
    return (v2, v3);
}

func inline(never) private %mixed(v0.i256, v1.i64, v2.i256, v3.i256) -> (i256, i64, i256, i256) {
block0:
    v4.i256 = mul v0 v2;
    v5.i64 = add v1 1.i64;
    v6.i256 = xor v2 v3;
    v7.i256 = shl 64.i256 v3;
    return (v4, v5, v6, v7);
}

func inline(never) private %double(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 v0;
    return v1;
}

func public %exercise(v0.*i256, v1.*i256) {
block0:
    v2.i256 = mload v0 i256;
    v3.i64 = ptr_to_int v0 i64;
    v4.i64 = add v3 32.i64;
    v5.*i256 = int_to_ptr v4 *i256;
    v6.i256 = mload v5 i256;
    (v7.i256, v8.i256) = call %sum_diff v2 v6;
    (v9.i256, v10.i64, v11.i256, v12.i256) = call %mixed v7 41.i64 v8 v2;
    v13.i256 = call %double v12;
    v14.i256 = zext v10 i256;
    v15.i256 = add v9 v14;
    v16.i256 = add v11 v13;
    mstore v1 v15 i256;
    v17.i64 = ptr_to_int v1 i64;
    v18.i64 = add v17 32.i64;
    v19.*i256 = int_to_ptr v18 *i256;
    mstore v19 v16 i256;
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
        .unwrap();
        let exercise: unsafe extern "C" fn(*const U256, *mut U256) =
            unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
        for (a, b) in [
            (U256::from(7), U256::from(5)),
            (U256::MAX, U256::from(3) << 200),
            (U256::from(1) << 255, U256::MAX - U256::from(12345)),
        ] {
            let (sum, _) = a.overflowing_add(b);
            let (diff, _) = a.overflowing_sub(b);
            let (product, _) = sum.overflowing_mul(diff);
            let shifted = a << 64;
            let (doubled, _) = shifted.overflowing_add(shifted);
            let expected = [
                product.overflowing_add(U256::from(42)).0,
                (diff ^ a).overflowing_add(doubled).0,
            ];
            let mut output = [U256::zero(); 2];
            unsafe { exercise([a, b].as_ptr(), output.as_mut_ptr()) };
            assert_eq!(output, expected, "{level:?}");
        }
    }
}
