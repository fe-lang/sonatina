use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};

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
