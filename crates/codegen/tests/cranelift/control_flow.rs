use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};
use sonatina_ir::U256;

use super::parse_native_module;

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
