use sonatina_codegen::{Compile, compile::OptLevel};
use sonatina_cranelift::CraneliftJitBackend;

use super::parse_verified_native_module;

/// Deep enough that the test thread's stack overflows unless each call
/// replaces its caller's frame.
const DEPTH: i64 = 10_000_000;

#[test]
fn mutually_recursive_tail_calls_reuse_the_frame() {
    let source = r#"
func private %even(v0.i64) -> i64 {
block0:
    v1.i1 = eq v0 0.i64;
    br v1 block1 block2;
block1:
    return 1.i64;
block2:
    v2.i64 = sub v0 1.i64;
    v3.i64 = call %odd v2;
    return v3;
}

func private %odd(v0.i64) -> i64 {
block0:
    v1.i1 = eq v0 0.i64;
    br v1 block1 block2;
block1:
    return 0.i64;
block2:
    v2.i64 = sub v0 1.i64;
    v3.i64 = call %even v2;
    return v3;
}

func public %is_even(v0.i64) -> i64 {
block0:
    v1.i64 = call %even v0;
    return v1;
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
        let is_even: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("is_even").unwrap()) };
        assert_eq!(unsafe { is_even(DEPTH) }, 1, "{level:?}");
        assert_eq!(unsafe { is_even(DEPTH + 1) }, 0, "{level:?}");
        // `even` and `odd` use the `tail` convention, which native callers
        // can't use.
        for name in ["even", "odd"] {
            assert!(
                artifact.function_address(name).is_none(),
                "{level:?} {name}"
            );
        }
    }
}

#[test]
fn tail_calls_pass_the_result_buffer_on() {
    // An i256 result is written through the caller's buffer, which each
    // tail call hands to its callee.
    let source = r#"
func private %down(v0.i64, v1.i64) -> i256 {
block0:
    v2.i1 = eq v0 0.i64;
    br v2 block1 block2;
block1:
    v3.i256 = zext v1 i256;
    v4.i256 = shl 192.i256 v3;
    v5.i256 = or v4 v3;
    return v5;
block2:
    v6.i64 = sub v0 1.i64;
    v7.i64 = add v1 1.i64;
    v8.i256 = call %down v6 v7;
    return v8;
}

func public %run(v0.i64, v1.*i256) {
block0:
    v2.i256 = call %down v0 0.i64;
    mstore v1 v2 i256;
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
        let run: unsafe extern "C" fn(i64, *mut u64) =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        let mut result = [0u64; 4];
        unsafe { run(DEPTH, result.as_mut_ptr()) };
        let depth = DEPTH as u64;
        assert_eq!(result, [depth, 0, 0, depth], "{level:?}");
    }
}

#[test]
fn dispatch_arms_tail_call_through_their_join() {
    // A `match` whose arms make calls joins their results in a block that
    // returns them, as an interpreter's dispatch does.
    let source = r#"
func private %dispatch(v0.i64, v1.i64) -> i64 {
block0:
    v2.i1 = eq v0 0.i64;
    br v2 block4 block1;
block1:
    v3.i64 = and v0 1.i64;
    br_table v3 block3 (0.i64 block2);
block2:
    v4.i64 = call %even v0 v1;
    jump block5;
block3:
    v5.i64 = call %odd v0 v1;
    jump block5;
block4:
    jump block5;
block5:
    v6.i64 = phi (v4 block2) (v5 block3) (v1 block4);
    return v6;
}

func private %even(v0.i64, v1.i64) -> i64 {
block0:
    v2.i64 = sub v0 1.i64;
    v3.i64 = add v1 1.i64;
    v4.i64 = call %dispatch v2 v3;
    return v4;
}

func private %odd(v0.i64, v1.i64) -> i64 {
block0:
    v2.i64 = sub v0 1.i64;
    v3.i64 = add v1 2.i64;
    v4.i64 = call %dispatch v2 v3;
    return v4;
}

func public %run(v0.i64) -> i64 {
block0:
    v1.i64 = call %dispatch v0 0.i64;
    return v1;
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
        let run: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        assert_eq!(unsafe { run(DEPTH) }, DEPTH / 2 * 3, "{level:?}");
    }
}

#[test]
fn tail_call_switches_dispatch_through_a_table() {
    // A byte-code interpreter: `dispatch` switches on the opcode at `pc`,
    // and every destination tail-calls a handler with the same arguments,
    // so dispatch becomes one indirect tail call.
    let source = r#"
func private %dispatch(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    v3.i64 = ptr_to_int v0 i64;
    v4.i64 = add v3 v1;
    v5.*i8 = int_to_ptr v4 *i8;
    v6.i8 = mload v5 i8;
    v7.i32 = zext v6 i32;
    br_table v7 block4 (0.i32 block1) (1.i32 block2) (2.i32 block3);
block1:
    v8.i64 = call %halt v0 v1 v2;
    return v8;
block2:
    v9.i64 = call %inc v0 v1 v2;
    return v9;
block3:
    v10.i64 = call %double v0 v1 v2;
    return v10;
block4:
    v11.i64 = call %invalid v0 v1 v2;
    return v11;
}

func private %halt(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    return v2;
}

func private %inc(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    v3.i64 = add v1 1.i64;
    v4.i64 = add v2 1.i64;
    v5.i64 = call %dispatch v0 v3 v4;
    return v5;
}

func private %double(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    v3.i64 = add v1 1.i64;
    v4.i64 = mul v2 2.i64;
    v5.i64 = call %dispatch v0 v3 v4;
    return v5;
}

func private %invalid(v0.*i8, v1.i64, v2.i64) -> i64 {
block0:
    return -1.i64;
}

func public %run(v0.*i8) -> i64 {
block0:
    v1.i64 = call %dispatch v0 0.i64 0.i64;
    return v1;
}
"#;
    let mut code = vec![1u8; DEPTH as usize];
    code[DEPTH as usize - 2] = 2;
    *code.last_mut().unwrap() = 0;
    let mut invalid = code.clone();
    invalid[DEPTH as usize / 2] = 7;
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let run: unsafe extern "C" fn(*const u8) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        assert_eq!(unsafe { run(code.as_ptr()) }, (DEPTH - 2) * 2, "{level:?}");
        assert_eq!(unsafe { run(invalid.as_ptr()) }, -1, "{level:?}");
    }
}
