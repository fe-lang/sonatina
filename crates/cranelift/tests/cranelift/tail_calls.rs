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
fn tail_calls_return_small_aggregates_as_parts() {
    // `@Quad` is held in registers. Each tail call hands nine result parts
    // on, which take all of the `tail` convention's return registers and the
    // caller's return area.
    let source = r#"
type @Quad = {i8, i64, i16, i64};
func private %even(v0.i64, v1.i64) -> (@Quad, i64, @Quad) {
block0:
    v2.i1 = eq v0 0.i64;
    br v2 block1 block2;
block1:
    v3.@Quad = insert_value undef.@Quad 0.i64 1.i8;
    v4.@Quad = insert_value v3 1.i64 v1;
    v5.@Quad = insert_value v4 2.i64 -3.i16;
    v6.@Quad = insert_value v5 3.i64 77.i64;
    v7.@Quad = insert_value v6 0.i64 9.i8;
    return (v6, v1, v7);
block2:
    v8.i64 = sub v0 1.i64;
    v9.i64 = add v1 2.i64;
    (v10.@Quad, v11.i64, v12.@Quad) = call %odd v8 v9;
    return (v10, v11, v12);
}

func private %odd(v0.i64, v1.i64) -> (@Quad, i64, @Quad) {
block0:
    v2.i1 = eq v0 0.i64;
    br v2 block1 block2;
block1:
    v3.@Quad = insert_value undef.@Quad 0.i64 2.i8;
    v4.@Quad = insert_value v3 1.i64 v1;
    return (v4, v1, v4);
block2:
    v5.i64 = sub v0 1.i64;
    v6.i64 = add v1 1.i64;
    (v7.@Quad, v8.i64, v9.@Quad) = call %even v5 v6;
    return (v7, v8, v9);
}

func public %run(v0.i64, v1.*i8) {
block0:
    (v2.@Quad, v3.i64, v4.@Quad) = call %even v0 0.i64;
    v5.*@Quad = bitcast v1 *@Quad;
    mstore v5 v2 @Quad;
    v6.*i8 = gep v1 32.i64;
    v7.*i64 = bitcast v6 *i64;
    mstore v7 v3 i64;
    v8.*i8 = gep v1 40.i64;
    v9.*@Quad = bitcast v8 *@Quad;
    mstore v9 v4 @Quad;
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
        let run: unsafe extern "C" fn(i64, *mut u8) =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        for depth in [DEPTH, DEPTH + 1] {
            let mut result = [0xa5u8; 72];
            unsafe { run(depth, result.as_mut_ptr()) };
            // An even depth ends in `%even`, an odd one in `%odd`, whose
            // fields it leaves undef are zero.
            let sum = (depth / 2 * 3 + depth % 2 * 2).to_le_bytes();
            let mut quad = [0u8; 32];
            quad[8..16].copy_from_slice(&sum);
            let mut second = quad;
            if depth % 2 == 0 {
                quad[16..18].copy_from_slice(&(-3i16).to_le_bytes());
                quad[24..32].copy_from_slice(&77i64.to_le_bytes());
                second = quad;
                (quad[0], second[0]) = (1, 9);
            } else {
                (quad[0], second[0]) = (2, 2);
            }
            let expected = [&quad[..], &sum, &second].concat();
            assert_eq!(result[..], expected, "{level:?} {depth}");
        }
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

#[test]
fn tail_calls_pass_aggregate_arguments_on() {
    // `%count` passes its argument on to itself, then to `%consume`, which
    // owns it and overwrites it, so `%count` owns it too and `%run`, which
    // reads its value afterwards, gives it a copy.
    let source = r#"
func inline(never) private %fill(v0.i64) -> [i64; 32] {
block0:
    v1.[i64; 32] = insert_value undef.[i64; 32] 0.i64 v0;
    return v1;
}

func inline(never) private %consume(v0.[i64; 32]) -> i64 {
block0:
    v1.objref<[i64; 32]> = obj.alloc [i64; 32];
    obj.store v1 v0;
    v2.objref<i64> = obj.index v1 0.i64;
    v3.i64 = obj.load v2;
    v4.i64 = add v3 1.i64;
    obj.store v2 v4;
    v5.i64 = obj.load v2;
    return v5;
}

func private %count(v0.[i64; 32], v1.i64) -> i64 {
block0:
    v2.i1 = eq v1 0.i64;
    br v2 block1 block2;
block1:
    v3.i64 = call %consume v0;
    return v3;
block2:
    v4.i64 = sub v1 1.i64;
    v5.i64 = call %count v0 v4;
    return v5;
}

func public %run(v0.i64, v1.i64) -> i64 {
block0:
    v2.[i64; 32] = call %fill v0;
    v3.i64 = call %count v2 v1;
    v4.i64 = extract_value v2 0.i64;
    v5.i64 = mul v4 1000.i64;
    v6.i64 = add v3 v5;
    return v6;
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
        let run: unsafe extern "C" fn(i64, i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        assert_eq!(unsafe { run(7, DEPTH) }, 8 + 7 * 1000, "{level:?}");
    }
}

#[test]
fn interpreter_handlers_tail_call_with_their_frame() {
    // Each handler takes the interpreter's frame (code, pc, count, top,
    // depth) and tail-calls `%next`, whose switch tail-calls the next
    // opcode's handler through a table. Five fields are held in registers;
    // with a sixth, the frame passes in storage, which each handler writes
    // its new frame into. The code `[1, 2, 0]` counts to `DEPTH`.
    for (extra_field, extra_init, extra_out) in [
        ("", "v8.@Frame = insert_value v7 4.i64 0.i64;", ""),
        (
            ", i64",
            "v8.@Frame = insert_value v7 5.i64 77.i64;",
            "v8.i64 = extract_value v1 5.i64;
    v9.*i64 = gep v0 3.i64;
    mstore v9 v8 i64;",
        ),
    ] {
        let source = format!(
            r#"
type @Frame = {{*i8, i64, i64, *i8, i64{extra_field}}};
func private %next(v0.*i64, v1.@Frame) {{
block0:
    v2.*i8 = extract_value v1 0.i64;
    v3.i64 = extract_value v1 1.i64;
    v4.*i8 = gep v2 v3;
    v5.i8 = mload v4 i8;
    br_table v5 block1 (1.i8 block2) (2.i8 block3);
block1:
    call %op_stop v0 v1;
    return;
block2:
    call %op_count v0 v1;
    return;
block3:
    call %op_loop v0 v1;
    return;
}}

func inline(never) private %op_stop(v0.*i64, v1.@Frame) {{
block0:
    v2.i64 = extract_value v1 2.i64;
    v3.*i8 = extract_value v1 3.i64;
    v4.i64 = extract_value v1 4.i64;
    v5.i64 = ptr_to_int v3 i64;
    mstore v0 v2 i64;
    v6.*i64 = gep v0 1.i64;
    mstore v6 v4 i64;
    v7.*i64 = gep v0 2.i64;
    mstore v7 v5 i64;
    {extra_out}
    return;
}}

func private %op_count(v0.*i64, v1.@Frame) {{
block0:
    v2.i64 = extract_value v1 1.i64;
    v3.i64 = add v2 1.i64;
    v4.i64 = extract_value v1 2.i64;
    v5.i64 = add v4 1.i64;
    v6.*i8 = extract_value v1 3.i64;
    v7.*i8 = gep v6 8.i64;
    v8.i64 = extract_value v1 4.i64;
    v9.i64 = add v8 1.i64;
    v10.@Frame = insert_value v1 1.i64 v3;
    v11.@Frame = insert_value v10 2.i64 v5;
    v12.@Frame = insert_value v11 3.i64 v7;
    v13.@Frame = insert_value v12 4.i64 v9;
    call %next v0 v13;
    return;
}}

func private %op_loop(v0.*i64, v1.@Frame) {{
block0:
    v2.i64 = extract_value v1 2.i64;
    v3.i64 = extract_value v1 4.i64;
    v4.i64 = add v3 2.i64;
    v5.@Frame = insert_value v1 4.i64 v4;
    v6.i1 = lt v2 {DEPTH}.i64;
    br v6 block1 block2;
block1:
    v7.@Frame = insert_value v5 1.i64 0.i64;
    call %next v0 v7;
    return;
block2:
    v8.i64 = extract_value v1 1.i64;
    v9.i64 = add v8 1.i64;
    v10.@Frame = insert_value v5 1.i64 v9;
    call %next v0 v10;
    return;
}}

func public %run(v0.*i8, v1.*i8, v2.*i64) {{
block0:
    v3.@Frame = insert_value undef.@Frame 0.i64 v0;
    v4.@Frame = insert_value v3 1.i64 0.i64;
    v5.@Frame = insert_value v4 2.i64 0.i64;
    v6.@Frame = insert_value v5 3.i64 v1;
    v7.@Frame = insert_value v6 4.i64 0.i64;
    {extra_init}
    call %next v2 v8;
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
            .unwrap_or_else(|errors| panic!("{level:?} {extra_field:?}: {errors:?}"));
            let run: unsafe extern "C" fn(*const u8, *const u8, *mut i64) =
                unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
            let code = [1u8, 2, 0];
            let top = 4096usize as *const u8;
            let mut status = [-1i64; 4];
            unsafe { run(code.as_ptr(), top, status.as_mut_ptr()) };
            let extra = if extra_field.is_empty() { -1 } else { 77 };
            assert_eq!(
                status,
                [DEPTH, 3 * DEPTH, 4096 + 8 * DEPTH, extra],
                "{level:?} {extra_field:?}"
            );
            assert!(
                artifact.function_address("next").is_none(),
                "{level:?} {extra_field:?}"
            );
        }
    }
}

#[test]
fn handlers_resume_through_a_dispatch_that_builds_their_frame() {
    // `%start` builds the interpreter's frame from scalars and tail-calls
    // the handler of its first opcode with it, through a table. `%op_loop`
    // resumes through `%start`, so the stack overflows unless `%start`'s
    // calls are tail calls. The code `[1, 2, 0]` counts to `DEPTH`.
    let source = format!(
        r#"
type @Frame = {{*i8, i64, i64, *i8, i64}};
func inline(never) private %start(v0.*i64, v1.*i8, v2.i64, v3.*i8, v4.i64) {{
block0:
    v5.@Frame = insert_value undef.@Frame 0.i64 v1;
    v6.@Frame = insert_value v5 1.i64 0.i64;
    v7.@Frame = insert_value v6 2.i64 v2;
    v8.@Frame = insert_value v7 3.i64 v3;
    v9.@Frame = insert_value v8 4.i64 v4;
    v10.i8 = mload v1 i8;
    br_table v10 block1 (1.i8 block2) (2.i8 block3);
block1:
    call %op_stop v0 v9;
    return;
block2:
    call %op_count v0 v9;
    return;
block3:
    call %op_loop v0 v9;
    return;
}}

func private %next(v0.*i64, v1.@Frame) {{
block0:
    v2.*i8 = extract_value v1 0.i64;
    v3.i64 = extract_value v1 1.i64;
    v4.*i8 = gep v2 v3;
    v5.i8 = mload v4 i8;
    br_table v5 block1 (1.i8 block2) (2.i8 block3);
block1:
    call %op_stop v0 v1;
    return;
block2:
    call %op_count v0 v1;
    return;
block3:
    call %op_loop v0 v1;
    return;
}}

func inline(never) private %op_stop(v0.*i64, v1.@Frame) {{
block0:
    v2.i64 = extract_value v1 2.i64;
    v3.*i8 = extract_value v1 3.i64;
    v4.i64 = extract_value v1 4.i64;
    v5.i64 = ptr_to_int v3 i64;
    mstore v0 v2 i64;
    v6.*i64 = gep v0 1.i64;
    mstore v6 v4 i64;
    v7.*i64 = gep v0 2.i64;
    mstore v7 v5 i64;
    return;
}}

func private %op_count(v0.*i64, v1.@Frame) {{
block0:
    v2.i64 = extract_value v1 1.i64;
    v3.i64 = add v2 1.i64;
    v4.i64 = extract_value v1 2.i64;
    v5.i64 = add v4 1.i64;
    v6.*i8 = extract_value v1 3.i64;
    v7.*i8 = gep v6 8.i64;
    v8.i64 = extract_value v1 4.i64;
    v9.i64 = add v8 1.i64;
    v10.@Frame = insert_value v1 1.i64 v3;
    v11.@Frame = insert_value v10 2.i64 v5;
    v12.@Frame = insert_value v11 3.i64 v7;
    v13.@Frame = insert_value v12 4.i64 v9;
    call %next v0 v13;
    return;
}}

func private %op_loop(v0.*i64, v1.@Frame) {{
block0:
    v2.i64 = extract_value v1 2.i64;
    v3.i64 = extract_value v1 4.i64;
    v4.i64 = add v3 2.i64;
    v5.i1 = lt v2 {DEPTH}.i64;
    br v5 block1 block2;
block1:
    v6.*i8 = extract_value v1 0.i64;
    v7.*i8 = extract_value v1 3.i64;
    call %start v0 v6 v2 v7 v4;
    return;
block2:
    v8.i64 = extract_value v1 1.i64;
    v9.i64 = add v8 1.i64;
    v10.@Frame = insert_value v1 1.i64 v9;
    v11.@Frame = insert_value v10 4.i64 v4;
    call %next v0 v11;
    return;
}}

func public %run(v0.*i8, v1.*i8, v2.*i64) {{
block0:
    call %start v2 v0 0.i64 v1 0.i64;
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
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let run: unsafe extern "C" fn(*const u8, *const u8, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        let code = [1u8, 2, 0];
        let top = 4096usize as *const u8;
        let mut status = [-1i64; 3];
        unsafe { run(code.as_ptr(), top, status.as_mut_ptr()) };
        assert_eq!(status, [DEPTH, 3 * DEPTH, 4096 + 8 * DEPTH], "{level:?}");
    }
}

#[test]
fn tail_calls_read_arguments_before_writing_their_storage() {
    // `%rotate`'s tail call writes a new `@Holder` into its first
    // argument's storage and passes the old first field, a view of that
    // storage, in its second argument's: the field is read first.
    let source = r#"
type @Holder = {[i64; 8], [i64; 8]};
func private %rotate(v0.@Holder, v1.[i64; 8], v2.i64, v3.*i8) {
block0:
    v4.i1 = eq v2 0.i64;
    br v4 block1 block2;
block1:
    v5.*@Holder = bitcast v3 *@Holder;
    mstore v5 v0 @Holder;
    v6.*i8 = gep v3 128.i64;
    v7.*[i64; 8] = bitcast v6 *[i64; 8];
    mstore v7 v1 [i64; 8];
    return;
block2:
    v8.[i64; 8] = extract_value v0 0.i64;
    v9.[i64; 8] = insert_value v1 0.i64 v2;
    v10.@Holder = insert_value v0 0.i64 v9;
    v11.i64 = sub v2 1.i64;
    call %rotate v10 v8 v11 v3;
    return;
}

func public %run(v0.*i8, v1.i64, v2.*i8) {
block0:
    v3.*@Holder = bitcast v0 *@Holder;
    v4.@Holder = mload v3 @Holder;
    v5.*i8 = gep v0 128.i64;
    v6.*[i64; 8] = bitcast v5 *[i64; 8];
    v7.[i64; 8] = mload v6 [i64; 8];
    call %rotate v4 v7 v1 v2;
    return;
}
"#;
    let steps = DEPTH / 10;
    // Each step makes the holder `{big with [0] = n, second}` and the big
    // the holder's old first field.
    let input: [i64; 24] = std::array::from_fn(|index| index as i64 + 1);
    let (mut first, mut second, mut big) = ([0i64; 8], [0i64; 8], [0i64; 8]);
    first.copy_from_slice(&input[..8]);
    second.copy_from_slice(&input[8..16]);
    big.copy_from_slice(&input[16..]);
    for n in (1..=steps).rev() {
        let mut next = big;
        next[0] = n;
        big = std::mem::replace(&mut first, next);
    }
    let expected = [first, second, big].concat();
    for level in [OptLevel::O0, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let run: unsafe extern "C" fn(*const i64, i64, *mut i64) =
            unsafe { std::mem::transmute(artifact.function_address("run").unwrap()) };
        let mut output = [0i64; 24];
        unsafe { run(input.as_ptr(), steps, output.as_mut_ptr()) };
        assert_eq!(output[..], expected[..], "{level:?}");
    }
}
