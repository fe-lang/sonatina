use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};

use super::parse_verified_native_module;

#[test]
fn heap_exports_preserve_projected_aliases_across_returns() {
    let source = r#"
declare external %free(*[i64; 2]);
func private %export(v0.objref<i64>) -> *i64 {
block0:
    v1.*i64 = obj.materialize.heap v0;
    return v1;
}
func private %make(v0.i64) -> *[i64; 2] {
block0:
    v1.objref<[i64; 2]> = obj.alloc [i64; 2];
    v2.objref<i64> = obj.index v1 1.i64;
    obj.store v2 v0;
    v3.*i64 = call %export v2;
    mstore v3 40.i64 i64;
    v4.i64 = obj.load v2;
    v5.i64 = add v4 2.i64;
    obj.store v2 v5;
    v6.*[i64; 2] = obj.materialize.stack v1;
    return v6;
}
func public %exercise() -> i64 {
block0:
    v0.*[i64; 2] = call %make 11.i64;
    v1.*[i64; 2] = call %make 22.i64;
    v2.*i64 = gep v0 0.i64 1.i64;
    v3.*i64 = gep v1 0.i64 1.i64;
    mstore v2 17.i64 i64;
    v4.i64 = mload v2 i64;
    v5.i64 = mload v3 i64;
    v6.i64 = mul v4 100.i64;
    v7.i64 = add v6 v5;
    call %free v0;
    call %free v1;
    return v7;
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
        let exercise: unsafe extern "C" fn() -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
        assert_eq!(unsafe { exercise() }, 1742, "{level:?}");
    }
}

#[test]
fn dynamic_allocations_are_distinct_and_support_wide_sizes() {
    let source = r#"
declare external %free(*i64);
func public %exercise(v0.i64) -> i64 {
block0:
    v1.i256 = zext v0 i256;
    v2.*i64 = mem.alloc_dynamic v1;
    v3.i128 = zext v0 i128;
    v4.*i64 = mem.alloc_dynamic v3;
    mstore v2 17.i64 i64;
    mstore v4 42.i64 i64;
    v5.i64 = mload v2 i64;
    v6.i64 = mload v4 i64;
    v7.i64 = mul v5 100.i64;
    v8.i64 = add v7 v6;
    call %free v2;
    call %free v4;
    return v8;
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
        let exercise: unsafe extern "C" fn(u64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
        assert_eq!(unsafe { exercise(8) }, 1742, "{level:?}");
    }
}

#[test]
fn selecting_between_borrowed_arguments_preserves_mutation_aliases() {
    let source = r#"
func private %choose(v0.i1, v1.objref<i64>, v2.objref<i64>) -> objref<i64> {
block0:
    br v0 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v3.objref<i64> = phi (v1 block1) (v2 block2);
    return v3;
}
func public %exercise(v0.i8) -> i64 {
block0:
    v1.objref<i64> = obj.alloc i64;
    v2.objref<i64> = obj.alloc i64;
    obj.store v1 11.i64;
    obj.store v2 22.i64;
    v3.i1 = trunc v0 i1;
    v4.objref<i64> = call %choose v3 v1 v2;
    obj.store v4 99.i64;
    v5.i64 = obj.load v1;
    v6.i64 = obj.load v2;
    v7.i64 = mul v5 100.i64;
    v8.i64 = add v7 v6;
    return v8;
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
        let exercise: unsafe extern "C" fn(u8) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
        assert_eq!(unsafe { exercise(0) }, 1199, "{level:?}");
        assert_eq!(unsafe { exercise(1) }, 9922, "{level:?}");
    }
}

#[test]
fn mixed_returns_preserve_fresh_lifetimes_and_borrowed_projection_aliases() {
    for separate_returns in [true, false] {
        let choose = if separate_returns {
            r#"block0:
    br v0 block1 block2;
block1:
    v3.objref<i64> = obj.alloc i64;
    obj.store v3 v2;
    return v3;
block2:
    v4.objref<i64> = obj.index v1 1.i64;
    return v4;"#
        } else {
            r#"block0:
    br v0 block1 block2;
block1:
    v3.objref<i64> = obj.alloc i64;
    obj.store v3 v2;
    jump block3;
block2:
    v4.objref<i64> = obj.index v1 1.i64;
    jump block3;
block3:
    v5.objref<i64> = phi (v3 block1) (v4 block2);
    return v5;"#
        };
        let source = format!(
            r#"
func private %choose(v0.i1, v1.objref<[i64; 2]>, v2.i64) -> objref<i64> {{
{choose}
}}
func private %forward(v0.i1, v1.objref<[i64; 2]>, v2.i64) -> objref<i64> {{
block0:
    v3.objref<i64> = call %choose v0 v1 v2;
    return v3;
}}
func public %exercise(v0.i8, v1.i8) -> i64 {{
block0:
    v2.objref<[i64; 2]> = obj.alloc [i64; 2];
    v3.objref<i64> = obj.index v2 1.i64;
    obj.store v3 42.i64;
    v4.i1 = trunc v0 i1;
    v5.i1 = trunc v1 i1;
    v6.objref<i64> = call %forward v4 v2 111.i64;
    v7.objref<i64> = call %forward v5 v2 222.i64;
    v8.i64 = obj.load v6;
    v9.i64 = obj.load v7;
    v10.i64 = add v8 v9;
    obj.store v6 10.i64;
    v11.i64 = obj.load v7;
    v12.i64 = obj.load v3;
    v13.i64 = mul v10 10000.i64;
    v14.i64 = mul v11 100.i64;
    v15.i64 = add v13 v14;
    v16.i64 = add v15 v12;
    return v16;
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
            let exercise: unsafe extern "C" fn(u8, u8) -> i64 =
                unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
            for first in [0, 1] {
                for second in [0, 1] {
                    let lhs = if first == 1 { 111 } else { 42 };
                    let rhs = if second == 1 { 222 } else { 42 };
                    let borrowed = if first == 1 { 42 } else { 10 };
                    let second_after = if second == 1 { 222 } else { borrowed };
                    let expected = (lhs + rhs) * 10000 + second_after * 100 + borrowed;
                    assert_eq!(
                        unsafe { exercise(first, second) },
                        expected,
                        "{first} {second} {level:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn loop_carried_value_snapshot_precedes_fresh_storage_reuse() {
    let source = r#"
func private %read(v0.objref<[i64; 2]>) -> i64 {
block0:
    v1.objref<i64> = obj.index v0 1.i64;
    v2.i64 = obj.load v1;
    return v2;
}
func public %exercise(v0.i64) -> i64 {
block0:
    v1.objref<[i64; 2]> = obj.alloc [i64; 2];
    v2.objref<i64> = obj.index v1 1.i64;
    obj.store v2 37.i64;
    jump block1;
block1:
    v3.objref<[i64; 2]> = phi (v1 block0) (v8 block1);
    v4.i64 = phi (0.i64 block0) (v11 block1);
    v5.i64 = call %read v3;
    v6.i64 = add v5 3.i64;
    v8.objref<[i64; 2]> = obj.alloc [i64; 2];
    v9.objref<i64> = obj.index v8 1.i64;
    obj.store v9 v6;
    v11.i64 = add v4 1.i64;
    v12.i1 = lt v11 v0;
    br v12 block1 block2;
block2:
    v13.i64 = call %read v8;
    return v13;
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
        let exercise: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
        for iterations in [1, 2, 3, 17, 64] {
            assert_eq!(
                unsafe { exercise(iterations) },
                37 + 3 * iterations,
                "{level:?}"
            );
        }
    }
}

#[test]
fn overlapping_materialized_loop_pointers_require_heap_storage() {
    // An explicit heap export preserves distinct iterations. A stack export
    // must still fail when an older alias overlaps the next allocation.
    for raw_pointer_phi in [false, true] {
        let source = format!(
            r#"
func public %exercise(v0.i64) -> i64 {{
block0:
    v1.objref<[i64; 2]> = obj.alloc [i64; 2];
    v2.objref<i64> = obj.index v1 1.i64;
    obj.store v2 37.i64;
    {initial_pointer}
    jump block1;
block1:
    {phi}
    v4.i64 = phi (0.i64 block0) (v11 block1);
    {materialize}
    v14.*i64 = gep v13 0.i64 1.i64;
    v15.*i8 = bitcast v14 *i8;
    v16.*i64 = bitcast v15 *i64;
    v8.objref<[i64; 2]> = obj.alloc [i64; 2];
    v9.objref<i64> = obj.index v8 1.i64;
    obj.store v9 v4;
    {next_pointer}
    v5.i64 = mload v16 i64;
    v11.i64 = add v4 1.i64;
    v12.i1 = lt v11 v0;
    br v12 block1 block2;
block2:
    return v5;
}}
"#,
            initial_pointer = if raw_pointer_phi {
                "v17.*[i64; 2] = obj.materialize.stack v1;"
            } else {
                ""
            },
            phi = if raw_pointer_phi {
                "v13.*[i64; 2] = phi (v17 block0) (v18 block1);"
            } else {
                "v3.objref<[i64; 2]> = phi (v1 block0) (v8 block1);"
            },
            materialize = if raw_pointer_phi {
                ""
            } else {
                "v13.*[i64; 2] = obj.materialize.stack v3;"
            },
            next_pointer = if raw_pointer_phi {
                "v18.*[i64; 2] = obj.materialize.stack v8;"
            } else {
                ""
            },
        );
        for level in [OptLevel::O0, OptLevel::O2] {
            let errors = Compile::new(
                parse_verified_native_module(&source),
                CraneliftJitBackend::new(),
            )
            .with_opt_level(level)
            .compile()
            .err()
            .expect("overlapping pointer must be rejected");
            assert!(
                errors
                    .iter()
                    .any(|error| error.to_string().contains("loop-carried fresh object")),
                "{raw_pointer_phi} {level:?}: {errors:?}"
            );
            let heap_source = format!(
                "declare external %free(*[i64; 2]);\n{}",
                source
                    .replace("obj.materialize.stack", "obj.materialize.heap")
                    .replace("v5.i64 = mload v16 i64;", "v5.i64 = mload v16 i64;\n    call %free v13;")
                    .replace("return v5;", "v19.*[i64; 2] = obj.materialize.heap v8;\n    call %free v19;\n    return v5;")
            );
            let artifact = Compile::new(
                parse_verified_native_module(&heap_source),
                CraneliftJitBackend::new(),
            )
            .with_opt_level(level)
            .compile()
            .unwrap();
            let exercise: unsafe extern "C" fn(i64) -> i64 =
                unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
            for iterations in [1, 2, 3, 17] {
                let expected = if iterations == 1 { 37 } else { iterations - 2 };
                assert_eq!(
                    unsafe { exercise(iterations) },
                    expected,
                    "{raw_pointer_phi} {level:?}"
                );
            }
        }
    }
}

#[test]
fn loop_backedge_preserves_projected_alias_lifetimes() {
    for split_latch in [false, true] {
        for carries_old_alias in [false, true] {
            let backedge = if split_latch { "block3" } else { "block1" };
            let source = format!(
                r#"
func public %exercise(v0.i64) -> i64 {{
block0:
    v1.objref<[i64; 2]> = obj.alloc [i64; 2];
    v2.objref<i64> = obj.index v1 1.i64;
    obj.store v2 37.i64;
    jump block1;
block1:
    v3.objref<[i64; 2]> = phi (v1 block0) (v8 {backedge});
    v4.objref<i64> = phi (v2 block0) ({carried} {backedge});
    v5.i64 = phi (0.i64 block0) (v11 {backedge});
    v6.i64 = obj.load v4;
    {latch}
    v7.objref<i64> = obj.index v3 1.i64;
    v8.objref<[i64; 2]> = obj.alloc [i64; 2];
    v9.objref<i64> = obj.index v8 1.i64;
    obj.store v9 v5;
    v11.i64 = add v5 1.i64;
    v12.i1 = lt v11 v0;
    br v12 block1 block2;
block2:
    return v6;
}}
"#,
                carried = if carries_old_alias { "v7" } else { "v9" },
                latch = if split_latch {
                    "jump block3;\nblock3:"
                } else {
                    ""
                },
            );
            for level in [OptLevel::O0, OptLevel::O2] {
                let result = Compile::new(
                    parse_verified_native_module(&source),
                    CraneliftJitBackend::new(),
                )
                .with_opt_level(level)
                .compile();
                if carries_old_alias {
                    let errors = result
                        .err()
                        .expect("backedge alias must prevent slot reuse");
                    assert!(
                        errors.iter().any(|error| {
                            error.to_string().contains("loop-carried fresh object")
                        }),
                        "{split_latch} {level:?}: {errors:?}"
                    );
                } else {
                    let artifact = result.unwrap();
                    let exercise: unsafe extern "C" fn(i64) -> i64 = unsafe {
                        std::mem::transmute(artifact.function_address("exercise").unwrap())
                    };
                    for iterations in [1, 2, 3, 17, 64] {
                        let expected = if iterations == 1 { 37 } else { iterations - 2 };
                        assert_eq!(
                            unsafe { exercise(iterations) },
                            expected,
                            "{split_latch} {level:?}: {iterations}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn loop_phi_aliases_are_live_only_on_their_predecessor_edge() {
    let source = r#"
func public %exercise(v0.i64) -> i64 {
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v1 37.i64;
    jump block1;
block1:
    v2.objref<i64> = phi (v1 block0) (v10 block4);
    v3.i64 = phi (0.i64 block0) (v11 block4);
    v4.i64 = obj.load v2;
    v5.i64 = and v3 1.i64;
    v6.i1 = eq v5 0.i64;
    br v6 block2 block3;
block2:
    v7.i64 = add v4 3.i64;
    v8.objref<i64> = obj.alloc i64;
    obj.store v8 v7;
    jump block4;
block3:
    jump block4;
block4:
    v10.objref<i64> = phi (v8 block2) (v2 block3);
    v11.i64 = add v3 1.i64;
    v12.i1 = lt v11 v0;
    br v12 block1 block5;
block5:
    v13.i64 = obj.load v10;
    return v13;
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
        let exercise: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
        for iterations in [1, 2, 3, 17, 64] {
            assert_eq!(
                unsafe { exercise(iterations) },
                37 + 3 * ((iterations + 1) / 2),
                "{level:?}: {iterations}"
            );
        }
    }
}

#[test]
fn references_held_in_local_aggregates_and_allocations_stay_on_the_stack() {
    // A reference into `v1` rests in an SSA pair, a local pair allocation and
    // a local enum allocation; each copy is read back and written through.
    let source = r#"
type @cell = { i64 };
type @pair = { i64, objref<i64> };
type @slot = enum { #Empty, #Full(objref<i64>) };
func public %exercise(v0.i64) -> i64 {
block0:
    v1.objref<@cell> = obj.alloc @cell;
    v2.objref<@pair> = obj.alloc @pair;
    v3.objref<@slot> = obj.alloc @slot;
    v4.objref<i64> = obj.proj v1 0.i64;
    obj.store v4 v0;
    v5.@pair = insert_value undef.@pair 0.i64 7.i64;
    v6.@pair = insert_value v5 1.i64 v4;
    obj.store v2 v6;
    v7.@slot = enum.make @slot #Full (v4);
    obj.store v3 v7;
    v8.objref<i64> = extract_value v6 1.i64;
    v9.i64 = obj.load v8;
    v10.i64 = add v9 1.i64;
    obj.store v8 v10;
    v11.objref<objref<i64>> = obj.proj v2 1.i64;
    v12.objref<i64> = obj.load v11;
    v13.i64 = obj.load v12;
    v14.i64 = mul v13 10.i64;
    obj.store v12 v14;
    v15.objref<@slot> = enum.assert_variant_ref v3 #Full;
    v16.objref<objref<i64>> = enum.proj v15 #Full 0.i8;
    v17.objref<i64> = obj.load v16;
    v18.i64 = obj.load v17;
    v19.i64 = add v18 2.i64;
    obj.store v17 v19;
    v20.i64 = obj.load v4;
    return v20;
}
"#;
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let artifact = Compile::new(
            parse_verified_native_module(source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(level)
        .compile()
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let exercise: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
        for input in [0, 4, -9] {
            assert_eq!(
                unsafe { exercise(input) },
                (input + 1) * 10 + 2,
                "{level:?}"
            );
        }
    }
}

#[test]
fn references_held_beyond_the_frame_are_rejected() {
    // Each case lets a reference into the local `v1` outlive the frame or the
    // iteration that allocated it, through a holder or an SSA pair.
    for (name, body) in [
        (
            "returned_pair",
            "v2.@pair = insert_value undef.@pair 1.i64 v1;\n    return v2;",
        ),
        (
            "stored_in_argument",
            "v2.@pair = insert_value undef.@pair 1.i64 v1;\n    obj.store v0 v2;\n    return undef.@pair;",
        ),
        (
            "holder_passed_on",
            "v2.objref<@holder> = obj.alloc @holder;\n    v3.objref<objref<i64>> = obj.proj v2 0.i64;\n    obj.store v3 v1;\n    call %keep v2 v0;\n    return undef.@pair;",
        ),
        (
            "recovered_from_holder",
            "v2.objref<@holder> = obj.alloc @holder;\n    v3.objref<objref<i64>> = obj.proj v2 0.i64;\n    obj.store v3 v1;\n    v4.objref<i64> = obj.load v3;\n    v5.@pair = insert_value undef.@pair 1.i64 v4;\n    obj.store v0 v5;\n    return undef.@pair;",
        ),
    ] {
        let source = format!(
            r#"
type @pair = {{ i64, objref<i64> }};
type @holder = {{ objref<i64> }};
func inline(never) private %keep(v0.objref<@holder>, v1.objref<@pair>) {{
block0:
    v2.objref<objref<i64>> = obj.proj v0 0.i64;
    v3.objref<i64> = obj.load v2;
    v4.objref<objref<i64>> = obj.proj v1 1.i64;
    obj.store v4 v3;
    return;
}}
func inline(never) private %{name}(v0.objref<@pair>) -> @pair {{
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v1 5.i64;
    {body}
}}
func public %entry() -> i64 {{
block0:
    v0.objref<@pair> = obj.alloc @pair;
    v1.@pair = call %{name} v0;
    v2.i64 = extract_value v1 0.i64;
    return v2;
}}
"#
        );
        let errors = match Compile::new(
            parse_verified_native_module(&source),
            CraneliftJitBackend::new(),
        )
        .with_opt_level(OptLevel::O0)
        .compile()
        {
            Ok(_) => panic!("{name}: an escaping stack reference was accepted"),
            Err(errors) => errors,
        };
        assert!(
            errors.iter().any(|error| {
                let error = error.to_string();
                error.contains(&format!("native reference lifetime in {name}: unproven"))
            }),
            "{name}: {errors:?}"
        );
    }
}

#[test]
fn loop_allocations_cannot_rest_in_outer_holders() {
    // The holder outlives the iteration whose allocation it references; the
    // next iteration reuses that allocation's slot.
    let source = r#"
type @holder = { objref<i64> };
func public %exercise(v0.i64) -> i64 {
block0:
    v1.objref<@holder> = obj.alloc @holder;
    v2.objref<objref<i64>> = obj.proj v1 0.i64;
    jump block1;
block1:
    v3.i64 = phi (0.i64 block0) (v5 block1);
    v4.objref<i64> = obj.alloc i64;
    obj.store v4 v3;
    obj.store v2 v4;
    v5.i64 = add v3 1.i64;
    v6.i1 = lt v5 v0;
    br v6 block1 block2;
block2:
    v7.objref<i64> = obj.load v2;
    v8.i64 = obj.load v7;
    return v8;
}
"#;
    let errors = match Compile::new(
        parse_verified_native_module(source),
        CraneliftJitBackend::new(),
    )
    .with_opt_level(OptLevel::O0)
    .compile()
    {
        Ok(_) => panic!("a loop allocation held by an outer holder was accepted"),
        Err(errors) => errors,
    };
    assert!(
        errors.iter().any(|error| error
            .to_string()
            .contains("native reference lifetime in exercise: unproven escape of local object")),
        "{errors:?}"
    );
}
