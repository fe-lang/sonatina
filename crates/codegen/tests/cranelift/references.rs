use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftJitBackend};

use super::parse_verified_native_module;

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
fn overlapping_materialized_loop_pointers_are_rejected() {
    // An older alias read after the next allocation names reused storage.
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
                    .any(|error| error.to_string().contains("refers to an earlier instance")),
                "{raw_pointer_phi} {level:?}: {errors:?}"
            );
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
                            error.to_string().contains("refers to an earlier instance")
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
fn references_a_callee_only_packs_stay_on_the_stack() {
    // `%pick` packs a reference into `v1` beside the value it reads and,
    // past a join with no pair, reads only that value back.
    let source = r#"
type @pair = { i64, objref<i64> };
func inline(never) private %pick(v0.objref<i64>, v1.i1) -> i64 {
block0:
    v2.i64 = obj.load v0;
    v3.@pair = insert_value undef.@pair 0.i64 v2;
    v4.@pair = insert_value v3 1.i64 v0;
    br v1 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v5.@pair = phi (v4 block1) (undef.@pair block2);
    br v1 block4 block5;
block4:
    v6.i64 = extract_value v5 0.i64;
    return v6;
block5:
    return 100.i64;
}
func public %exercise(v0.i64) -> i64 {
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v1 v0;
    v2.i64 = call %pick v1 1.i1;
    v3.i64 = call %pick v1 0.i1;
    v4.i64 = add v2 v3;
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
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:?}"));
        let exercise: unsafe extern "C" fn(i64) -> i64 =
            unsafe { std::mem::transmute(artifact.function_address("exercise").unwrap()) };
        for input in [0, 4, -9] {
            assert_eq!(unsafe { exercise(input) }, input + 100, "{level:?}");
        }
    }
}

#[test]
fn references_in_holders_passed_to_calls_and_nested_holders_stay_on_the_stack() {
    // A reference into `v1` rests in the holder `v2`, which `%bump` borrows,
    // and then in `v4`, which holds `v2`; each path writes through it.
    let source = r#"
type @holder = { objref<i64> };
type @outer = { i64, objref<@holder> };
func inline(never) private %bump(v0.objref<@holder>) {
block0:
    v1.objref<objref<i64>> = obj.proj v0 0.i64;
    v2.objref<i64> = obj.load v1;
    v3.i64 = obj.load v2;
    v4.i64 = add v3 1.i64;
    obj.store v2 v4;
    return;
}
func public %exercise(v0.i64) -> i64 {
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v1 v0;
    v2.objref<@holder> = obj.alloc @holder;
    v3.objref<objref<i64>> = obj.proj v2 0.i64;
    obj.store v3 v1;
    call %bump v2;
    v4.objref<@outer> = obj.alloc @outer;
    v5.objref<objref<@holder>> = obj.proj v4 1.i64;
    obj.store v5 v2;
    v6.objref<@holder> = obj.load v5;
    v7.objref<objref<i64>> = obj.proj v6 0.i64;
    v8.objref<i64> = obj.load v7;
    v9.i64 = obj.load v8;
    v10.i64 = mul v9 10.i64;
    obj.store v8 v10;
    v11.i64 = obj.load v1;
    return v11;
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
            assert_eq!(unsafe { exercise(input) }, (input + 1) * 10, "{level:?}");
        }
    }
}

#[test]
fn loop_allocations_may_rest_in_outer_holders() {
    // The holder keeps the last iteration's allocation, which lives until the
    // function returns.
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
        for iterations in [1, 2, 3, 17] {
            assert_eq!(unsafe { exercise(iterations) }, iterations - 1, "{level:?}");
        }
    }
}
