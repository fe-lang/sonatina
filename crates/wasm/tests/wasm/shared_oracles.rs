//! Programs whose results the EVM and native suites already fix.

use sonatina_codegen::{Compile, OptLevel};
use sonatina_wasm::WasmBackend;

use wasmtime::Val;

use super::harness::{Machine, parse};
use crate::alias_execution;

fn compile_at(source: &str, level: OptLevel) -> Result<Vec<u8>, String> {
    Compile::new(parse(source), WasmBackend::new())
        .with_opt_level(level)
        .compile()
        .map(|artifact| artifact.into_bytes())
        .map_err(|errors| format!("{errors:?}"))
}

#[test]
fn the_object_alias_matrix_gives_the_results_the_other_backends_give() {
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let bytes = compile_at(alias_execution::SOURCE, level).expect("the matrix compiles");
        wasmparser::Validator::new()
            .validate_all(&bytes)
            .expect("the module validates");
        let mut machine = Machine::new(&bytes);
        for &(name, expected) in alias_execution::CASES {
            let entry = machine.func(name);
            let got = machine.call(&entry, &[])[0].unwrap_i64();
            assert_eq!(got, expected, "{level:?}: {name}");
        }
        let bytes = compile_at(alias_execution::DISJOINT_SOURCE, level).expect("compiles");
        let mut machine = Machine::new(&bytes);
        let entry = machine.func("disjoint_only");
        assert_eq!(machine.call(&entry, &[])[0].unwrap_i64(), 11, "{level:?}");
    }
}

#[test]
fn a_returned_local_allocation_is_rejected_as_it_is_natively() {
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let error = compile_at(alias_execution::CAPTURE_SOURCE, level)
            .expect_err("the captured reference must not compile");
        assert!(
            error.contains("returns a reference to local object"),
            "{level:?}: {error}"
        );
    }
}

fn machine_at(source: &str, level: OptLevel) -> Machine {
    let bytes = compile_at(source, level).unwrap_or_else(|errors| panic!("{level:?}: {errors}"));
    wasmparser::Validator::new()
        .validate_all(&bytes)
        .expect("the module validates");
    Machine::new(&bytes)
}

fn call_i64(machine: &mut Machine, name: &str, args: &[Val]) -> i64 {
    let entry = machine.func(name);
    machine.call(&entry, args)[0].unwrap_i64()
}

// The remaining programs and their expected results are those of the
// native-target tests of object references (`tests/cranelift/references.rs`).

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
        let mut machine = machine_at(source, level);
        assert_eq!(
            call_i64(&mut machine, "exercise", &[Val::I32(0)]),
            1199,
            "{level:?}"
        );
        assert_eq!(
            call_i64(&mut machine, "exercise", &[Val::I32(1)]),
            9922,
            "{level:?}"
        );
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
        let mut machine = machine_at(source, level);
        for iterations in [1, 2, 3, 17, 64] {
            let got = call_i64(&mut machine, "exercise", &[Val::I64(iterations)]);
            assert_eq!(got, 37 + 3 * iterations, "{level:?}");
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
                let result = compile_at(&source, level);
                if carries_old_alias {
                    let error = result.expect_err("a backedge alias must prevent slot reuse");
                    assert!(
                        error.contains("refers to an earlier instance"),
                        "{split_latch} {level:?}: {error}"
                    );
                } else {
                    let mut machine = machine_at(&source, level);
                    for iterations in [1, 2, 3, 17, 64] {
                        let expected = if iterations == 1 { 37 } else { iterations - 2 };
                        let got = call_i64(&mut machine, "exercise", &[Val::I64(iterations)]);
                        assert_eq!(got, expected, "{split_latch} {level:?}: {iterations}");
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
        let mut machine = machine_at(source, level);
        for iterations in [1, 2, 3, 17, 64] {
            let got = call_i64(&mut machine, "exercise", &[Val::I64(iterations)]);
            assert_eq!(
                got,
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
        let mut machine = machine_at(source, level);
        for input in [0, 4, -9] {
            let got = call_i64(&mut machine, "exercise", &[Val::I64(input)]);
            assert_eq!(got, (input + 1) * 10 + 2, "{level:?}");
        }
    }
}

#[test]
fn references_in_holders_passed_to_calls_and_nested_holders_stay_on_the_stack() {
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
        let mut machine = machine_at(source, level);
        for input in [0, 4, -9] {
            let got = call_i64(&mut machine, "exercise", &[Val::I64(input)]);
            assert_eq!(got, (input + 1) * 10, "{level:?}");
        }
    }
}
