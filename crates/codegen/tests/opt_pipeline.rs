mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::{
    domtree::DomTree,
    loop_analysis::LoopTree,
    optim::{
        Pass, Step, gvn::GvnSolver, licm::LicmSolver, pipeline::Pipeline,
        scalar_canonicalize::ScalarCanonicalize, sccp::SccpSolver,
    },
};
use sonatina_ir::{
    ControlFlowGraph, Module,
    ir_writer::{FuncWriter, ModuleWriter},
    module::FuncRef,
};
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/opt_pipeline/",
    glob: "*.sntn"
)]
fn test_opt_pipeline(fixture: Fixture<&str>) {
    let mut parsed = common::parse_module(fixture.path());
    Pipeline::size().run(&mut parsed.module);

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    snap_test!(writer.dump_string(), fixture.path());
}

#[test]
fn sccp_folds_constant_uaddo_results() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry() -> i256 {
    block0:
        (v0.i256, v1.i1) = uaddo 1.i256 2.i256;
        br v1 block1 block2;

    block1:
        return 99.i256;

    block2:
        return v0;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_not_contains(&module, func_ref, "uaddo");
    assert_fast_verified(&module);
}

#[test]
fn sccp_folds_uaddo_zero_identities() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
    block0:
        (v1.i256, v2.i1) = uaddo v0 0.i256;
        br v2 block1 block2;

    block1:
        return 99.i256;

    block2:
        return v1;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_not_contains(&module, func_ref, "uaddo");
    assert_fast_verified(&module);
}

#[test]
fn sccp_removes_uaddo_when_other_result_is_dead() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
    block0:
        (v1.i256, v2.i1) = uaddo v0 0.i256;
        return v1;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_not_contains(&module, func_ref, "uaddo");
    assert_fast_verified(&module);
}

#[test]
fn sccp_folds_checked_overflow_identities() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
    block0:
        (v1.i256, v2.i1) = usubo v0 0.i256;
        (v3.i256, v4.i1) = umulo v1 1.i256;
        (v5.i256, v6.i1) = evm_udivo v3 1.i256;
        (v7.i256, v8.i1) = evm_umodo v5 1.i256;
        br v8 block1 block2;

    block1:
        return v7;

    block2:
        return v5;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    for needle in ["usubo", "umulo", "evm_udivo", "evm_umodo"] {
        assert_func_not_contains(&module, func_ref, needle);
    }
    assert_fast_verified(&module);
}

#[test]
fn sccp_folds_width_sensitive_evm_saturating_constants() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry() -> i256 {
    block0:
        v0.i256 = evm_uaddsat 255.i256 1.i256 i8;
        v1.i1 = eq v0 255.i256;
        br v1 block1 block2;

    block1:
        return v0;

    block2:
        return 0.i256;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_not_contains(&module, func_ref, "evm_uaddsat");
    assert_fast_verified(&module);
}

#[test]
fn sccp_folds_one_sided_evm_peepholes() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = evm_add_mod v0 v1 0.i256;
        v3.i256 = evm_mul_mod v0 v1 0.i256;
        v4.i256 = evm_exp v0 0.i256;
        v5.i256 = evm_exp 1.i256 v1;
        v6.i256 = evm_byte v0 0.i256;
        v7.i256 = evm_clz 0.i256;
        v8.i256 = add v2 v3;
        v9.i256 = add v8 v4;
        v10.i256 = add v9 v5;
        v11.i256 = add v10 v6;
        v12.i256 = add v11 v7;
        return v12;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 258.i256;"),
        "unexpected SCCP output:\n{dumped}"
    );
    for needle in [
        "evm_add_mod",
        "evm_mul_mod",
        "evm_exp",
        "evm_byte",
        "evm_clz",
    ] {
        assert!(
            !dumped.contains(needle),
            "expected {needle} to fold away:\n{dumped}"
        );
    }
    assert_fast_verified(&module);
}

#[test]
fn sccp_folds_snego_zero_identity() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry() -> i256 {
    block0:
        (v0.i256, v1.i1) = snego 0.i256;
        br v1 block1 block2;

    block1:
        return 99.i256;

    block2:
        return v0;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_not_contains(&module, func_ref, "snego");
    assert_fast_verified(&module);
}

#[test]
fn sccp_folds_const_load_from_const_ref() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

global private const i256 $value = 77;

func public %entry() -> i256 {
    block0:
        v0.constref<i256> = const.ref $value;
        v1.i256 = const.load v0;
        return v1;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_not_contains(&module, func_ref, "const.load");
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 77.i256;"),
        "const.load(const.ref) should fold to an immediate:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn sccp_folds_const_load_through_const_proj() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

global private const @pair $pair = {10, 20};

func public %entry() -> i256 {
    block0:
        v0.constref<@pair> = const.ref $pair;
        v1.constref<i256> = const.proj v0 1.i8;
        v2.i256 = const.load v1;
        return v2;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_not_contains(&module, func_ref, "const.load");
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 20.i256;"),
        "const.load(const.proj(const.ref ...)) should fold to an immediate:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn sccp_folds_const_load_with_proven_constant_dynamic_index() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [11, 22, 33, 44];

func public %entry() -> i256 {
    block0:
        v0.i8 = add 0.i8 1.i8;
        v1.constref<[i256; 4]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_not_contains(&module, func_ref, "const.load");
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 22.i256;"),
        "const.load with an SCCP-proven dynamic index should fold to an immediate:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn sccp_folds_const_load_through_same_path_phi() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

global private const @pair $pair = {10, 20};

func public %entry(v0.i1) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        v1.constref<@pair> = const.ref $pair;
        v2.constref<i256> = const.proj v1 1.i8;
        jump block3;

    block2:
        v3.constref<@pair> = const.ref $pair;
        v4.constref<i256> = const.proj v3 1.i8;
        jump block3;

    block3:
        v5.constref<i256> = phi (v2 block1) (v4 block2);
        v6.i256 = const.load v5;
        return v6;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_not_contains(&module, func_ref, "const.load");
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 20.i256;"),
        "const.load through a phi of identical paths should fold to an immediate:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn sccp_keeps_const_load_with_unknown_dynamic_index() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [11, 22, 33, 44];

func public %entry(v0.i8) -> i256 {
    block0:
        v1.constref<[i256; 4]> = const.ref $arr;
        v2.constref<i256> = const.index v1 v0;
        v3.i256 = const.load v2;
        return v3;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_contains(&module, func_ref, "const.load");
    assert_fast_verified(&module);
}

#[test]
fn sccp_keeps_const_load_with_loop_varying_index_phi() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

global private const [i256; 4] $arr = [11, 22, 33, 44];

func public %entry() -> i256 {
    block0:
        jump block1;

    block1:
        v0.i256 = phi (0.i256 block0) (v5 block3);
        v1.i256 = phi (0.i256 block0) (v4 block3);
        v2.i1 = lt v0 4.i256;
        br v2 block2 block4;

    block2:
        v3.constref<[i256; 4]> = const.ref $arr;
        v6.constref<i256> = const.index v3 v0;
        v7.i256 = const.load v6;
        v4.i256 = add v1 v7;
        jump block3;

    block3:
        v5.i256 = add v0 1.i256;
        jump block1;

    block4:
        return v1;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("const.load"),
        "loop-varying const.load index should not fold to a single immediate:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn sccp_keeps_const_load_with_reused_dynamic_index_value() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

global private const [[i256; 2]; 2] $arr = [[11, 22], [33, 44]];

func public %entry() -> i256 {
    block0:
        jump block1;

    block1:
        v0.i256 = phi (0.i256 block0) (v5 block3);
        v1.i256 = phi (0.i256 block0) (v4 block3);
        v2.i1 = lt v0 2.i256;
        br v2 block2 block4;

    block2:
        v3.constref<[[i256; 2]; 2]> = const.ref $arr;
        v6.constref<[i256; 2]> = const.index v3 v0;
        v7.constref<i256> = const.index v6 v0;
        v8.i256 = const.load v7;
        v4.i256 = add v1 v8;
        jump block3;

    block3:
        v5.i256 = add v0 1.i256;
        jump block1;

    block4:
        return v1;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("const.load"),
        "reused loop-varying index should not fold to a single immediate:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn sccp_preserves_maybe_undef_saturating_zero_identities() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i1) -> i8 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v1.i8 = phi (undef.i8 block1) (7.i8 block2);
        v2.i8 = usubsat 0.i8 v1;
        v3.i8 = umulsat v1 0.i8;
        v4.i8 = add v2 v3;
        return v4;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("usubsat"),
        "maybe-undef usubsat should not fold to zero:\n{dumped}"
    );
    assert!(
        dumped.contains("umulsat"),
        "maybe-undef umulsat should not fold to zero:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn sccp_preserves_maybe_undef_one_sided_evm_folds() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i1) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v1.i256 = phi (undef.i256 block1) (7.i256 block2);
        v2.i256 = evm_add_mod v1 3.i256 0.i256;
        v3.i256 = evm_exp v1 0.i256;
        v4.i256 = evm_exp 1.i256 v1;
        v5.i256 = evm_byte v1 0.i256;
        v6.i256 = add v2 v3;
        v7.i256 = add v4 v5;
        v8.i256 = add v6 v7;
        return v8;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert_eq!(
        dumped.matches("evm_add_mod").count(),
        1,
        "unexpected SCCP output:\n{dumped}"
    );
    assert_eq!(
        dumped.matches("evm_exp").count(),
        2,
        "unexpected SCCP output:\n{dumped}"
    );
    assert_eq!(
        dumped.matches("evm_byte").count(),
        1,
        "unexpected SCCP output:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn sccp_prunes_complex_loop_without_adce_block_delete_panic() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %complex_loop() -> i8 {
    block0:
        v0.i8 = add 1.i8 0.i8;
        v1.i8 = add v0 0.i8;
        v2.i8 = sub v0 1.i8;
        jump block1;

    block1:
        v3.i8 = phi (v9 block6) (v0 block0);
        v4.i8 = phi (v10 block6) (v2 block0);
        v5.i1 = lt v4 100.i8;
        br v5 block2 block3;

    block2:
        v6.i1 = lt v3 20.i8;
        br v6 block4 block5;

    block3:
        return v3;

    block4:
        v7.i8 = add 1.i8 v4;
        jump block6;

    block5:
        v8.i8 = add v4 2.i8;
        jump block6;

    block6:
        v9.i8 = phi (v0 block4) (v4 block5);
        v10.i8 = phi (v7 block4) (v8 block5);
        jump block1;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 1.i8;"),
        "complex loop should fold to a constant return:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn function_passes_scalarize_enum_bearing_products_without_lowering_enums() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

type @option_i256 = enum {
    #None,
    #Some(i256),
};

type @wrapper = {@option_i256, i256};

func private %entry(v0.i256) -> i256 {
    block0:
        v1.@option_i256 = enum.make @option_i256 #Some (v0);
        v2.@wrapper = insert_value undef.@wrapper 0.i8 v1;
        v3.@wrapper = insert_value v2 1.i8 1.i256;
        v4.@option_i256 = extract_value v3 0.i8;
        v5.i1 = enum.is_variant v4 #Some;
        br v5 block1 block2;

    block1:
        v6.i256 = enum.extract v4 #Some 0.i8;
        v7.i256 = extract_value v3 1.i8;
        v8.i256 = add v6 v7;
        return v8;

    block2:
        return 0.i256;
}
"#,
    );
    let mut pipeline = Pipeline::new();
    pipeline.add_step(Step::FuncPasses(vec![
        Pass::CfgCleanup,
        Pass::AggregateCombine,
        Pass::AggregateScalarize,
        Pass::CfgCleanup,
    ]));
    let mut module = module;
    pipeline.run(&mut module);
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        !dumped.contains("@wrapper") && !dumped.contains("__enum_lowered"),
        "enum-bearing product should scalarize without erasing enum semantics:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn function_passes_use_object_effect_summaries_across_private_calls() {
    let mut parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %peek(v0.objref<@pair>) {
    block0:
        v1.objref<i256> = obj.proj v0 0.i8;
        v2.i256 = obj.load v1;
        return;
}

func private %entry(v0.i256) -> i256 {
    block0:
        v1.objref<@pair> = obj.alloc @pair;
        v2.objref<i256> = obj.proj v1 0.i8;
        obj.store v2 v0;
        call %peek v1;
        v3.i256 = obj.load v2;
        return v3;
}
"#,
    )
    .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let entry = find_func_by_name(&parsed.module, "entry");

    let mut pipeline = Pipeline::new();
    pipeline.add_step(Step::FuncPasses(vec![
        Pass::AggregateCombine,
        Pass::ObjectLoadStore,
        Pass::CfgCleanup,
    ]));
    pipeline.run(&mut parsed.module);

    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(
        dumped.contains("call %peek v1;"),
        "read-only helper call should remain visible:\n{dumped}"
    );
    assert!(
        !dumped.contains("obj.load"),
        "summary-aware object load/store should forward across the call:\n{dumped}"
    );
    assert!(
        dumped.contains("return v0;"),
        "entry should return the stored value after the read-only call:\n{dumped}"
    );
    assert_fast_verified(&parsed.module);
}

#[test]
fn pipeline_inlines_multi_use_object_helper_family_before_object_cleanup() {
    let mut parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

type @triple = { i256, i256, i256 };

func private %write(v0.objref<@triple>, v1.i256, v2.i256, v3.i256) {
    block0:
        v4.objref<i256> = obj.proj v0 0.i8;
        v5.objref<i256> = obj.proj v0 1.i8;
        v6.objref<i256> = obj.proj v0 2.i8;
        obj.store v4 v1;
        obj.store v5 v2;
        obj.store v6 v3;
        return;
}

func public %entry(v0.i256, v1.i256, v2.i256, v3.i256, v4.i256, v5.i256) -> i256 {
    block0:
        v6.objref<@triple> = obj.alloc @triple;
        call %write v6 v0 v1 v2;
        call %write v6 v3 v4 v5;
        v7.objref<i256> = obj.proj v6 0.i8;
        v8.i256 = obj.load v7;
        return v8;
}
"#,
    )
    .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let entry = find_func_by_name(&parsed.module, "entry");

    Pipeline::size().run(&mut parsed.module);

    let dumped = parsed
        .module
        .func_store
        .view(entry, |func| FuncWriter::new(entry, func).dump_string());
    assert!(
        !dumped.contains("call %write"),
        "object-aware inline budget should inline the multi-use helper:\n{dumped}"
    );
    assert!(
        dumped.contains("return v3;"),
        "later object cleanup should forward the final stored value:\n{dumped}"
    );
    assert_fast_verified(&parsed.module);
}

#[test]
fn sccp_deletes_unreachable_region_with_cross_block_uses() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry() -> i256 {
    block0:
        v0.i1 = eq 0.i256 1.i256;
        br v0 block1 block2;

    block1:
        v1.i256 = add 40.i256 2.i256;
        jump block3;

    block2:
        return 7.i256;

    block3:
        return v1;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 7.i256;"),
        "unreachable region should be pruned without leaving live users:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_deletes_unreachable_region_with_cross_block_uses() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry() -> i256 {
    block0:
        v0.i1 = eq 0.i256 1.i256;
        br v0 block1 block2;

    block1:
        v1.i256 = add 40.i256 2.i256;
        jump block3;

    block2:
        return 7.i256;

    block3:
        return v1;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 7.i256;"),
        "unreachable region should be pruned without leaving live users:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_deletes_unreachable_region_with_ptr_to_int_cross_block_use() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

global private i32 $G0 = 0;

func public %entry() -> i256 {
    block0:
        v0.i1 = eq 0.i256 1.i256;
        br v0 block1 block2;

    block1:
        v1.i256 = ptr_to_int $G0 i256;
        jump block3;

    block2:
        return 7.i256;

    block3:
        v2.i256 = add v1 1.i256;
        return v2;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 7.i256;"),
        "dead ptr_to_int region should be pruned without leaving live users:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_eliminates_redundant_checked_overflow_ops() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256, v1.i256) -> i256 {
    block0:
        (v2.i256, v3.i1) = umulo v0 v1;
        (v4.i256, v5.i1) = umulo v0 v1;
        v6.i1 = or v3 v5;
        (v7.i256, v8.i1) = evm_udivo v2 v1;
        (v9.i256, v10.i1) = evm_udivo v4 v1;
        v11.i1 = or v6 v8;
        v12.i1 = or v11 v10;
        br v12 block1 block2;

    block1:
        return v9;

    block2:
        return v7;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert_eq!(
        dumped.matches("umulo").count(),
        1,
        "unexpected GVN output:\n{dumped}"
    );
    assert_eq!(
        dumped.matches("evm_udivo").count(),
        1,
        "unexpected GVN output:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_folds_width_sensitive_evm_saturating_constants() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry() -> i256 {
    block0:
        v0.i256 = evm_umulsat 200.i256 2.i256 i8;
        v1.i256 = evm_ssubsat -128.i256 1.i256 i8;
        v2.i256 = add v0 v1;
        return v2;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 127.i256;"),
        "unexpected GVN output:\n{dumped}"
    );
    assert_eq!(
        dumped.matches("evm_umulsat").count(),
        0,
        "unexpected GVN output:\n{dumped}"
    );
    assert_eq!(
        dumped.matches("evm_ssubsat").count(),
        0,
        "unexpected GVN output:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_cses_commutative_evm_saturating_ops() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = evm_uaddsat v0 v1 i8;
        v3.i256 = evm_uaddsat v1 v0 i8;
        v4.i256 = evm_umulsat v0 v1 i8;
        v5.i256 = evm_umulsat v1 v0 i8;
        v6.i256 = add v2 v3;
        v7.i256 = add v4 v5;
        v8.i256 = add v6 v7;
        return v8;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert_eq!(
        dumped.matches("evm_uaddsat").count(),
        1,
        "unexpected GVN output:\n{dumped}"
    );
    assert_eq!(
        dumped.matches("evm_umulsat").count(),
        1,
        "unexpected GVN output:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_preserves_maybe_undef_saturating_zero_identities() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i1) -> i8 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v1.i8 = phi (undef.i8 block1) (7.i8 block2);
        v2.i8 = usubsat 0.i8 v1;
        v3.i8 = umulsat v1 0.i8;
        v4.i8 = add v2 v3;
        return v4;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("usubsat"),
        "maybe-undef usubsat should not fold to zero:\n{dumped}"
    );
    assert!(
        dumped.contains("umulsat"),
        "maybe-undef umulsat should not fold to zero:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_preserves_maybe_undef_one_sided_evm_folds() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i1) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v1.i256 = phi (undef.i256 block1) (7.i256 block2);
        v2.i256 = evm_add_mod v1 3.i256 0.i256;
        v3.i256 = evm_exp v1 0.i256;
        v4.i256 = evm_exp 1.i256 v1;
        v5.i256 = evm_byte v1 0.i256;
        v6.i256 = add v2 v3;
        v7.i256 = add v4 v5;
        v8.i256 = add v6 v7;
        return v8;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert_eq!(
        dumped.matches("evm_add_mod").count(),
        1,
        "unexpected GVN output:\n{dumped}"
    );
    assert_eq!(
        dumped.matches("evm_exp").count(),
        2,
        "unexpected GVN output:\n{dumped}"
    );
    assert_eq!(
        dumped.matches("evm_byte").count(),
        1,
        "unexpected GVN output:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_folds_one_sided_evm_peepholes() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = evm_add_mod v0 v1 0.i256;
        v3.i256 = evm_mul_mod v0 v1 0.i256;
        v4.i256 = evm_exp v0 0.i256;
        v5.i256 = evm_exp 1.i256 v1;
        v6.i256 = evm_byte v0 0.i256;
        v7.i256 = evm_clz 0.i256;
        v8.i256 = add v2 v3;
        v9.i256 = add v8 v4;
        v10.i256 = add v9 v5;
        v11.i256 = add v10 v6;
        v12.i256 = add v11 v7;
        return v12;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains("return 258.i256;"),
        "unexpected GVN output:\n{dumped}"
    );
    for needle in [
        "evm_add_mod",
        "evm_mul_mod",
        "evm_exp",
        "evm_byte",
        "evm_clz",
    ] {
        assert!(
            !dumped.contains(needle),
            "expected {needle} to fold away:\n{dumped}"
        );
    }
    assert_fast_verified(&module);
}

#[test]
fn gvn_cses_eq_zero_with_is_zero() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i1 = eq v0 0.i256;
        v2.i1 = is_zero v0;
        v3.i256 = zext v1 i256;
        v4.i256 = zext v2 i256;
        v5.i256 = add v3 v4;
        return v5;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert_eq!(
        dumped.matches(" = eq ").count() + dumped.matches(" = is_zero ").count(),
        1,
        "expected eq-zero and is_zero to CSE:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn scalar_canonicalize_rewrites_eq_zero_to_is_zero() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i1 = eq v0 0.i256;
        v2.i256 = zext v1 i256;
        return v2;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        assert!(ScalarCanonicalize::new().run(func));
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains(" = is_zero "),
        "expected eq-zero to rewrite to is_zero:\n{dumped}"
    );
    assert!(
        !dumped.contains(" = eq "),
        "expected eq-zero rewrite to remove eq:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_cses_mul_by_two_with_shl_one() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = mul v0 2.i256;
        v2.i256 = shl 1.i256 v0;
        v3.i256 = add v1 v2;
        return v3;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert_eq!(
        dumped.matches(" = mul ").count() + dumped.matches(" = shl ").count(),
        1,
        "expected mul-by-two and shl-one to CSE:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn scalar_canonicalize_rewrites_mul_by_pow2_to_shl() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = mul v0 8.i256;
        return v1;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        assert!(ScalarCanonicalize::new().run(func));
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains(" = shl 3.i256 "),
        "expected mul-by-pow2 to rewrite to shl:\n{dumped}"
    );
    assert!(
        !dumped.contains(" = mul "),
        "expected mul-by-pow2 rewrite to remove mul:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn gvn_cses_add_neg_with_sub() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = neg v1;
        v3.i256 = add v0 v2;
        v4.i256 = sub v0 v1;
        v5.i256 = add v3 v4;
        return v5;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert_eq!(
        dumped.matches(" = add ").count() + dumped.matches(" = sub ").count(),
        2,
        "expected add-neg and sub to CSE, leaving only one producer plus the final add:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn scalar_canonicalize_rewrites_add_neg_to_sub() {
    let (module, func_ref) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = neg v1;
        v3.i256 = add v0 v2;
        return v3;
}
"#,
    );
    module.func_store.modify(func_ref, |func| {
        assert!(ScalarCanonicalize::new().run(func));
    });
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains(" = sub v0 v1;"),
        "expected add-neg to rewrite to sub:\n{dumped}"
    );
    assert!(
        !dumped.contains(" = add v0 v2;"),
        "expected add-neg rewrite to remove add-neg form:\n{dumped}"
    );
    assert_fast_verified(&module);
}

#[test]
fn standalone_function_passes_support_live_multi_result_input() {
    let (sccp_module, sccp_func) = parse_test_module(STANDALONE_MULTI_RESULT_SRC);
    sccp_module.func_store.modify(sccp_func, |func| {
        let mut cfg = ControlFlowGraph::new();
        SccpSolver::new().run(func, &mut cfg);
    });
    assert_func_contains(&sccp_module, sccp_func, "uaddo");
    assert_fast_verified(&sccp_module);

    let (gvn_module, gvn_func) = parse_test_module(STANDALONE_MULTI_RESULT_SRC);
    gvn_module.func_store.modify(gvn_func, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    assert_func_contains(&gvn_module, gvn_func, "uaddo");
    assert_fast_verified(&gvn_module);

    let (licm_module, licm_func) = parse_test_module(STANDALONE_MULTI_RESULT_LOOP_SRC);
    licm_module.func_store.modify(licm_func, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut lpt = LoopTree::new();
        LicmSolver::new().run(func, &mut cfg, &mut lpt);
    });
    assert_func_contains(&licm_module, licm_func, "uaddo");
    assert_fast_verified(&licm_module);
}

#[test]
fn gvn_tolerates_live_multi_result_calls() {
    let (module, _) = parse_test_module(
        r#"
target = "evm-ethereum-osaka"

declare external %pair() -> (i256, i1);

func public %entry() -> i256 {
    block0:
        (v0.i256, v1.i1) = call %pair;
        br v1 block1 block2;

    block1:
        return 0.i256;

    block2:
        return v0;
}
"#,
    );
    let func_ref = find_func_by_name(&module, "entry");
    module.func_store.modify(func_ref, |func| {
        let mut cfg = ControlFlowGraph::new();
        let mut domtree = DomTree::new();
        GvnSolver::new().run(func, &mut cfg, &mut domtree);
    });
    assert_func_contains(&module, func_ref, "call %pair");
    assert_fast_verified(&module);
}

#[test]
fn balanced_pipeline_preserves_live_multi_result_ir_until_lowering() {
    let (mut module, func_ref) = parse_test_module(STANDALONE_MULTI_RESULT_SRC);
    Pipeline::size().run(&mut module);
    assert_func_contains(&module, func_ref, "uaddo");
    assert_fast_verified(&module);
}

const STANDALONE_MULTI_RESULT_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256, v1.i256) -> i256 {
    block0:
        (v2.i256, v3.i1) = uaddo v0 v1;
        br v3 block1 block2;

    block1:
        return v2;

    block2:
        return v0;
}
"#;

const STANDALONE_MULTI_RESULT_LOOP_SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i256, v1.i256, v2.i1) -> i256 {
    block0:
        jump block1;

    block1:
        (v3.i256, v4.i1) = uaddo v0 v1;
        br v2 block2 block3;

    block2:
        jump block1;

    block3:
        return v3;
}
"#;

fn parse_test_module(src: &str) -> (Module, FuncRef) {
    let parsed = parse_module(src).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
    let func_ref = parsed
        .module
        .funcs()
        .into_iter()
        .next()
        .expect("test module must contain a function");
    (parsed.module, func_ref)
}

fn find_func_by_name(module: &Module, name: &str) -> FuncRef {
    module
        .funcs()
        .into_iter()
        .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
        .unwrap_or_else(|| panic!("function `{name}` should exist"))
}

fn assert_func_not_contains(module: &Module, func_ref: FuncRef, needle: &str) {
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        !dumped.contains(needle),
        "function still contains `{needle}`:\n{dumped}"
    );
}

fn assert_func_contains(module: &Module, func_ref: FuncRef, needle: &str) {
    let dumped = module.func_store.view(func_ref, |func| {
        FuncWriter::new(func_ref, func).dump_string()
    });
    assert!(
        dumped.contains(needle),
        "function did not contain `{needle}`:\n{dumped}"
    );
}

fn assert_fast_verified(module: &Module) {
    let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Fast));
    assert!(report.is_ok(), "module failed verification: {report:?}");
}
