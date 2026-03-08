mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::{
    domtree::DomTree,
    loop_analysis::LoopTree,
    optim::{
        egraph::run_egraph_pass, gvn::GvnSolver, licm::LicmSolver, pipeline::Pipeline,
        sccp::SccpSolver,
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
    Pipeline::balanced().run(&mut parsed.module);

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

    let (egraph_module, egraph_func) = parse_test_module(STANDALONE_MULTI_RESULT_SRC);
    egraph_module
        .func_store
        .modify(egraph_func, run_egraph_pass);
    assert_func_contains(&egraph_module, egraph_func, "uaddo");
    assert_fast_verified(&egraph_module);
}

#[test]
fn balanced_pipeline_preserves_live_multi_result_ir_until_lowering() {
    let (mut module, func_ref) = parse_test_module(STANDALONE_MULTI_RESULT_SRC);
    Pipeline::balanced().run(&mut module);
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
