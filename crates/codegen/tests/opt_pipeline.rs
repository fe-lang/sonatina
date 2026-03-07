mod common;

use std::collections::BTreeMap;

use dir_test::{Fixture, dir_test};
use rustc_hash::FxHashSet;
use sonatina_codegen::{
    analysis::func_behavior,
    cfg_edit::CleanupMode,
    domtree::DomTree,
    loop_analysis::LoopTree,
    optim::{
        adce::AdceSolver,
        cfg_cleanup::CfgCleanup,
        dead_func::{DeadFuncElimConfig, collect_object_roots, run_dead_func_elim},
        egraph::run_egraph_pass,
        gvn::GvnSolver,
        inliner::{Inliner, InlinerConfig},
        licm::LicmSolver,
        pipeline::Pipeline,
        sccp::SccpSolver,
    },
};
use sonatina_ir::{
    ControlFlowGraph, Function, InstDowncast, Module,
    inst::data::{GetFunctionPtr, SymAddr, SymSize, SymbolRef},
    ir_writer::{FuncWriter, ModuleWriter},
    module::FuncRef,
};
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

const MAX_POLISH_ITERS: usize = 2;
const MAX_OPT_PIPELINE_ITERS: usize = 4;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/opt_pipeline/",
    glob: "*.sntn"
)]
fn test_opt_pipeline(fixture: Fixture<&str>) {
    let mut parsed = common::parse_module(fixture.path());
    func_behavior::analyze_module(&parsed.module);

    run_opt_pipeline_loop(&mut parsed.module);

    let roots = collect_object_roots(&parsed.module);
    run_dead_func_elim(&mut parsed.module, &roots, DeadFuncElimConfig::default());

    let mut writer = ModuleWriter::with_debug_provider(&parsed.module, &parsed.debug);
    snap_test!(writer.dump_string(), fixture.path());
}

fn run_baseline_pipeline(func: &mut Function) {
    run_sccp(func);
    CfgCleanup::new(CleanupMode::Strict).run(func);
    AdceSolver::new().run(func);
    run_licm(func);
    run_egraph_pass(func);
}

fn run_opt_pipeline_loop(module: &mut Module) {
    let mut inliner = Inliner::new(InlinerConfig::default());
    let mut funcs_to_optimize = object_reachable_funcs(module);
    for _ in 0..MAX_OPT_PIPELINE_ITERS {
        if funcs_to_optimize.is_empty() {
            break;
        }
        func_behavior::analyze_module(module);
        run_function_round(module, &funcs_to_optimize);
        func_behavior::analyze_module(module);
        let reachable_before_inline = object_reachable_funcs(module);
        let before_inline = module_fingerprint_map(module, &reachable_before_inline);
        inliner.run(module);
        let reachable_after_inline = object_reachable_funcs(module);
        let after_inline = module_fingerprint_map(module, &reachable_after_inline);
        funcs_to_optimize = changed_funcs(&before_inline, &after_inline);
        if funcs_to_optimize.is_empty() {
            break;
        }
    }
}

fn run_function_round(module: &mut Module, reachable_funcs: &[FuncRef]) {
    for func_ref in reachable_funcs {
        module.func_store.modify(*func_ref, |func| {
            run_baseline_pipeline(func);
            run_polish_pipeline(func, *func_ref);
        });
    }
}

fn run_polish_pipeline(func: &mut Function, func_ref: FuncRef) {
    for _ in 0..MAX_POLISH_ITERS {
        let before = func_fingerprint(func, func_ref);
        run_sccp(func);
        CfgCleanup::new(CleanupMode::Strict).run(func);
        AdceSolver::new().run(func);
        run_egraph_pass(func);
        if before == func_fingerprint(func, func_ref) {
            break;
        }
    }
}

fn run_sccp(func: &mut Function) {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    SccpSolver::new().run(func, &mut cfg);
}

fn run_licm(func: &mut Function) {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    let mut domtree = DomTree::new();
    domtree.compute(&cfg);
    let mut lpt = LoopTree::new();
    lpt.compute(&cfg, &domtree);
    LicmSolver::new().run(func, &mut cfg, &mut lpt);
    CfgCleanup::new(CleanupMode::Strict).run(func);
}

fn func_fingerprint(func: &Function, func_ref: FuncRef) -> String {
    FuncWriter::new(func_ref, func).dump_string()
}

fn module_fingerprint_map(module: &Module, func_refs: &[FuncRef]) -> BTreeMap<FuncRef, String> {
    let mut fingerprint = BTreeMap::new();
    for func_ref in func_refs {
        module.func_store.view(*func_ref, |func| {
            fingerprint.insert(*func_ref, func_fingerprint(func, *func_ref));
        });
    }
    fingerprint
}

fn changed_funcs(
    before: &BTreeMap<FuncRef, String>,
    after: &BTreeMap<FuncRef, String>,
) -> Vec<FuncRef> {
    let mut changed = Vec::new();
    for (func_ref, after_sig) in after {
        if before.get(func_ref) != Some(after_sig) {
            changed.push(*func_ref);
        }
    }
    changed.sort_unstable();
    changed
}

fn object_reachable_funcs(module: &Module) -> Vec<FuncRef> {
    let roots = collect_object_roots(module);
    let mut reachable = FxHashSet::default();
    let mut worklist = Vec::new();

    for root in roots {
        enqueue_reachable(module, root, &mut reachable, &mut worklist);
    }

    while let Some(func_ref) = worklist.pop() {
        if !module.ctx.func_linkage(func_ref).has_definition() {
            continue;
        }

        module.func_store.view(func_ref, |func| {
            let is = func.inst_set();
            for block in func.layout.iter_block() {
                for inst_id in func.layout.iter_inst(block) {
                    if let Some(call) = func.dfg.call_info(inst_id) {
                        enqueue_reachable(module, call.callee(), &mut reachable, &mut worklist);
                    }

                    let inst = func.dfg.inst(inst_id);
                    if let Some(ptr) = <&GetFunctionPtr as InstDowncast>::downcast(is, inst) {
                        enqueue_reachable(module, *ptr.func(), &mut reachable, &mut worklist);
                    }

                    if let Some(sym) = <&SymAddr as InstDowncast>::downcast(is, inst)
                        && let SymbolRef::Func(sym_func_ref) = sym.sym()
                    {
                        enqueue_reachable(module, *sym_func_ref, &mut reachable, &mut worklist);
                    }

                    if let Some(sym) = <&SymSize as InstDowncast>::downcast(is, inst)
                        && let SymbolRef::Func(sym_func_ref) = sym.sym()
                    {
                        enqueue_reachable(module, *sym_func_ref, &mut reachable, &mut worklist);
                    }
                }
            }
        });
    }

    let mut reachable: Vec<_> = reachable.into_iter().collect();
    reachable.sort_unstable();
    reachable
}

fn enqueue_reachable(
    module: &Module,
    func_ref: FuncRef,
    reachable: &mut FxHashSet<FuncRef>,
    worklist: &mut Vec<FuncRef>,
) {
    if module.ctx.declared_funcs.contains_key(&func_ref) && reachable.insert(func_ref) {
        worklist.push(func_ref);
    }
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
