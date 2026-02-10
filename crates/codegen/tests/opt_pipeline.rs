mod common;

use dir_test::{Fixture, dir_test};
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
        inliner::{InlineStats, Inliner, InlinerConfig},
        licm::LicmSolver,
        sccp::SccpSolver,
    },
};
use sonatina_ir::{
    ControlFlowGraph, Function, Module,
    ir_writer::{FuncWriter, ModuleWriter},
    module::FuncRef,
};

const MAX_POLISH_ITERS: usize = 2;
const MAX_OPT_PIPELINE_ITERS: usize = 4;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/opt_pipeline/",
    glob: "*.sntn"
)]
fn test_opt_pipeline(fixture: Fixture<&str>) {
    let mut parsed = common::parse_module(fixture.path());
    func_behavior::analyze_module(&parsed.module);

    run_opt_pipeline_loop(&mut parsed.module, &parsed.debug.func_order);

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

fn run_opt_pipeline_loop(module: &mut Module, func_order: &[FuncRef]) {
    let mut inliner = Inliner::new(InlinerConfig::default());
    for _ in 0..MAX_OPT_PIPELINE_ITERS {
        func_behavior::analyze_module(module);
        run_function_round(module, func_order);
        func_behavior::analyze_module(module);
        let inline_stats = inliner.run(module);
        if !inliner_changed(&inline_stats) {
            break;
        }
    }
}

fn run_function_round(module: &mut Module, func_order: &[FuncRef]) {
    for func_ref in func_order {
        module.func_store.modify(*func_ref, |func| {
            run_baseline_pipeline(func);
            run_polish_pipeline(func, *func_ref);
        });
    }
}

fn inliner_changed(stats: &InlineStats) -> bool {
    stats.calls_removed > 0 || stats.calls_rewritten > 0 || stats.calls_spliced > 0
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
