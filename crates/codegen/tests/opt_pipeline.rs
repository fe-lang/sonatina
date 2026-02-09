mod common;

use dir_test::{Fixture, dir_test};
use sonatina_codegen::{
    analysis::func_behavior,
    cfg_edit::CleanupMode,
    domtree::DomTree,
    loop_analysis::LoopTree,
    optim::{
        adce::AdceSolver, cfg_cleanup::CfgCleanup, egraph::run_egraph_pass, licm::LicmSolver,
        sccp::SccpSolver,
    },
};
use sonatina_ir::{
    ControlFlowGraph, Function,
    ir_writer::{FuncWriter, ModuleWriter},
    module::FuncRef,
};

const MAX_POLISH_ITERS: usize = 2;

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/opt_pipeline/",
    glob: "*.sntn"
)]
fn test_opt_pipeline(fixture: Fixture<&str>) {
    let parsed = common::parse_module(fixture.path());
    func_behavior::analyze_module(&parsed.module);

    for func_ref in parsed.debug.func_order.clone() {
        parsed.module.func_store.modify(func_ref, |func| {
            run_baseline_pipeline(func);
            run_polish_pipeline(func, func_ref);
        });
    }

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
