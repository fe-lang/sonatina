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
        inliner::{Inliner, InlinerConfig},
        licm::LicmSolver,
        sccp::SccpSolver,
    },
};
use sonatina_ir::{
    ControlFlowGraph, Function, InstDowncast, Module,
    inst::data::{GetFunctionPtr, SymAddr, SymSize, SymbolRef},
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
