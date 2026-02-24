//! Optimization pipeline for composing and running optimization passes.
//!
//! The pipeline sequences two kinds of work:
//!
//! - **Module-level passes** like inlining that need cross-function access
//! - **Per-function passes** (SCCP, LICM, etc.) that run independently and
//!   in parallel across all functions
//!
//! [`Step`] represents one unit of work in the pipeline. [`Pipeline`] holds
//! an ordered sequence of steps and executes them against a module.

use sonatina_ir::{ControlFlowGraph, Function, module::Module};

use crate::{
    analysis::func_behavior, cfg_edit::CleanupMode, domtree::DomTree, loop_analysis::LoopTree,
};

use super::{
    adce::AdceSolver,
    cfg_cleanup::CfgCleanup,
    dead_func::{DeadFuncElimConfig, collect_object_roots, run_dead_func_elim},
    egraph::run_egraph_pass,
    gvn::GvnSolver,
    inliner::{Inliner, InlinerConfig},
    licm::LicmSolver,
    sccp::SccpSolver,
};

/// A per-function optimization pass.
///
/// [`Pass::Sccp`] is a composite pass that internally runs CfgCleanup, SCCP
/// solving, CfgCleanup, and ADCE. Use [`Pass::Adce`] only in custom pipelines
/// where standalone dead code elimination is needed without constant propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Pass {
    /// Control flow graph cleanup (dead block removal, phi pruning, terminator repair).
    CfgCleanup,
    /// Sparse conditional constant propagation (composite: CfgCleanup + SCCP + CfgCleanup + ADCE).
    Sccp,
    /// Standalone aggressive dead code elimination.
    Adce,
    /// Loop invariant code motion.
    Licm,
    /// E-graph based algebraic simplification and memory forwarding.
    Egraph,
    /// Complete Global Value Numbering (legacy sparse predicated solver).
    Gvn,
    /// Recompute `dfg.users` from layout-inserted instructions only.
    ///
    /// Use after passes (like Egraph) that can leave stale user entries
    /// due to `change_to_alias` + layout removal interactions.
    RebuildUsers,
}

/// A step in the module-level optimization pipeline.
///
/// Steps execute sequentially. [`Step::Inline`] operates on the whole module;
/// [`Step::FuncPasses`] runs per-function passes in parallel across all
/// functions; [`Step::DeadFuncElim`] prunes unreachable function definitions.
#[derive(Debug, Clone)]
pub enum Step {
    /// Run the inliner across the whole module (cross-function).
    Inline,
    /// Run per-function optimization passes in parallel across all functions.
    FuncPasses(Vec<Pass>),
    /// Remove unreachable function definitions rooted at object `entry`/`include` directives.
    DeadFuncElim,
}

/// An ordered sequence of optimization steps.
///
/// Use [`Pipeline::default_pipeline`] for a conservative preset, or build a
/// custom sequence with [`Pipeline::new`] and [`Pipeline::add_step`].
///
/// # Analysis lifecycle
///
/// Each per-function pass that requires analyses (CFG, dominator tree, loop
/// tree) recomputes them from the current IR state. Allocated storage is
/// reused within a function's pass sequence to avoid repeated allocation,
/// but the data is always fresh.
pub struct Pipeline {
    steps: Vec<Step>,
    /// Configuration for all [`Step::Inline`] steps in this pipeline.
    pub inliner_config: InlinerConfig,
}

fn pass_needs_func_behavior(pass: Pass) -> bool {
    matches!(
        pass,
        Pass::CfgCleanup | Pass::Sccp | Pass::Adce | Pass::Egraph | Pass::Gvn
    )
}

fn step_needs_func_behavior(passes: &[Pass]) -> bool {
    passes.iter().copied().any(pass_needs_func_behavior)
}

fn pass_may_invalidate_func_behavior(pass: Pass) -> bool {
    matches!(
        pass,
        Pass::CfgCleanup | Pass::Sccp | Pass::Adce | Pass::Licm | Pass::Egraph | Pass::Gvn
    )
}

fn step_may_invalidate_func_behavior(passes: &[Pass]) -> bool {
    passes
        .iter()
        .copied()
        .any(pass_may_invalidate_func_behavior)
}

impl Pipeline {
    /// Create an empty pipeline with default inliner configuration.
    pub fn new() -> Self {
        Self {
            steps: Vec::new(),
            inliner_config: InlinerConfig::default(),
        }
    }

    /// No optimization pipeline.
    ///
    /// This is equivalent to [`Pipeline::new`].
    pub fn none() -> Self {
        Self::new()
    }

    /// Conservative optimization pipeline preset.
    ///
    /// This is the recommended baseline (O1-style) pipeline.
    pub fn balanced() -> Self {
        let mut p = Self::new();
        p.add_step(Step::Inline);
        p.add_step(Step::FuncPasses(vec![
            Pass::CfgCleanup,
            Pass::Sccp,
            Pass::Gvn,
            Pass::Licm,
            Pass::CfgCleanup,
            Pass::Egraph,
            Pass::RebuildUsers,
            Pass::Sccp,
            Pass::CfgCleanup,
        ]));
        p.add_step(Step::DeadFuncElim);
        p
    }

    /// Aggressive optimization pipeline preset.
    ///
    /// Uses a larger inliner budget and a second inline+SCCP round.
    pub fn aggressive() -> Self {
        let mut p = Self::new();
        p.add_step(Step::Inline);
        p.add_step(Step::FuncPasses(vec![
            Pass::CfgCleanup,
            Pass::Sccp,
            Pass::Gvn,
            Pass::Licm,
            Pass::CfgCleanup,
            Pass::Egraph,
            Pass::RebuildUsers,
            Pass::Sccp,
            Pass::CfgCleanup,
        ]));
        p.add_step(Step::Inline);
        p.add_step(Step::FuncPasses(vec![
            Pass::CfgCleanup,
            Pass::Sccp,
            Pass::Gvn,
            Pass::CfgCleanup,
        ]));
        p.add_step(Step::DeadFuncElim);
        p
    }

    /// Default optimization pipeline with a conservative ordering.
    ///
    /// Current sequence:
    /// 1. `Inline` — single-block inlining (module-level)
    /// 2. Per-function passes (parallel):
    ///    - `CfgCleanup` — normalize CFG before analysis-heavy passes
    ///    - `Sccp` — constant propagation + dead code elimination (composite)
    ///    - `Gvn` — sparse predicated global value numbering with value-phi resolution
    ///    - `Licm` — loop invariant code motion
    ///    - `CfgCleanup` — clean up after LICM structural changes
    ///    - `Egraph` — algebraic simplification, memory forwarding
    ///    - `RebuildUsers` — fix stale `dfg.users` after egraph
    ///    - `Sccp` — second round catches constants exposed by egraph
    ///    - `CfgCleanup` — final cleanup
    /// 3. `DeadFuncElim` — prune unreachable private definitions from object roots
    pub fn default_pipeline() -> Self {
        Self::balanced()
    }

    /// Append a step to the pipeline. Returns `&mut Self` for chaining.
    pub fn add_step(&mut self, step: Step) -> &mut Self {
        self.steps.push(step);
        self
    }

    /// Run the full pipeline on a module.
    ///
    /// Steps execute sequentially. [`Step::Inline`] mutates the module
    /// directly; [`Step::FuncPasses`] parallelizes across functions via
    /// `FuncStore::par_for_each`.
    ///
    /// Function behavior analysis runs lazily before each pass round that
    /// needs call attributes, and is marked dirty again after mutating rounds.
    /// This keeps attrs fresh without recomputing before every step.
    ///
    /// The invalidation boundary is per [`Step::FuncPasses`], because function
    /// rounds execute function-major in parallel.
    pub fn run(&self, module: &mut Module) {
        let mut func_behavior_dirty = true;

        for step in &self.steps {
            match step {
                Step::Inline => {
                    let mut inliner = Inliner::new(self.inliner_config);
                    inliner.run(module);
                    func_behavior_dirty = true;
                }
                Step::FuncPasses(passes) => {
                    if func_behavior_dirty && step_needs_func_behavior(passes) {
                        func_behavior::analyze_module(module);
                        func_behavior_dirty = false;
                    }
                    module.func_store.par_for_each(|_func_ref, func| {
                        run_func_passes(passes, func);
                    });
                    if step_may_invalidate_func_behavior(passes) {
                        func_behavior_dirty = true;
                    }
                }
                Step::DeadFuncElim => {
                    let roots = collect_object_roots(module);
                    run_dead_func_elim(module, &roots, DeadFuncElimConfig::default());
                    func_behavior_dirty = true;
                }
            }
        }
    }
}

impl Default for Pipeline {
    /// Returns [`Pipeline::default_pipeline`], not an empty pipeline.
    fn default() -> Self {
        Self::balanced()
    }
}

/// Run a sequence of per-function passes on a single function.
///
/// This is the building block for [`Step::FuncPasses`] and is also useful
/// for testing individual pass sequences without a full module.
///
/// This helper cannot run module-level analyses. Callers that include
/// attribute-dependent passes must ensure function attrs are computed first.
pub fn run_func_passes(passes: &[Pass], func: &mut Function) {
    let mut ctx = PassContext::default();
    for &pass in passes {
        run_pass(pass, func, &mut ctx);
    }
}

/// Reusable analysis allocations for a single pass sequence on one function.
///
/// Analyses are recomputed fresh before each pass that needs them;
/// the allocated storage is reused across passes to avoid repeated heap
/// allocation.
#[derive(Default)]
struct PassContext {
    cfg: ControlFlowGraph,
    domtree: DomTree,
    lpt: LoopTree,
}

/// Dispatch a single pass, recomputing any required analyses from the
/// current function state.
fn run_pass(pass: Pass, func: &mut Function, ctx: &mut PassContext) {
    match pass {
        Pass::CfgCleanup => {
            CfgCleanup::new(CleanupMode::Strict).run(func);
        }
        Pass::Sccp => {
            // SccpSolver::run is composite: internally does
            //   CfgCleanup → SCCP solving → CfgCleanup → ADCE.
            ctx.cfg.compute(func);
            let mut solver = SccpSolver::new();
            solver.run(func, &mut ctx.cfg);
            CfgCleanup::new(CleanupMode::Strict).run(func);
        }
        Pass::Adce => {
            AdceSolver::new().run(func);
        }
        Pass::Licm => {
            ctx.cfg.compute(func);
            ctx.domtree.compute(&ctx.cfg);
            ctx.lpt.compute(&ctx.cfg, &ctx.domtree);
            let mut solver = LicmSolver::new();
            solver.run(func, &mut ctx.cfg, &mut ctx.lpt);
            CfgCleanup::new(CleanupMode::Strict).run(func);
        }
        Pass::Egraph => {
            run_egraph_pass(func);
        }
        Pass::Gvn => {
            ctx.cfg.compute(func);
            ctx.domtree.compute(&ctx.cfg);
            let mut solver = GvnSolver::new();
            solver.run(func, &mut ctx.cfg, &mut ctx.domtree);
        }
        Pass::RebuildUsers => {
            func.rebuild_users();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        Type,
        builder::test_util::*,
        inst::{arith::Add, control_flow::Return},
        ir_writer::FuncWriter,
        prelude::*,
    };
    use sonatina_parser::parse_module;

    /// Build a module with a single function: `fn test(i32) -> i32 { arg0 + 1 }`.
    fn build_test_module() -> sonatina_ir::module::Module {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I32], Type::I32);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        builder.switch_to_block(b0);

        let arg = builder.args()[0];
        let c1 = builder.make_imm_value(1i32);
        let sum = builder.insert_inst_with(|| Add::new(is, arg, c1), Type::I32);
        builder.insert_inst_no_result_with(|| Return::new(is, Some(sum)));
        builder.seal_all();
        builder.finish();

        mb.build()
    }

    #[test]
    fn default_pipeline_runs() {
        let pipeline = Pipeline::default_pipeline();
        let mut module = build_test_module();
        pipeline.run(&mut module);
    }

    #[test]
    fn custom_pipeline_runs() {
        let mut pipeline = Pipeline::new();
        pipeline.add_step(Step::FuncPasses(vec![
            Pass::CfgCleanup,
            Pass::Adce,
            Pass::CfgCleanup,
        ]));

        let mut module = build_test_module();
        pipeline.run(&mut module);
    }

    #[test]
    fn inline_then_optimize() {
        let mut pipeline = Pipeline::new();
        pipeline
            .add_step(Step::Inline)
            .add_step(Step::FuncPasses(vec![Pass::CfgCleanup, Pass::Sccp]));

        let mut module = build_test_module();
        pipeline.run(&mut module);
    }

    #[test]
    fn empty_pipeline_is_identity() {
        let pipeline = Pipeline::new();
        let mut module = build_test_module();
        pipeline.run(&mut module);
    }

    #[test]
    fn func_passes_standalone() {
        let module = build_test_module();
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            run_func_passes(&[Pass::CfgCleanup, Pass::Sccp, Pass::Egraph], func);
        });
    }

    #[test]
    fn default_pipeline_prunes_unreachable_private_functions() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() {
    block0:
        return;
}

func private %dead() {
    block0:
        return;
}

object @O {
    section runtime {
        entry %entry;
    }
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        Pipeline::default_pipeline().run(&mut module);

        let mut names = module
            .funcs()
            .into_iter()
            .map(|func_ref| module.ctx.func_sig(func_ref, |sig| sig.name().to_string()))
            .collect::<Vec<_>>();
        names.sort();
        assert_eq!(names, vec!["entry".to_string()]);
    }

    #[test]
    fn gvn_keeps_duplicate_branch_dest_reachable() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i256 {
    block0:
        v0.i1 = eq 0.i256 0.i256;
        br v0 block1 block1;

    block1:
        return 1.i256;
}
"#;

        let module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            run_func_passes(
                &[Pass::CfgCleanup, Pass::Sccp, Pass::Gvn, Pass::CfgCleanup],
                func,
            );
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return 1.i256;"),
                "expected return to survive duplicate-branch GVN:\n{dumped}"
            );
            assert!(
                !dumped.contains("unreachable;"),
                "duplicate branch destination collapsed to unreachable:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_preserves_reachable_br_table_entry_with_duplicate_dest() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i32 {
    block0:
        br_table 0.i8 block3 (0.i8 block1) (1.i8 block2) (2.i8 block1);

    block1:
        return 11.i32;

    block2:
        return 22.i32;

    block3:
        return 33.i32;
}
"#;

        let module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            run_func_passes(&[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup], func);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return 11.i32;"),
                "expected reachable br_table arm to survive duplicate-dest pruning:\n{dumped}"
            );
            assert!(
                !dumped.contains("return 33.i32;"),
                "default arm should be removed for constant scrutinee:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_preserves_phi_arg_when_duplicate_pred_edge_remains_reachable() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i32 {
    block0:
        br_table 0.i8 block2 (0.i8 block1) (1.i8 block1);

    block1:
        v0.i32 = phi (7.i32 block0);
        return v0;

    block2:
        return 9.i32;
}
"#;

        let module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            run_func_passes(&[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup], func);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return 7.i32;"),
                "phi argument from block0 should remain when one duplicate edge is reachable:\n{dumped}"
            );
            assert!(
                !dumped.contains("return 9.i32;"),
                "unreachable default arm should be removed for constant scrutinee:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_does_not_fold_self_cmp_when_value_may_be_undef() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i256 {
    block0:
        v1.i256 = add undef.i256 1.i256;
        v2.i1 = eq v1 v1;
        br v2 block1 block2;

    block1:
        return 1.i256;

    block2:
        return 2.i256;
}
"#;

        let module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            run_func_passes(&[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup], func);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return 1.i256;"),
                "then branch should remain reachable:\n{dumped}"
            );
            assert!(
                dumped.contains("return 2.i256;"),
                "else branch should remain reachable when eq compares maybe-undef value:\n{dumped}"
            );
        });
    }
}
