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

use crate::{cfg_edit::CleanupMode, domtree::DomTree, loop_analysis::LoopTree};

use super::{
    adce::AdceSolver,
    cfg_cleanup::CfgCleanup,
    egraph::run_egraph_pass,
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
/// functions.
#[derive(Debug, Clone)]
pub enum Step {
    /// Run the inliner across the whole module (cross-function).
    Inline,
    /// Run per-function optimization passes in parallel across all functions.
    FuncPasses(Vec<Pass>),
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

impl Pipeline {
    /// Create an empty pipeline with default inliner configuration.
    pub fn new() -> Self {
        Self {
            steps: Vec::new(),
            inliner_config: InlinerConfig::default(),
        }
    }

    /// Default optimization pipeline with a conservative ordering.
    ///
    /// Current sequence:
    /// 1. `Inline` — single-block inlining (module-level)
    /// 2. Per-function passes (parallel):
    ///    - `CfgCleanup` — normalize CFG before analysis-heavy passes
    ///    - `Sccp` — constant propagation + dead code elimination (composite)
    ///    - `Licm` — loop invariant code motion
    ///    - `CfgCleanup` — clean up after LICM structural changes
    ///    - `Egraph` — algebraic simplification, memory forwarding
    ///    - `RebuildUsers` — fix stale `dfg.users` after egraph
    ///    - `Sccp` — second round catches constants exposed by egraph
    ///    - `CfgCleanup` — final cleanup
    pub fn default_pipeline() -> Self {
        let mut p = Self::new();
        p.add_step(Step::Inline);
        p.add_step(Step::FuncPasses(vec![
            Pass::CfgCleanup,
            Pass::Sccp,
            Pass::Licm,
            Pass::CfgCleanup,
            Pass::Egraph,
            Pass::RebuildUsers,
            Pass::Sccp,
            Pass::CfgCleanup,
        ]));
        p
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
    pub fn run(&self, module: &mut Module) {
        for step in &self.steps {
            match step {
                Step::Inline => {
                    let mut inliner = Inliner::new(self.inliner_config);
                    inliner.run(module);
                }
                Step::FuncPasses(passes) => {
                    module.func_store.par_for_each(|_func_ref, func| {
                        run_func_passes(passes, func);
                    });
                }
            }
        }
    }
}

impl Default for Pipeline {
    /// Returns [`Pipeline::default_pipeline`], not an empty pipeline.
    fn default() -> Self {
        Self::default_pipeline()
    }
}

/// Run a sequence of per-function passes on a single function.
///
/// This is the building block for [`Step::FuncPasses`] and is also useful
/// for testing individual pass sequences without a full module.
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
        prelude::*,
    };

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
        pipeline
            .add_step(Step::FuncPasses(vec![
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
            .add_step(Step::FuncPasses(vec![
                Pass::CfgCleanup,
                Pass::Sccp,
            ]));

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
            run_func_passes(
                &[Pass::CfgCleanup, Pass::Sccp, Pass::Egraph],
                func,
            );
        });
    }
}
