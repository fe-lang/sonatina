//! Optimization pipeline for composing and running optimization passes.
//!
//! Provides [`Pipeline`] for running a sequence of passes on functions or
//! modules, with both a conservative default preset and custom composition.

use sonatina_ir::{ControlFlowGraph, Function, module::Module};

use crate::{cfg_edit::CleanupMode, domtree::DomTree, loop_analysis::LoopTree};

use super::{
    adce::AdceSolver, cfg_cleanup::CfgCleanup, egraph::run_egraph_pass, licm::LicmSolver,
    sccp::SccpSolver,
};

/// An individual optimization pass.
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
}

/// An ordered sequence of optimization passes.
///
/// Use [`Pipeline::default_pipeline`] for a conservative preset, or build a
/// custom sequence with [`Pipeline::new`] and [`Pipeline::add_pass`].
///
/// # Analysis lifecycle
///
/// Each pass that requires analyses (CFG, dominator tree, loop tree) recomputes
/// them from the current IR state. The [`PassContext`] reuses allocated storage
/// across passes to avoid repeated allocation, but the data is always fresh.
pub struct Pipeline {
    passes: Vec<Pass>,
}

impl Pipeline {
    /// Create an empty pipeline.
    pub fn new() -> Self {
        Self { passes: Vec::new() }
    }

    /// Default optimization pipeline with a conservative pass ordering.
    ///
    /// Current sequence:
    /// 1. `CfgCleanup` — normalize CFG before analysis-heavy passes
    /// 2. `Sccp` — constant propagation + dead code elimination (composite)
    /// 3. `Licm` — loop invariant code motion
    /// 4. `CfgCleanup` — clean up after LICM structural changes
    /// 5. `Egraph` — algebraic simplification, memory forwarding
    ///
    /// A second SCCP round after Egraph is intentionally omitted: the egraph
    /// pass currently uses raw layout removal which can leave stale `dfg.users`
    /// entries, and SCCP assumes user instructions are layout-inserted.
    pub fn default_pipeline() -> Self {
        let mut p = Self::new();
        p.add_pass(Pass::CfgCleanup);
        p.add_pass(Pass::Sccp);
        p.add_pass(Pass::Licm);
        p.add_pass(Pass::CfgCleanup);
        p.add_pass(Pass::Egraph);
        p
    }

    /// Append a pass to the pipeline. Returns `&mut Self` for chaining.
    pub fn add_pass(&mut self, pass: Pass) -> &mut Self {
        self.passes.push(pass);
        self
    }

    /// Run the pipeline on a single function.
    ///
    /// Allocates a fresh analysis context internally; all analyses are
    /// recomputed before each pass that requires them.
    pub fn run_on_function(&self, func: &mut Function) {
        let mut ctx = PassContext::default();
        for &pass in &self.passes {
            run_pass(pass, func, &mut ctx);
        }
    }

    /// Run the pipeline on all functions in a module.
    ///
    /// Functions are optimized independently and in parallel (via rayon through
    /// `FuncStore::par_for_each`). Each thread allocates its own analysis context.
    ///
    /// Note: this mutates functions through `FuncStore`'s interior mutability
    /// (`DashMap`-backed). Iteration order across functions is non-deterministic.
    pub fn run_on_module(&self, module: &Module) {
        module.func_store.par_for_each(|_func_ref, func| {
            self.run_on_function(func);
        });
    }
}

impl Default for Pipeline {
    /// Returns [`Pipeline::default_pipeline`], not an empty pipeline.
    fn default() -> Self {
        Self::default_pipeline()
    }
}

/// Reusable analysis allocations for a single pipeline run on one function.
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
        let module = build_test_module();
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            pipeline.run_on_function(func);
        });
    }

    #[test]
    fn custom_pipeline_runs() {
        let mut pipeline = Pipeline::new();
        pipeline
            .add_pass(Pass::CfgCleanup)
            .add_pass(Pass::Adce)
            .add_pass(Pass::CfgCleanup);

        let module = build_test_module();
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            pipeline.run_on_function(func);
        });
    }

    #[test]
    fn empty_pipeline_is_identity() {
        let pipeline = Pipeline::new();
        let module = build_test_module();
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            pipeline.run_on_function(func);
        });
    }

    #[test]
    fn module_level_pipeline_runs() {
        let pipeline = Pipeline::default_pipeline();
        let module = build_test_module();
        pipeline.run_on_module(&module);
    }
}
