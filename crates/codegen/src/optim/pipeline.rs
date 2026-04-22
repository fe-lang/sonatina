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

use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use sonatina_ir::{
    ControlFlowGraph, Function,
    module::{FuncRef, Module},
};
use tracing::{debug_span, info_span, trace_span};

use crate::{
    analysis::func_behavior, cfg_edit::CleanupMode, domtree::DomTree, loop_analysis::LoopTree,
};

use super::{
    adce::AdceSolver,
    aggregate::{
        AggregateCombine, AggregateScalarize, LocalObjectArgMap, ObjectEffectSummaryMap,
        ObjectLoadStore, ObjectMemoryAnalysis, collect_local_object_arg_info,
        collect_local_object_arg_info_with_effects, compute_object_effect_summaries,
    },
    branch_canonicalize::BranchCanonicalize,
    cfg_cleanup::CfgCleanup,
    checked_arith_elim::{CheckedArithElim, has_supported_checked_arith},
    dead_arg::{DeadArgElimConfig, run_dead_arg_elim},
    dead_func::{DeadFuncElimConfig, collect_object_roots, run_dead_func_elim},
    gvn::GvnSolver,
    inliner::{Inliner, InlinerConfig},
    known_bits_simplify::KnownBitsSimplify,
    licm::LicmSolver,
    load_store::LoadStoreSolver,
    loop_strength_reduce::LoopStrengthReduce,
    multi_result_legalize::legalize_multi_result,
    scalar_canonicalize::ScalarCanonicalize,
    sccp::SccpSolver,
};

/// A per-function optimization pass.
///
/// [`Pass::Sccp`] is a composite pass that internally runs CfgCleanup, SCCP
/// solving, CfgCleanup, and ADCE. Use [`Pass::Adce`] only in custom pipelines
/// where standalone dead code elimination is needed without constant propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Pass {
    LegalizeMultiResult,
    /// Control flow graph cleanup (dead block removal, phi pruning, terminator repair).
    CfgCleanup,
    /// Local aggregate InstCombine rewrites.
    AggregateCombine,
    /// Canonicalize boolean branch conditions and invert expensive compares.
    BranchCanonicalize,
    /// Object-space load/store forwarding and dead-store elimination for fresh semantic objects.
    ObjectLoadStore,
    /// Aggregate scalarization (SROA + closed SSA-web scalarization).
    AggregateScalarize,
    /// Per-space load/store forwarding and dead-store elimination.
    LoadStore,
    /// Cheap local scalar canonicalization (zero-compares, neg-arith, pow2 mul, cast chains).
    ScalarCanonicalize,
    /// Simplify expressions with precise known-bit reasoning.
    KnownBitsSimplify,
    /// Eliminate checked arithmetic and div/mod overflow flags proven unreachable by range analysis.
    CheckedArithElim,
    /// Sparse conditional constant propagation (composite: CfgCleanup + SCCP + CfgCleanup + ADCE).
    Sccp,
    /// Standalone aggressive dead code elimination.
    Adce,
    /// Loop invariant code motion.
    Licm,
    /// Loop strength reduction for affine memory addresses.
    LoopStrengthReduce,
    /// Complete Global Value Numbering (legacy sparse predicated solver).
    Gvn,
    /// Recompute `dfg.users` from layout-inserted instructions only.
    ///
    /// Use after passes that can leave stale user entries
    /// due to `change_to_alias` + layout removal interactions.
    RebuildUsers,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PassInfo {
    name: &'static str,
    needs_func_behavior: bool,
    invalidates_func_behavior: bool,
}

impl Pass {
    const fn info(self) -> PassInfo {
        match self {
            Pass::LegalizeMultiResult => PassInfo {
                name: "legalize_multi_result",
                needs_func_behavior: false,
                invalidates_func_behavior: false,
            },
            Pass::CfgCleanup => PassInfo {
                name: "cfg_cleanup",
                needs_func_behavior: true,
                invalidates_func_behavior: true,
            },
            Pass::AggregateCombine => PassInfo {
                name: "aggregate_combine",
                needs_func_behavior: false,
                invalidates_func_behavior: true,
            },
            Pass::BranchCanonicalize => PassInfo {
                name: "branch_canonicalize",
                needs_func_behavior: false,
                invalidates_func_behavior: true,
            },
            Pass::ObjectLoadStore => PassInfo {
                name: "object_load_store",
                needs_func_behavior: false,
                invalidates_func_behavior: true,
            },
            Pass::AggregateScalarize => PassInfo {
                name: "aggregate_scalarize",
                needs_func_behavior: false,
                invalidates_func_behavior: true,
            },
            Pass::LoadStore => PassInfo {
                name: "load_store",
                needs_func_behavior: true,
                invalidates_func_behavior: true,
            },
            Pass::ScalarCanonicalize => PassInfo {
                name: "scalar_canonicalize",
                needs_func_behavior: false,
                invalidates_func_behavior: true,
            },
            Pass::KnownBitsSimplify => PassInfo {
                name: "known_bits_simplify",
                needs_func_behavior: false,
                invalidates_func_behavior: true,
            },
            Pass::CheckedArithElim => PassInfo {
                name: "checked_arith_elim",
                needs_func_behavior: false,
                invalidates_func_behavior: true,
            },
            Pass::Sccp => PassInfo {
                name: "sccp",
                needs_func_behavior: true,
                invalidates_func_behavior: true,
            },
            Pass::Adce => PassInfo {
                name: "adce",
                needs_func_behavior: true,
                invalidates_func_behavior: true,
            },
            Pass::Licm => PassInfo {
                name: "licm",
                needs_func_behavior: true,
                invalidates_func_behavior: true,
            },
            Pass::LoopStrengthReduce => PassInfo {
                name: "loop_strength_reduce",
                needs_func_behavior: false,
                invalidates_func_behavior: true,
            },
            Pass::Gvn => PassInfo {
                name: "gvn",
                needs_func_behavior: true,
                invalidates_func_behavior: true,
            },
            Pass::RebuildUsers => PassInfo {
                name: "rebuild_users",
                needs_func_behavior: false,
                invalidates_func_behavior: false,
            },
        }
    }

    pub const fn as_str(self) -> &'static str {
        self.info().name
    }

    const fn needs_func_behavior(self) -> bool {
        self.info().needs_func_behavior
    }

    const fn invalidates_func_behavior(self) -> bool {
        self.info().invalidates_func_behavior
    }
}

/// A step in the module-level optimization pipeline.
///
/// Steps execute sequentially. [`Step::Inline`] operates on the whole module;
/// [`Step::FuncPasses`] runs per-function passes in parallel across all
/// functions; [`Step::DeadArgElim`] rewrites dead private formals; [`Step::DeadFuncElim`]
/// prunes unreachable function definitions.
#[derive(Debug, Clone)]
pub enum Step {
    /// Run the inliner across the whole module (cross-function).
    Inline,
    /// Run per-function optimization passes in parallel across all functions.
    FuncPasses(Vec<Pass>),
    /// Remove dead formal arguments from rewritable functions and update direct callsites.
    DeadArgElim,
    /// Remove unreachable function definitions rooted at object `entry`/`include` directives.
    DeadFuncElim,
}

impl Step {
    pub const fn as_str(&self) -> &'static str {
        match self {
            Step::Inline => "inline",
            Step::FuncPasses(_) => "func_passes",
            Step::DeadArgElim => "dead_arg_elim",
            Step::DeadFuncElim => "dead_func_elim",
        }
    }
}

/// An ordered sequence of optimization steps.
///
/// Use [`Pipeline::default_pipeline`] for the default speed-oriented preset, or build a
/// custom sequence with [`Pipeline::new`] and [`Pipeline::add_step`].
///
/// # Analysis lifecycle
///
/// Each per-function pass that requires analyses (CFG, dominator tree, loop
/// tree) recomputes them from the current IR state. Module pipelines execute
/// pass-major function rounds so cross-function behavior summaries stay fresh
/// between passes.
pub struct Pipeline {
    steps: Vec<Step>,
    /// Configuration for all [`Step::Inline`] steps in this pipeline.
    pub inliner_config: InlinerConfig,
}

const PRIMARY_FUNC_PASSES: &[Pass] = &[
    Pass::CfgCleanup,
    Pass::AggregateCombine,
    Pass::BranchCanonicalize,
    Pass::ObjectLoadStore,
    Pass::AggregateScalarize,
    Pass::LoadStore,
    Pass::CheckedArithElim,
    Pass::Sccp,
    Pass::ScalarCanonicalize,
    Pass::Gvn,
    Pass::Licm,
    Pass::CfgCleanup,
    Pass::ScalarCanonicalize,
    Pass::Gvn,
    Pass::KnownBitsSimplify,
    Pass::Sccp,
    Pass::BranchCanonicalize,
    Pass::CfgCleanup,
];

const SECONDARY_FUNC_PASSES: &[Pass] = &[
    Pass::CfgCleanup,
    Pass::AggregateCombine,
    Pass::BranchCanonicalize,
    Pass::ObjectLoadStore,
    Pass::AggregateScalarize,
    Pass::LoadStore,
    Pass::CheckedArithElim,
    Pass::Sccp,
    Pass::ScalarCanonicalize,
    Pass::Gvn,
    Pass::BranchCanonicalize,
    Pass::CfgCleanup,
];

const POST_DEAD_ARG_CLEANUP_PASSES: &[Pass] = &[
    Pass::CfgCleanup,
    Pass::Sccp,
    Pass::BranchCanonicalize,
    Pass::CfgCleanup,
];

fn size_inliner_config() -> InlinerConfig {
    InlinerConfig {
        // The size-oriented mode still runs the full optimization schedule, but
        // uses a wider full-inlining budget because that tends to reduce overall
        // bytecode once later cleanup and dead-function elimination run.
        enable_full_inliner: true,
        splice_max_insts: 6,
        max_inlinee_blocks: 8,
        max_inlinee_insts: 48,
        max_growth_per_caller: 32,
        max_total_growth: 160,
        max_inline_depth: 3,
        inline_threshold: 10,
        inline_threshold_cold: 5,
        single_use_bonus: 8,
        leaf_bonus: 2,
        call_overhead_bonus: 6,
        duplicated_block_penalty: 1,
        multi_use_inst_free_allowance: 5,
        multi_use_excess_inst_penalty: 1,
        loop_penalty: 32,
        object_scalarization_bonus_cap: 8,
        object_helper_cluster_bonus: 3,
        ..InlinerConfig::default()
    }
}

fn speed_inliner_config() -> InlinerConfig {
    InlinerConfig {
        // The speed-oriented mode stays more selective about inlining, because
        // on the EVM a smaller post-inline body often wins on runtime gas.
        enable_full_inliner: true,
        splice_max_insts: 4,
        max_inlinee_blocks: 8,
        max_inlinee_insts: 32,
        max_growth_per_caller: 24,
        max_total_growth: 128,
        max_inline_depth: 3,
        inline_threshold: 8,
        inline_threshold_cold: 4,
        single_use_bonus: 8,
        leaf_bonus: 2,
        call_overhead_bonus: 6,
        duplicated_block_penalty: 1,
        multi_use_inst_free_allowance: 5,
        multi_use_excess_inst_penalty: 1,
        loop_penalty: 32,
        object_scalarization_bonus_cap: 10,
        object_helper_cluster_bonus: 4,
        ..InlinerConfig::default()
    }
}

impl Pipeline {
    fn optimized_with_inliner_config(inliner_config: InlinerConfig) -> Self {
        let mut p = Self::new();
        p.inliner_config = inliner_config;
        p.add_step(Step::Inline);
        p.add_step(Step::FuncPasses(PRIMARY_FUNC_PASSES.to_vec()));
        p.add_step(Step::Inline);
        p.add_step(Step::FuncPasses(SECONDARY_FUNC_PASSES.to_vec()));
        p.add_step(Step::DeadArgElim);
        p.add_step(Step::FuncPasses(POST_DEAD_ARG_CLEANUP_PASSES.to_vec()));
        p.add_step(Step::DeadFuncElim);
        p.add_step(Step::Inline);
        p.add_step(Step::FuncPasses(SECONDARY_FUNC_PASSES.to_vec()));
        p.add_step(Step::DeadFuncElim);
        p
    }

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

    /// Size-oriented optimization pipeline preset.
    ///
    /// It uses the same aggressive pass schedule as [`Pipeline::speed`], but
    /// keeps inlining biased toward avoiding code size growth.
    pub fn size() -> Self {
        Self::optimized_with_inliner_config(size_inliner_config())
    }

    /// Speed-oriented optimization pipeline preset.
    ///
    /// Uses the same pass schedule as [`Pipeline::size`], but widens the
    /// inliner budget for runtime speed.
    pub fn speed() -> Self {
        Self::optimized_with_inliner_config(speed_inliner_config())
    }

    /// Default optimization pipeline with a speed-oriented ordering.
    ///
    /// Current sequence:
    /// 1. `Inline` — module-level inlining (trivial + constrained full inliner)
    /// 2. Per-function passes (parallel):
    ///    - `CfgCleanup`
    ///    - `AggregateCombine`
    ///    - `BranchCanonicalize`
    ///    - `ObjectLoadStore`
    ///    - `AggregateScalarize`
    ///    - `LoadStore`
    ///    - `CheckedArithElim`
    ///    - `Sccp` — constant propagation + dead code elimination (composite)
    ///    - `ScalarCanonicalize` — local canonical forms for scalar SSA instructions
    ///    - `Gvn` — sparse predicated global value numbering with value-phi resolution
    ///    - `Licm` — loop invariant code motion
    ///    - `CfgCleanup` — clean up after LICM structural changes
    ///    - `ScalarCanonicalize` — canonicalize new local forms exposed by LICM cleanup
    ///    - `Gvn` — second value-numbering round for LICM-exposed redundancy
    ///    - `KnownBitsSimplify` — fact-driven local simplification
    ///    - `Sccp` — second round catches constants exposed by the new local rewrites
    ///    - `BranchCanonicalize`
    ///    - `CfgCleanup` — final cleanup
    /// 3. `Inline` — repeat inlining with freshly simplified callees/callers
    /// 4. Per-function passes (parallel):
    ///    - `CfgCleanup`
    ///    - `AggregateCombine`
    ///    - `BranchCanonicalize`
    ///    - `AggregateScalarize`
    ///    - `LoadStore`
    ///    - `CheckedArithElim`
    ///    - `Sccp`
    ///    - `ScalarCanonicalize`
    ///    - `Gvn`
    ///    - `BranchCanonicalize`
    ///    - `CfgCleanup`
    /// 5. `DeadArgElim` — remove dead private formals and rewrite direct calls
    /// 6. Per-function cleanup:
    ///    - `CfgCleanup`
    ///    - `Sccp`
    ///    - `CfgCleanup`
    /// 7. `DeadFuncElim` — prune unreachable private definitions from object roots
    pub fn default_pipeline() -> Self {
        Self::speed()
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
    /// Function behavior analysis runs lazily before `Inline` and before each
    /// pass round in [`Step::FuncPasses`] that needs call attributes. Mutating
    /// rounds mark summaries dirty again, while no-op inline rounds keep the
    /// already-analyzed summaries live for later passes.
    pub fn run(&self, module: &mut Module) {
        let _run_span = info_span!(
            "sonatina.optim.pipeline.run",
            steps_len = self.steps.len(),
            func_count = module.funcs().len()
        )
        .entered();
        let mut func_behavior_dirty = true;

        for (step_index, step) in self.steps.iter().enumerate() {
            let _step_span = debug_span!(
                "sonatina.optim.pipeline.step",
                step_index,
                step = step.as_str()
            )
            .entered();
            match step {
                Step::Inline => {
                    if func_behavior_dirty {
                        let _span =
                            trace_span!("sonatina.optim.pipeline.func_behavior_analyze").entered();
                        func_behavior::analyze_module(module);
                    }
                    let _span = debug_span!("sonatina.optim.pipeline.inline").entered();
                    let mut inliner = Inliner::new(self.inliner_config);
                    let stats = {
                        let _span = trace_span!("sonatina.optim.pipeline.pass.inliner").entered();
                        inliner.run(module)
                    };
                    func_behavior_dirty = stats.changed;
                }
                Step::FuncPasses(passes) => {
                    let _span = debug_span!(
                        "sonatina.optim.pipeline.func_passes",
                        pass_count = passes.len()
                    )
                    .entered();
                    run_function_pass_round(
                        module,
                        passes,
                        &mut func_behavior_dirty,
                        FuncPassOverrides::default(),
                    );
                }
                Step::DeadArgElim => {
                    let _span = debug_span!("sonatina.optim.pipeline.dead_arg_elim").entered();
                    run_dead_arg_elim(module, DeadArgElimConfig::default());
                    func_behavior_dirty = true;
                }
                Step::DeadFuncElim => {
                    let _span = debug_span!("sonatina.optim.pipeline.dead_func_elim").entered();
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
        Self::default_pipeline()
    }
}

#[derive(Default, Clone, Copy)]
pub(crate) struct FuncPassOverrides<'a> {
    pub(crate) funcs: Option<&'a [FuncRef]>,
    pub(crate) local_object_args: Option<&'a LocalObjectArgMap>,
    pub(crate) object_effects: Option<&'a ObjectEffectSummaryMap>,
}

pub(crate) fn run_function_pass_round(
    module: &Module,
    passes: &[Pass],
    func_behavior_dirty: &mut bool,
    overrides: FuncPassOverrides<'_>,
) {
    for &pass in passes {
        if *func_behavior_dirty && pass.needs_func_behavior() {
            let _span = trace_span!("sonatina.optim.pipeline.func_behavior_analyze").entered();
            func_behavior::analyze_module(module);
            *func_behavior_dirty = false;
        }
        run_module_pass(pass, module, overrides);
        if pass.invalidates_func_behavior() {
            *func_behavior_dirty = true;
        }
    }
}

fn run_module_pass(pass: Pass, module: &Module, overrides: FuncPassOverrides<'_>) {
    let _span = debug_span!("sonatina.optim.pipeline.pass_round", pass = pass.as_str()).entered();
    let owned_object_effects = if overrides.object_effects.is_none() {
        matches!(
            pass,
            Pass::ObjectLoadStore | Pass::AggregateScalarize | Pass::Gvn | Pass::Licm
        )
        .then(|| compute_object_effect_summaries(module))
    } else {
        None
    };
    let object_effects = overrides.object_effects.or(owned_object_effects.as_ref());
    let owned_local_object_args = if overrides.local_object_args.is_none() {
        object_effects
            .map(|effects| collect_local_object_arg_info_with_effects(module, effects))
            .or_else(|| {
                matches!(
                    pass,
                    Pass::ObjectLoadStore | Pass::AggregateScalarize | Pass::Gvn | Pass::Licm
                )
                .then(|| collect_local_object_arg_info(module))
            })
    } else {
        None
    };
    let local_object_args = overrides
        .local_object_args
        .or(owned_local_object_args.as_ref());
    if let Some(funcs) = overrides.funcs {
        funcs.par_iter().copied().for_each(|func_ref| {
            module.func_store.modify(func_ref, |func| {
                let _span = debug_span!(
                    "sonatina.optim.pipeline.function",
                    func_ref = func_ref.as_u32()
                )
                .entered();
                let mut ctx = PassContext::default();
                run_pass(
                    pass,
                    Some(func_ref),
                    func,
                    &mut ctx,
                    local_object_args,
                    object_effects,
                );
            });
        });
    } else {
        module.func_store.par_for_each(|func_ref, func| {
            let _span = debug_span!(
                "sonatina.optim.pipeline.function",
                func_ref = func_ref.as_u32()
            )
            .entered();
            let mut ctx = PassContext::default();
            run_pass(
                pass,
                Some(func_ref),
                func,
                &mut ctx,
                local_object_args,
                object_effects,
            );
        });
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
fn run_pass(
    pass: Pass,
    func_ref: Option<sonatina_ir::module::FuncRef>,
    func: &mut Function,
    ctx: &mut PassContext,
    local_object_args: Option<&LocalObjectArgMap>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) {
    let _span = trace_span!("sonatina.optim.pipeline.pass", pass = pass.as_str()).entered();
    match pass {
        Pass::LegalizeMultiResult => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.legalize_multi_result").entered();
            legalize_multi_result(func);
        }
        Pass::CfgCleanup => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.cfg_cleanup").entered();
            CfgCleanup::new(CleanupMode::Strict).run(func);
        }
        Pass::AggregateCombine => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.aggregate_combine").entered();
            AggregateCombine::default().run(func);
        }
        Pass::BranchCanonicalize => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.branch_canonicalize").entered();
            BranchCanonicalize::new().run(func);
        }
        Pass::ObjectLoadStore => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.object_load_store").entered();
            if let (Some(func_ref), Some(local_object_args), Some(object_effects)) =
                (func_ref, local_object_args, object_effects)
            {
                ObjectLoadStore::default().run_for_func(
                    func_ref,
                    func,
                    local_object_args,
                    object_effects,
                );
            } else {
                ObjectLoadStore::default().run(func);
            }
        }
        Pass::AggregateScalarize => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.aggregate_scalarize").entered();
            if let (Some(func_ref), Some(local_object_args)) = (func_ref, local_object_args) {
                AggregateScalarize::default().run_for_func(func_ref, func, local_object_args);
            } else {
                AggregateScalarize::default().run(func);
            }
        }
        Pass::LoadStore => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.load_store").entered();
            {
                let _span = trace_span!("sonatina.optim.pipeline.load_store.compute_cfg").entered();
                ctx.cfg.compute(func);
            }
            let mut solver = LoadStoreSolver::new();
            {
                let _span = trace_span!("sonatina.optim.pipeline.load_store.solve").entered();
                solver.run(func, &mut ctx.cfg);
            }
        }
        Pass::ScalarCanonicalize => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.scalar_canonicalize").entered();
            ScalarCanonicalize::new().run(func);
        }
        Pass::KnownBitsSimplify => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.known_bits_simplify").entered();
            KnownBitsSimplify::new().run(func);
        }
        Pass::CheckedArithElim => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.checked_arith_elim").entered();
            if !has_supported_checked_arith(func) {
                return;
            }
            {
                let _span =
                    trace_span!("sonatina.optim.pipeline.checked_arith_elim.compute_cfg").entered();
                ctx.cfg.compute(func);
            }
            {
                let _span =
                    trace_span!("sonatina.optim.pipeline.checked_arith_elim.compute_domtree")
                        .entered();
                ctx.domtree.compute(&ctx.cfg);
            }
            {
                let _span =
                    trace_span!("sonatina.optim.pipeline.checked_arith_elim.compute_looptree")
                        .entered();
                ctx.lpt.compute(&ctx.cfg, &ctx.domtree);
            }
            {
                let _span =
                    trace_span!("sonatina.optim.pipeline.checked_arith_elim.solve").entered();
                CheckedArithElim::new().run(func, &ctx.cfg, &ctx.lpt);
            }
        }
        Pass::Sccp => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.sccp").entered();
            // SccpSolver::run is composite: internally does
            //   CfgCleanup → SCCP solving → CfgCleanup → ADCE.
            {
                let _span = trace_span!("sonatina.optim.pipeline.sccp.compute_cfg").entered();
                ctx.cfg.compute(func);
            }
            let mut solver = SccpSolver::new();
            {
                let _span = trace_span!("sonatina.optim.pipeline.sccp.solve").entered();
                solver.run(func, &mut ctx.cfg);
            }
            {
                let _span = trace_span!("sonatina.optim.pipeline.sccp.cleanup").entered();
                CfgCleanup::new(CleanupMode::Strict).run(func);
            }
        }
        Pass::Adce => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.adce").entered();
            AdceSolver::new().run(func);
        }
        Pass::Licm => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.licm").entered();
            {
                let _span = trace_span!("sonatina.optim.pipeline.licm.compute_cfg").entered();
                ctx.cfg.compute(func);
            }
            {
                let _span = trace_span!("sonatina.optim.pipeline.licm.compute_domtree").entered();
                ctx.domtree.compute(&ctx.cfg);
            }
            {
                let _span = trace_span!("sonatina.optim.pipeline.licm.compute_looptree").entered();
                ctx.lpt.compute(&ctx.cfg, &ctx.domtree);
            }
            let mut solver = LicmSolver::new();
            let mut object_memory = ObjectMemoryAnalysis::default();
            let func_local_object_args = func_ref
                .and_then(|func_ref| local_object_args.and_then(|args| args.get(&func_ref)));
            object_memory.compute(func, func_local_object_args, object_effects);
            {
                let _span = trace_span!("sonatina.optim.pipeline.licm.solve").entered();
                solver.run_with_object_memory(
                    func,
                    &mut ctx.cfg,
                    &mut ctx.lpt,
                    Some(&object_memory),
                );
            }
            {
                let _span = trace_span!("sonatina.optim.pipeline.licm.cleanup").entered();
                CfgCleanup::new(CleanupMode::Strict).run(func);
            }
        }
        Pass::LoopStrengthReduce => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.loop_strength_reduce").entered();
            {
                let _span = trace_span!("sonatina.optim.pipeline.loop_strength_reduce.compute_cfg")
                    .entered();
                ctx.cfg.compute(func);
            }
            {
                let _span =
                    trace_span!("sonatina.optim.pipeline.loop_strength_reduce.compute_domtree")
                        .entered();
                ctx.domtree.compute(&ctx.cfg);
            }
            {
                let _span =
                    trace_span!("sonatina.optim.pipeline.loop_strength_reduce.compute_looptree")
                        .entered();
                ctx.lpt.compute(&ctx.cfg, &ctx.domtree);
            }
            {
                let _span =
                    trace_span!("sonatina.optim.pipeline.loop_strength_reduce.solve").entered();
                LoopStrengthReduce::new().run(func, &mut ctx.cfg, &mut ctx.domtree, &mut ctx.lpt);
            }
        }
        Pass::Gvn => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.gvn").entered();
            {
                let _span = trace_span!("sonatina.optim.pipeline.gvn.compute_cfg").entered();
                ctx.cfg.compute(func);
            }
            {
                let _span = trace_span!("sonatina.optim.pipeline.gvn.compute_domtree").entered();
                ctx.domtree.compute(&ctx.cfg);
            }
            let mut solver = GvnSolver::new();
            let mut object_memory = ObjectMemoryAnalysis::default();
            let func_local_object_args = func_ref
                .and_then(|func_ref| local_object_args.and_then(|args| args.get(&func_ref)));
            object_memory.compute(func, func_local_object_args, object_effects);
            {
                let _span = trace_span!("sonatina.optim.pipeline.gvn.solve").entered();
                solver.run_with_object_memory(
                    func,
                    &mut ctx.cfg,
                    &mut ctx.domtree,
                    Some(&object_memory),
                );
            }
        }
        Pass::RebuildUsers => {
            let _span = trace_span!("sonatina.optim.pipeline.pass.rebuild_users").entered();
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
        module::{FuncHints, InlineHint},
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
        builder.insert_inst_no_result_with(|| Return::new_single(is, sum));
        builder.seal_all();
        builder.finish();

        mb.build()
    }

    fn run_test_func_passes(module: &mut sonatina_ir::module::Module, passes: &[Pass]) {
        let mut pipeline = Pipeline::new();
        pipeline.add_step(Step::FuncPasses(passes.to_vec()));
        pipeline.run(module);
    }

    #[test]
    fn default_pipeline_runs() {
        let pipeline = Pipeline::default_pipeline();
        let mut module = build_test_module();
        pipeline.run(&mut module);
    }

    #[test]
    fn default_pipeline_uses_speed_profile() {
        let pipeline = Pipeline::default_pipeline();
        assert_eq!(
            pipeline.inliner_config.splice_max_insts,
            Pipeline::speed().inliner_config.splice_max_insts
        );
        assert_eq!(
            Pipeline::default().inliner_config.splice_max_insts,
            Pipeline::speed().inliner_config.splice_max_insts
        );
        assert_ne!(
            pipeline.inliner_config.splice_max_insts,
            Pipeline::size().inliner_config.splice_max_insts
        );
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
    fn licm_pass_triggers_func_behavior_analysis() {
        assert!(Pass::Licm.needs_func_behavior());
        assert!(Pass::Licm.invalidates_func_behavior());
    }

    #[test]
    fn func_passes_single_function_module() {
        let mut module = build_test_module();
        run_test_func_passes(
            &mut module,
            &[
                Pass::CfgCleanup,
                Pass::Sccp,
                Pass::ScalarCanonicalize,
                Pass::Gvn,
                Pass::KnownBitsSimplify,
            ],
        );
    }

    #[test]
    fn func_passes_refresh_func_behavior_between_passes() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %exit_now() {
    block0:
        br 1.i1 block1 block2;

    block1:
        evm_return 0.i256 0.i256;

    block2:
        return;
}

func private %caller() {
    block0:
        call %exit_now;
        return;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let mut pipeline = Pipeline::new();
        pipeline.add_step(Step::FuncPasses(vec![
            Pass::CfgCleanup,
            Pass::Sccp,
            Pass::CfgCleanup,
        ]));
        pipeline.run(&mut module);

        let caller = module
            .funcs()
            .into_iter()
            .find(|func_ref| module.ctx.func_sig(*func_ref, |sig| sig.name() == "caller"))
            .expect("caller should exist");
        module.func_store.view(caller, |func| {
            let dumped = FuncWriter::new(caller, func).dump_string();
            assert!(
                dumped.contains("unreachable;"),
                "caller should be trimmed after a now-noreturn call:\n{dumped}"
            );
            assert!(
                !dumped.contains("return;"),
                "return after noreturn call should be removed:\n{dumped}"
            );
        });
    }

    #[test]
    fn cfg_cleanup_trims_noreturn_call_with_split_continuation() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %run() -> i256 {
block0:
    evm_return 0.i256 0.i256;
}

func private %test_run() {
block0:
    v0.i256 = call %run;
    v3.i1 = eq v0 2.i256;
    jump block2;

block2:
    v4.i1 = is_zero v3;
    br v4 block3 block4;

block3:
    evm_revert 0.i256 0.i256;

block4:
    jump block1;

block1:
    return;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        run_test_func_passes(&mut module, &[Pass::CfgCleanup]);

        let test_run = module
            .funcs()
            .into_iter()
            .find(|func_ref| {
                module
                    .ctx
                    .func_sig(*func_ref, |sig| sig.name() == "test_run")
            })
            .expect("test_run should exist");
        module.func_store.view(test_run, |func| {
            let dumped = FuncWriter::new(test_run, func).dump_string();
            assert!(
                dumped.contains("unreachable;"),
                "split continuation after noreturn call should be trimmed:\n{dumped}"
            );
            assert!(
                !dumped.contains("eq "),
                "trimmed tail should not leave eq behind:\n{dumped}"
            );
            assert!(
                !dumped.contains("is_zero "),
                "unreachable continuation should be removed:\n{dumped}"
            );
            assert!(
                !dumped.contains("undef"),
                "structural noreturn cleanup should not synthesize undef:\n{dumped}"
            );
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
    fn sccp_folds_logical_shr_mask_with_known_bits() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = shr 224.i256 v0;
        v2.i256 = and v1 4294967295.i256;
        return v2;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Sccp, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(dumped.contains("v1.i256 = shr 224.i256 v0;"), "{dumped}");
            assert!(!dumped.contains(" and "), "{dumped}");
            assert!(dumped.contains("return v1;"), "{dumped}");
        });
    }

    #[test]
    fn sccp_keeps_sar_mask_when_sign_is_unknown() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = sar 224.i256 v0;
        v2.i256 = and v1 4294967295.i256;
        return v2;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Sccp, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("v2.i256 = and v1 4294967295.i256;"),
                "{dumped}"
            );
        });
    }

    #[test]
    fn sccp_compare_contradiction_requires_defined_operands() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i256 {
    block0:
        v1.i8 = and undef.i8 1.i8;
        v2.i8 = or v1 2.i8;
        v3.i1 = eq v1 v2;
        br v3 block1 block2;

    block1:
        return 1.i256;

    block2:
        return 2.i256;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Sccp, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(dumped.contains("return 1.i256;"), "{dumped}");
            assert!(dumped.contains("return 2.i256;"), "{dumped}");
        });
    }

    #[test]
    fn sccp_does_not_copy_fold_phi_with_undef_incoming() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i1) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v1.i256 = phi (undef.i256 block1) (7.i256 block2);
        v2.i256 = and v1 4294967295.i256;
        return v2;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Sccp, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("v2.i256 = and v1 4294967295.i256;"),
                "{dumped}"
            );
        });
    }

    #[test]
    fn gvn_cses_pure_opaque_gep_with_identical_operands() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.*i256) -> *i256 {
    block0:
        v1.*i256 = gep v0 0.i256 1.i256;
        v2.*i256 = gep v0 0.i256 1.i256;
        return v2;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            let gep_count = dumped.matches(" = gep ").count();
            assert_eq!(
                gep_count, 1,
                "expected duplicate pure opaque geps to CSE:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_canonicalizes_non_binary_operands_before_cse() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.*i256, v1.i256) -> *i256 {
    block0:
        v2.i256 = add v1 0.i256;
        v3.*i256 = gep v0 0.i256 v2;
        v4.*i256 = gep v0 0.i256 v1;
        return v4;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            let gep_count = dumped.matches(" = gep ").count();
            assert_eq!(
                gep_count, 1,
                "expected congruent n-ary operands to canonicalize before CSE:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_keeps_distinct_obj_allocs_unique() {
        let source = r#"
target = "evm-ethereum-london"

type @box = { i256 };

func private %entry() -> i256 {
    block0:
        v0.objref<@box> = obj.alloc @box;
        v1.objref<i256> = obj.proj v0 0.i8;
        obj.store v1 1.i256;
        v2.objref<@box> = obj.alloc @box;
        v3.objref<i256> = obj.proj v2 0.i8;
        obj.store v3 2.i256;
        v4.i256 = obj.load v1;
        v5.i256 = obj.load v3;
        v6.i256 = add v4 v5;
        return v6;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            let alloc_count = dumped.matches(" = obj.alloc ").count();
            assert_eq!(
                alloc_count, 2,
                "distinct object allocations must not CSE:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_does_not_reuse_obj_load_across_obj_store() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i256 {
    block0:
        v0.objref<i256> = obj.alloc i256;
        obj.store v0 1.i256;
        v1.i256 = obj.load v0;
        obj.store v0 2.i256;
        v2.i256 = obj.load v0;
        v3.i256 = add v1 v2;
        return v3;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains(" = obj.load "),
                "GVN should fold each load to its reaching stored value:\n{dumped}"
            );
            assert!(
                dumped.contains("return 3.i256;"),
                "intervening store must still keep the two load results distinct:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_does_not_cse_uninitialized_obj_loads_from_fresh_alloc() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i256 {
    block0:
        v0.objref<i256> = obj.alloc i256;
        v1.i256 = obj.load v0;
        v2.i256 = obj.load v0;
        v3.i256 = add v1 v2;
        return v3;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            let load_count = dumped.matches(" = obj.load ").count();
            assert_eq!(
                load_count, 2,
                "fresh uninitialized loads must remain distinct:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_cses_obj_loads_across_read_only_helper_call() {
        let mut parsed = parse_module(
            r#"
target = "evm-ethereum-london"

func private %peek(v0.objref<i256>) {
    block0:
        v1.i256 = obj.load v0;
        return;
}

func private %entry(v0.i256) -> i256 {
    block0:
        v1.objref<i256> = obj.alloc i256;
        obj.store v1 v0;
        call %peek v1;
        v2.i256 = obj.load v1;
        v3.i256 = obj.load v1;
        v4.i256 = add v2 v3;
        return v4;
}
"#,
        )
        .expect("parse should succeed");
        let entry = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func_ref| {
                parsed
                    .module
                    .ctx
                    .func_sig(func_ref, |sig| sig.name() == "entry")
            })
            .expect("entry should exist");

        let mut pipeline = Pipeline::new();
        pipeline.add_step(Step::FuncPasses(vec![
            Pass::CfgCleanup,
            Pass::Gvn,
            Pass::CfgCleanup,
        ]));
        pipeline.run(&mut parsed.module);

        let dumped = parsed
            .module
            .func_store
            .view(entry, |func| FuncWriter::new(entry, func).dump_string());
        assert!(
            dumped.contains("call %peek v1;"),
            "helper call should remain visible:\n{dumped}"
        );
        assert!(
            !dumped.contains("obj.load v1"),
            "summary-aware GVN should eliminate repeated loads after the read-only helper:\n{dumped}"
        );
    }

    #[test]
    fn gvn_cses_repeated_join_obj_loads_through_object_memory_phi() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i1, v1.i256, v2.i256) -> i256 {
    block0:
        v3.objref<i256> = obj.alloc i256;
        br v0 block1 block2;

    block1:
        obj.store v3 v1;
        jump block3;

    block2:
        obj.store v3 v2;
        jump block3;

    block3:
        v4.i256 = obj.load v3;
        v5.i256 = obj.load v3;
        v6.i256 = add v4 v5;
        return v6;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            let load_count = dumped.matches(" = obj.load ").count();
            assert_eq!(
                load_count, 1,
                "GVN should CSE repeated join loads keyed by the same object-memory phi:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_treats_globals_as_always_available() {
        let source = r#"
target = "evm-ethereum-london"

global public const i256 $G = 0;

func private %entry(v0.i1) -> *i256 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v1.*i256 = phi ($G block1) ($G block2);
        return v1;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return $G;"),
                "expected global to be available for phi simplification:\n{dumped}"
            );
            assert!(
                !dumped.contains(" = phi "),
                "phi over identical globals should be eliminated:\n{dumped}"
            );
        });
    }

    #[test]
    fn licm_hoists_initialized_obj_load_out_of_loop() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i256, v1.i1) -> i256 {
    block0:
        v2.objref<i256> = obj.alloc i256;
        obj.store v2 v0;
        jump block1;

    block1:
        br v1 block2 block3;

    block2:
        v3.i256 = obj.load v2;
        v4.i256 = add v3 1.i256;
        jump block1;

    block3:
        return 0.i256;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let mut object_memory = ObjectMemoryAnalysis::default();
            object_memory.compute(func, None, None);
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let mut domtree = DomTree::new();
            domtree.compute(&cfg);
            let mut lpt = LoopTree::new();
            lpt.compute(&cfg, &domtree);
            let load = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find(|&inst| {
                    sonatina_ir::inst::downcast::<&sonatina_ir::inst::data::ObjLoad>(
                        func.inst_set(),
                        func.dfg.inst(inst),
                    )
                    .is_some()
                })
                .expect("loop load should exist before LICM");
            let lp = lpt.loops().next().expect("loop should exist");
            assert!(
                object_memory.read_is_loop_invariant(func, &cfg, &lpt, lp, load),
                "object-memory analysis should mark the loop load as invariant before LICM"
            );
        });
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Licm, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            let block0 = dumped
                .split("block0:")
                .nth(1)
                .and_then(|tail| tail.split("block1:").next())
                .expect("block0 section should exist");
            let block2 = dumped
                .split("block2:")
                .nth(1)
                .and_then(|tail| tail.split("block3:").next())
                .expect("block2 section should exist");
            assert!(
                block0.contains("obj.load"),
                "loop-invariant object load should hoist to the preheader:\n{dumped}"
            );
            assert!(
                !block2.contains("obj.load"),
                "loop body should no longer contain the hoisted object load:\n{dumped}"
            );
        });
    }

    #[test]
    fn licm_hoists_initialized_obj_load_out_of_loop_across_read_only_helper_call() {
        let mut parsed = parse_module(
            r#"
target = "evm-ethereum-london"

func private %peek(v0.objref<i256>) {
    block0:
        v1.i256 = obj.load v0;
        return;
}

func private %entry(v0.i256, v1.i1) -> i256 {
    block0:
        v2.objref<i256> = obj.alloc i256;
        obj.store v2 v0;
        jump block1;

    block1:
        br v1 block2 block3;

    block2:
        call %peek v2;
        v3.i256 = obj.load v2;
        v4.i256 = add v3 1.i256;
        jump block1;

    block3:
        return 0.i256;
}
"#,
        )
        .expect("parse should succeed");
        let entry = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func_ref| {
                parsed
                    .module
                    .ctx
                    .func_sig(func_ref, |sig| sig.name() == "entry")
            })
            .expect("entry should exist");

        let mut pipeline = Pipeline::new();
        pipeline.add_step(Step::FuncPasses(vec![
            Pass::CfgCleanup,
            Pass::Licm,
            Pass::CfgCleanup,
        ]));
        pipeline.run(&mut parsed.module);

        let dumped = parsed
            .module
            .func_store
            .view(entry, |func| FuncWriter::new(entry, func).dump_string());
        let block0 = dumped
            .split("block0:")
            .nth(1)
            .and_then(|tail| tail.split("block1:").next())
            .expect("block0 section should exist");
        let block2 = dumped
            .split("block2:")
            .nth(1)
            .and_then(|tail| tail.split("block3:").next())
            .expect("block2 section should exist");
        assert!(
            block0.contains("obj.load"),
            "LICM should hoist the loop-invariant load into the preheader even across a read-only helper call:\n{dumped}"
        );
        assert!(
            !block2.contains("obj.load"),
            "loop body should no longer contain the hoisted load:\n{dumped}"
        );
    }

    #[test]
    fn licm_does_not_hoist_obj_load_across_loop_store() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i256, v1.i1) -> i256 {
    block0:
        v2.objref<i256> = obj.alloc i256;
        obj.store v2 0.i256;
        jump block1;

    block1:
        br v1 block2 block3;

    block2:
        obj.store v2 v0;
        v3.i256 = obj.load v2;
        v4.i256 = add v3 1.i256;
        jump block1;

    block3:
        return 0.i256;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Licm, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            let block0 = dumped
                .split("block0:")
                .nth(1)
                .and_then(|tail| tail.split("block1:").next())
                .expect("block0 section should exist");
            let block2 = dumped
                .split("block2:")
                .nth(1)
                .and_then(|tail| tail.split("block3:").next())
                .expect("block2 section should exist");
            assert!(
                !block0.contains("obj.load"),
                "loop-clobbered object load must not hoist:\n{dumped}"
            );
            assert!(
                block2.contains("obj.load"),
                "loop body should retain the load when the slice is clobbered each iteration:\n{dumped}"
            );
        });
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

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Sccp, Pass::Gvn, Pass::CfgCleanup],
        );

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
    fn gvn_uses_br_table_default_when_known_scrutinee_has_no_match() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i32 {
    block0:
        br_table 42.i8 block3 (0.i8 block1) (1.i8 block2);

    block1:
        return 11.i32;

    block2:
        return 22.i32;

    block3:
        return 33.i32;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return 33.i32;"),
                "expected default arm to stay reachable:\n{dumped}"
            );
            assert!(
                !dumped.contains("return 11.i32;"),
                "keyed arm with non-matching immediate scrutinee should be unreachable:\n{dumped}"
            );
            assert!(
                !dumped.contains("return 22.i32;"),
                "all non-default keyed arms should be unreachable when no key matches:\n{dumped}"
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

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

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

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

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
    fn gvn_phi_pruning_keeps_users_consistent_for_followup_sccp_dce() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i1, v1.i32) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        v2.i32 = add v1 3.i32;
        br 0.i1 block3 block4;

    block2:
        jump block3;

    block3:
        v3.i32 = phi (v2 block1) (7.i32 block2);
        return v3;

    block4:
        return 9.i32;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[
                Pass::CfgCleanup,
                Pass::ScalarCanonicalize,
                Pass::Gvn,
                Pass::KnownBitsSimplify,
                Pass::Sccp,
                Pass::CfgCleanup,
            ],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains(" = add "),
                "dead add should be removed after phi pruning:\n{dumped}"
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

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

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

    #[test]
    fn gvn_folds_logical_shr_mask_with_known_bits() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = shr 224.i256 v0;
        v2.i256 = and v1 4294967295.i256;
        return v2;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(dumped.contains("v1.i256 = shr 224.i256 v0;"), "{dumped}");
            assert!(!dumped.contains(" and "), "{dumped}");
            assert!(dumped.contains("return v1;"), "{dumped}");
        });
    }

    #[test]
    fn gvn_compare_contradiction_requires_defined_operands() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i256 {
    block0:
        v1.i8 = and undef.i8 1.i8;
        v2.i8 = or v1 2.i8;
        v3.i1 = eq v1 v2;
        br v3 block1 block2;

    block1:
        return 1.i256;

    block2:
        return 2.i256;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(dumped.contains("return 1.i256;"), "{dumped}");
            assert!(dumped.contains("return 2.i256;"), "{dumped}");
        });
    }

    #[test]
    fn gvn_does_not_cancel_sub_add_when_operand_may_be_undef() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i256 {
    block0:
        v1.i256 = add 5.i256 undef.i256;
        v2.i256 = sub v1 undef.i256;
        v3.i1 = eq v2 5.i256;
        br v3 block1 block2;

    block1:
        return 1.i256;

    block2:
        return 2.i256;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return 1.i256;"),
                "then branch should remain reachable:\n{dumped}"
            );
            assert!(
                dumped.contains("return 2.i256;"),
                "else branch should remain reachable when sub/add cancellation operand may be undef:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_cancels_add_sub_when_operand_is_defined() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = sub v0 v1;
        v3.i256 = add v1 v2;
        return v3;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return v0;"),
                "expected add/sub cancellation to fold to v0:\n{dumped}"
            );
            assert!(
                !dumped.contains(" = add "),
                "expected add instruction to be removed:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_folds_constant_shifts() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry() -> i32 {
    block0:
        v1.i32 = shl 2.i32 3.i32;
        v2.i32 = shr 1.i32 v1;
        return v2;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return 6.i32;"),
                "expected constant-shift chain to fold:\n{dumped}"
            );
            assert!(
                !dumped.contains(" = shl "),
                "expected shl instruction to be removed:\n{dumped}"
            );
            assert!(
                !dumped.contains(" = shr "),
                "expected shr instruction to be removed:\n{dumped}"
            );
        });
    }

    #[test]
    fn gvn_infers_equality_through_bool_zero_compare() {
        let source = r#"
target = "evm-ethereum-london"

func private %entry(v0.i32, v1.i32) -> i32 {
    block0:
        v2.i1 = ne v0 v1;
        v3.i1 = eq v2 0.i1;
        br v3 block1 block2;

    block1:
        v4.i32 = sub v0 v1;
        return v4;

    block2:
        return 7.i32;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let func_ref = module.funcs()[0];
        run_test_func_passes(
            &mut module,
            &[Pass::CfgCleanup, Pass::Gvn, Pass::CfgCleanup],
        );

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("return 0.i32;"),
                "expected inferred equality from eq(ne x y, 0) to fold sub in true branch:\n{dumped}"
            );
        });
    }

    #[test]
    fn size_and_speed_use_distinct_inliner_profiles() {
        let size = Pipeline::size();
        assert!(size.inliner_config.enable_full_inliner);
        assert_eq!(size.inliner_config.splice_max_insts, 6);
        assert!(size.inliner_config.call_overhead_bonus > 0);

        let speed = Pipeline::speed();
        assert!(speed.inliner_config.enable_full_inliner);
        assert!(size.inliner_config.splice_max_insts > speed.inliner_config.splice_max_insts);
        assert!(speed.inliner_config.max_inlinee_blocks > 0);
        assert!(speed.inliner_config.max_inlinee_insts > 0);
        assert!(
            size.inliner_config.max_growth_per_caller >= speed.inliner_config.max_growth_per_caller
        );
        assert!(size.inliner_config.max_total_growth >= speed.inliner_config.max_total_growth);
        assert_ne!(
            speed.inliner_config.inline_threshold,
            size.inliner_config.inline_threshold
        );
        assert_ne!(
            speed.inliner_config.inline_threshold_cold,
            size.inliner_config.inline_threshold_cold
        );
    }

    #[test]
    fn size_and_speed_share_same_step_schedule() {
        let size = Pipeline::size();
        let speed = Pipeline::speed();
        assert_eq!(size.steps.len(), speed.steps.len());
        for (size_step, speed_step) in size.steps.iter().zip(speed.steps.iter()) {
            match (size_step, speed_step) {
                (Step::Inline, Step::Inline)
                | (Step::DeadArgElim, Step::DeadArgElim)
                | (Step::DeadFuncElim, Step::DeadFuncElim) => {}
                (Step::FuncPasses(size_passes), Step::FuncPasses(speed_passes)) => {
                    assert_eq!(size_passes, speed_passes);
                }
                _ => panic!("size and speed should differ only in inliner config"),
            }
        }
    }

    #[test]
    fn optimized_pipelines_preserve_noinline_hint_across_second_inline_round() {
        let source = r#"
target = "evm-ethereum-london"

func private %id(v0.i32) -> i32 {
    block0:
        return v0;
}

func public %caller(v0.i32) -> i32 {
    block0:
        v1.i32 = call %id v0;
        return v1;
}
"#;

        for (name, pipeline) in [("size", Pipeline::size()), ("speed", Pipeline::speed())] {
            let mut module = parse_module(source).expect("parse should succeed").module;
            let id = module
                .funcs()
                .into_iter()
                .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == "id"))
                .expect("id function should exist");
            let caller = module
                .funcs()
                .into_iter()
                .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == "caller"))
                .expect("caller function should exist");

            module.ctx.set_func_hints(id, FuncHints::NOINLINE);

            pipeline.run(&mut module);

            module.func_store.view(caller, |func| {
                let dumped = FuncWriter::new(caller, func).dump_string();
                assert!(
                    dumped.contains("call %id"),
                    "NOINLINE hint should survive the {name} pipeline:\n{dumped}"
                );
            });
        }
    }

    #[test]
    fn optimized_pipelines_treat_inline_hint_as_strong_preference() {
        let source = r#"
target = "evm-ethereum-london"

func private %costly(v0.i1, v1.i32) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        return v1;

    block2:
        v2.i32 = add v1 1.i32;
        v3.i32 = add v2 1.i32;
        v4.i32 = add v3 1.i32;
        v5.i32 = add v4 1.i32;
        v6.i32 = add v5 1.i32;
        v7.i32 = add v6 1.i32;
        return v7;
}

func public %caller(v0.i1, v1.i32) -> i32 {
    block0:
        v2.i32 = call %costly v0 v1;
        v3.i32 = call %costly v0 v2;
        return v3;
}
"#;

        for (name, pipeline) in [("size", Pipeline::size()), ("speed", Pipeline::speed())] {
            let mut baseline = parse_module(source).expect("parse should succeed").module;
            let caller = baseline
                .funcs()
                .into_iter()
                .find(|&func_ref| {
                    baseline
                        .ctx
                        .func_sig(func_ref, |sig| sig.name() == "caller")
                })
                .expect("caller function should exist");

            pipeline.run(&mut baseline);

            baseline.func_store.view(caller, |func| {
                let dumped = FuncWriter::new(caller, func).dump_string();
                assert!(
                    dumped.contains("call %costly"),
                    "baseline {name} pipeline should leave the costly helper uninlined:\n{dumped}"
                );
            });

            let mut hinted = parse_module(source).expect("parse should succeed").module;
            let costly = hinted
                .funcs()
                .into_iter()
                .find(|&func_ref| hinted.ctx.func_sig(func_ref, |sig| sig.name() == "costly"))
                .expect("costly function should exist");
            let caller = hinted
                .funcs()
                .into_iter()
                .find(|&func_ref| hinted.ctx.func_sig(func_ref, |sig| sig.name() == "caller"))
                .expect("caller function should exist");

            hinted.ctx.set_inline_hint(costly, InlineHint::Inline);
            pipeline.run(&mut hinted);

            hinted.func_store.view(caller, |func| {
                let dumped = FuncWriter::new(caller, func).dump_string();
                assert!(
                    !dumped.contains("call %costly"),
                    "inline hint should force the {name} pipeline past heuristic cost:\n{dumped}"
                );
            });
        }
    }

    #[test]
    fn inline_analyzes_func_behavior_before_first_round() {
        let source = r#"
target = "evm-ethereum-london"

func private %pure(v0.i1, v1.i32) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        return v1;

    block2:
        v2.i32 = add v1 2.i32;
        return v2;
}

func private %helper(v0.i1, v1.i32) -> i32 {
    block0:
        v2.i32 = call %pure v0 v1;
        v3.i32 = add v2 1.i32;
        return v3;
}

func public %caller(v0.i1, v1.i32) -> i32 {
    block0:
        v2.i32 = call %helper v0 v1;
        return v2;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let caller = module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == "caller"))
            .expect("caller function should exist");
        let mut pipeline = Pipeline::new();
        pipeline.inliner_config = InlinerConfig {
            splice_require_pure: true,
            ..InlinerConfig::default()
        };
        pipeline.add_step(Step::Inline);

        pipeline.run(&mut module);

        module.func_store.view(caller, |func| {
            let dumped = FuncWriter::new(caller, func).dump_string();
            assert!(
                !dumped.contains("call %helper"),
                "first inline round should splice helper once callee purity is analyzed:\n{dumped}"
            );
            assert!(
                dumped.contains("call %pure"),
                "multi-block pure callee should remain as a call after helper splicing:\n{dumped}"
            );
        });
    }

    #[test]
    fn inline_recomputes_func_behavior_before_second_round() {
        let source = r#"
target = "evm-ethereum-london"

func private %pure_after_cleanup(v0.i1, v1.*i32, v2.i32) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        br 0.i1 block3 block4;

    block2:
        return v2;

    block3:
        mstore v1 1.i32 i32;
        return 99.i32;

    block4:
        v3.i32 = add v2 2.i32;
        return v3;
}

func private %helper(v0.i1, v1.*i32, v2.i32) -> i32 {
    block0:
        v3.i32 = call %pure_after_cleanup v0 v1 v2;
        v4.i32 = add v3 1.i32;
        return v4;
}

func public %caller(v0.i1, v1.*i32, v2.i32) -> i32 {
    block0:
        v3.i32 = call %helper v0 v1 v2;
        return v3;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let caller = module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == "caller"))
            .expect("caller function should exist");
        let mut pipeline = Pipeline::new();
        pipeline.inliner_config = InlinerConfig {
            splice_require_pure: true,
            ..InlinerConfig::default()
        };
        pipeline
            .add_step(Step::Inline)
            .add_step(Step::FuncPasses(vec![
                Pass::CfgCleanup,
                Pass::Sccp,
                Pass::CfgCleanup,
            ]))
            .add_step(Step::Inline);

        pipeline.run(&mut module);

        module.func_store.view(caller, |func| {
            let dumped = FuncWriter::new(caller, func).dump_string();
            assert!(
                !dumped.contains("call %helper"),
                "second inline round should see updated callee purity after optimization:\n{dumped}"
            );
            assert!(
                dumped.contains("call %pure_after_cleanup"),
                "helper splicing should leave the still-multi-block inner call in place:\n{dumped}"
            );
        });
    }

    #[test]
    fn licm_recomputes_func_behavior_before_licm_only_step() {
        let source = r#"
target = "evm-ethereum-london"

func private %pure_after_cleanup(v0.i1, v1.*i32, v2.i32) -> i32 {
    block0:
        br v0 block1 block2;

    block1:
        br 0.i1 block3 block4;

    block2:
        return v2;

    block3:
        mstore v1 1.i32 i32;
        return 99.i32;

    block4:
        v3.i32 = add v2 2.i32;
        return v3;
}

func private %entry(v0.i1, v1.*i32, v2.i32) -> i32 {
    block0:
        jump block1;

    block1:
        br v0 block2 block3;

    block2:
        v3.i32 = call %pure_after_cleanup v0 v1 v2;
        v4.i32 = add v3 1.i32;
        jump block1;

    block3:
        return 0.i32;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let entry = module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == "entry"))
            .expect("entry should exist");
        let mut pipeline = Pipeline::new();
        pipeline
            .add_step(Step::FuncPasses(vec![
                Pass::CfgCleanup,
                Pass::Sccp,
                Pass::CfgCleanup,
            ]))
            .add_step(Step::FuncPasses(vec![Pass::Licm]));

        pipeline.run(&mut module);

        let dumped = module
            .func_store
            .view(entry, |func| FuncWriter::new(entry, func).dump_string());
        let block0 = dumped
            .split("block0:")
            .nth(1)
            .and_then(|tail| tail.split("block1:").next())
            .expect("block0 section should exist");
        let block2 = dumped
            .split("block2:")
            .nth(1)
            .and_then(|tail| tail.split("block3:").next())
            .expect("block2 section should exist");
        assert!(
            block0.contains("call %pure_after_cleanup"),
            "LICM-only step should see refreshed callee effects and hoist the invariant call:\n{dumped}"
        );
        assert!(
            !block2.contains("call %pure_after_cleanup"),
            "loop body should no longer contain the hoisted call after LICM:\n{dumped}"
        );
    }

    #[test]
    fn dead_arg_elim_step_is_followed_by_cleanup_that_erases_dead_actual_computation() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %sink(v0.i256) -> i256 {
    block0:
        return 7.i256;
}

func private %caller(v0.i256) -> i256 {
    block0:
        v1.i256 = add v0 1.i256;
        v2.i256 = call %sink v1;
        return v2;
}

func public %entry(v0.i256) -> i256 {
    block0:
        v1.i256 = call %caller v0;
        return v1;
}
"#;

        let mut module = parse_module(source).expect("parse should succeed").module;
        let caller = module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == "caller"))
            .expect("caller function should exist");
        let mut pipeline = Pipeline::new();
        pipeline
            .add_step(Step::DeadArgElim)
            .add_step(Step::FuncPasses(POST_DEAD_ARG_CLEANUP_PASSES.to_vec()));

        pipeline.run(&mut module);

        let sig = module
            .ctx
            .get_sig(caller)
            .expect("caller signature should exist");
        assert!(sig.args().is_empty(), "caller arg should be eliminated");
        module.func_store.view(caller, |func| {
            let dumped = FuncWriter::new(caller, func).dump_string();
            assert!(
                !dumped.contains("add "),
                "cleanup after dead-arg elim should remove dead actual computation:\n{dumped}"
            );
            assert!(
                dumped.contains("call %sink"),
                "caller should still call sink after cleanup:\n{dumped}"
            );
        });
    }

    #[test]
    fn explicit_func_subset_only_runs_passes_on_selected_functions() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %selected() -> i256 {
block0:
    br 1.i1 block1 block2;

block1:
    return 7.i256;

block2:
    return 9.i256;
}

func private %other() -> i256 {
block0:
    br 1.i1 block1 block2;

block1:
    return 11.i256;

block2:
    return 13.i256;
}
"#;

        let module = parse_module(source).expect("parse should succeed").module;
        let funcs = module.funcs();
        let selected = funcs
            .iter()
            .copied()
            .find(|func_ref| {
                module
                    .ctx
                    .func_sig(*func_ref, |sig| sig.name() == "selected")
            })
            .expect("selected should exist");
        let other = funcs
            .iter()
            .copied()
            .find(|func_ref| module.ctx.func_sig(*func_ref, |sig| sig.name() == "other"))
            .expect("other should exist");

        let mut func_behavior_dirty = true;
        run_function_pass_round(
            &module,
            &[Pass::Sccp, Pass::CfgCleanup],
            &mut func_behavior_dirty,
            FuncPassOverrides {
                funcs: Some(&[selected]),
                ..FuncPassOverrides::default()
            },
        );

        module.func_store.view(selected, |func| {
            let dumped = FuncWriter::new(selected, func).dump_string();
            assert!(
                !dumped.contains("block2"),
                "selected function should be optimized by the subset pass round:\n{dumped}"
            );
        });
        module.func_store.view(other, |func| {
            let dumped = FuncWriter::new(other, func).dump_string();
            assert!(
                dumped.contains("block2"),
                "unselected function should not be mutated by the subset pass round:\n{dumped}"
            );
        });
    }
}
