use sonatina_ir::{ControlFlowGraph, Function, Module, module::FuncRef};
use tracing::debug_span;

use crate::{
    analysis::func_behavior,
    domtree::DomTree,
    object::lowering::{MachinePassKind, StepKind},
    optim::{
        adce::{AdceCallPolicy, AdceSolver},
        aggregate::{ModuleObjectFacts, ObjectMemoryAnalysis},
        branch_canonicalize::BranchCanonicalize,
        cfg_cleanup::CfgCleanup,
        gvn::GvnSolver,
        known_bits_simplify::KnownBitsSimplify,
        pipeline::Pass,
        scalar_canonicalize::ScalarCanonicalize,
        sccp::SccpSolver,
        steps::StepLog,
    },
};

use super::{
    super::{LateCleanupProfile, SwitchLoweringStrategy},
    branch::canonicalize_machine_branch_conditions,
    copy::coalesce_machine_copies,
    record::{MachineRecorder, run_machine_pass},
    switch::lower_switches,
    verify::verify_machine_module,
};

const MACHINE_PASSES: &[Pass] = &[
    Pass::CfgCleanup,
    Pass::BranchCanonicalize,
    Pass::ScalarCanonicalize,
    Pass::KnownBitsSimplify,
    Pass::Sccp,
    Pass::Gvn,
    Pass::Adce,
    Pass::CfgCleanup,
];

pub(crate) fn run_machine_opt_pipeline(
    module: &Module,
    funcs: &[FuncRef],
    profile: LateCleanupProfile,
    switch_strategy: SwitchLoweringStrategy,
    reach_depth: u8,
    mut recorder: Option<&mut MachineRecorder>,
) -> Result<(), String> {
    let _span = debug_span!(
        "sonatina.codegen.evm.machine.pipeline",
        funcs = funcs.len(),
        passes = MACHINE_PASSES.len()
    )
    .entered();
    run_machine_pass_round(module, funcs, recorder.as_deref_mut());
    let use_tree = match switch_strategy {
        SwitchLoweringStrategy::Auto => profile == LateCleanupProfile::Speed,
        SwitchLoweringStrategy::Linear => false,
        SwitchLoweringStrategy::Tree => true,
    };
    if use_tree {
        run_machine_pass(
            module,
            funcs,
            recorder.as_deref_mut(),
            MachinePassKind::LowerSwitches,
            |_, function, mut log| {
                lower_switches(function, reach_depth);
                StepLog::step(&mut log, StepKind::LowerSwitches, function, None);
                false
            },
        );
    }
    if profile == LateCleanupProfile::Size {
        run_machine_pass(
            module,
            funcs,
            recorder.as_deref_mut(),
            MachinePassKind::BranchConditions,
            |_, function, mut log| {
                canonicalize_machine_branch_conditions(function);
                StepLog::step(&mut log, StepKind::BranchConditions, function, None);
                false
            },
        );
    }
    run_machine_pass(
        module,
        funcs,
        recorder,
        MachinePassKind::CoalesceCopies,
        |_, function, mut log| {
            coalesce_machine_copies(function);
            StepLog::step(&mut log, StepKind::CoalesceCopies, function, None);
            false
        },
    );
    verify_machine_module(module, funcs)
}

/// `MACHINE_PASSES` over `funcs`, as `optim::pipeline::run_function_pass_round`
/// runs them, reporting their steps to `recorder`.
fn run_machine_pass_round(
    module: &Module,
    funcs: &[FuncRef],
    mut recorder: Option<&mut MachineRecorder>,
) {
    let mut func_behavior_dirty = true;
    for &pass in MACHINE_PASSES {
        let _span =
            debug_span!("sonatina.codegen.evm.machine.pass", pass = pass.as_str()).entered();
        if func_behavior_dirty && pass.needs_func_behavior() {
            func_behavior::analyze_module(module);
            func_behavior_dirty = false;
        }
        let object_facts = pass
            .needs_object_facts()
            .then(|| ModuleObjectFacts::compute(module));
        let kind = match pass {
            Pass::CfgCleanup => MachinePassKind::CfgCleanup,
            Pass::BranchCanonicalize => MachinePassKind::BranchCanonicalize,
            Pass::ScalarCanonicalize => MachinePassKind::ScalarCanonicalize,
            Pass::KnownBitsSimplify => MachinePassKind::KnownBitsSimplify,
            Pass::Sccp => MachinePassKind::Sccp,
            Pass::Gvn => MachinePassKind::Gvn,
            Pass::Adce => MachinePassKind::Adce,
            _ => unreachable!("{pass:?} is not a machine pass"),
        };
        let changed = run_machine_pass(
            module,
            funcs,
            recorder.as_deref_mut(),
            kind,
            |func_ref, function, log| {
                run_pass(pass, func_ref, function, object_facts.as_ref(), log)
            },
        );
        func_behavior_dirty |= changed && pass.invalidates_func_behavior();
    }
}

/// `pass` on `func`, as `optim::pipeline::run_pass` runs it.
fn run_pass(
    pass: Pass,
    func_ref: FuncRef,
    func: &mut Function,
    object_facts: Option<&ModuleObjectFacts>,
    mut log: Option<&mut StepLog>,
) -> bool {
    let mut cfg = ControlFlowGraph::new();
    match pass {
        Pass::CfgCleanup => {
            let changed = CfgCleanup::new().run(func);
            StepLog::step(&mut log, StepKind::CfgCleanup, func, None);
            changed
        }
        Pass::BranchCanonicalize => {
            let changed = BranchCanonicalize::new().run(func);
            StepLog::step(&mut log, StepKind::BranchCanonicalize, func, None);
            changed
        }
        Pass::ScalarCanonicalize => ScalarCanonicalize::new().run_with_steps(func, log),
        Pass::KnownBitsSimplify => KnownBitsSimplify::new().run_with_steps(func, log),
        Pass::Sccp => {
            cfg.compute(func);
            let changed = SccpSolver::new().run_with_steps(func, &mut cfg, log.as_deref_mut());
            let cleaned = CfgCleanup::new().run(func);
            StepLog::step(&mut log, StepKind::CfgCleanup, func, None);
            changed || cleaned
        }
        Pass::Gvn => {
            cfg.compute(func);
            let mut domtree = DomTree::new();
            domtree.compute(&cfg);
            let mut object_memory = ObjectMemoryAnalysis::default();
            let object_facts = object_facts.expect("GVN runs with object facts");
            object_memory.compute(
                func,
                object_facts.local_args().get(&func_ref),
                Some(object_facts.effects()),
            );
            GvnSolver::new().run_with_steps(func, &mut cfg, &mut domtree, Some(&object_memory), log)
        }
        Pass::Adce => AdceSolver::with_call_policy(AdceCallPolicy::UseCurrentFuncEffects)
            .run_with_steps(func, log),
        _ => unreachable!("{pass:?} is not a machine pass"),
    }
}
