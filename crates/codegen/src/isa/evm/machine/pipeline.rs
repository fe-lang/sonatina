use sonatina_ir::{Module, module::FuncRef};
use tracing::debug_span;

use crate::{
    object::lowering::{MachinePassKind, StepKind},
    optim::{
        pipeline::{Pass, run_function_pass_round},
        steps::StepRecorder,
    },
};

use super::{
    super::{LateCleanupProfile, SwitchLoweringStrategy},
    branch::canonicalize_machine_branch_conditions,
    copy::coalesce_machine_copies,
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
    mut recorder: Option<&mut StepRecorder>,
) -> Result<(), String> {
    let _span = debug_span!(
        "sonatina.codegen.evm.machine.pipeline",
        funcs = funcs.len(),
        passes = MACHINE_PASSES.len()
    )
    .entered();
    let mut func_behavior_dirty = true;
    run_function_pass_round(
        module,
        MACHINE_PASSES,
        &mut func_behavior_dirty,
        Some(funcs),
        recorder.as_deref_mut(),
    );
    let use_tree = match switch_strategy {
        SwitchLoweringStrategy::Auto => profile == LateCleanupProfile::Speed,
        SwitchLoweringStrategy::Linear => false,
        SwitchLoweringStrategy::Tree => true,
    };
    if use_tree {
        let kind = (MachinePassKind::LowerSwitches, StepKind::LowerSwitches);
        StepRecorder::run_pass(recorder.as_deref_mut(), module, funcs, kind, |function| {
            lower_switches(function, reach_depth)
        });
    }
    if profile == LateCleanupProfile::Size {
        let kind = (
            MachinePassKind::BranchConditions,
            StepKind::BranchConditions,
        );
        StepRecorder::run_pass(recorder.as_deref_mut(), module, funcs, kind, |function| {
            canonicalize_machine_branch_conditions(function);
        });
    }
    let kind = (MachinePassKind::CoalesceCopies, StepKind::CoalesceCopies);
    StepRecorder::run_pass(recorder, module, funcs, kind, |function| {
        coalesce_machine_copies(function);
    });
    verify_machine_module(module, funcs)
}
