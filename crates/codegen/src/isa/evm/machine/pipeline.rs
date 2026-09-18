use sonatina_ir::{Module, module::FuncRef};
use tracing::debug_span;

use crate::optim::pipeline::{FuncPassOverrides, Pass, run_function_pass_round};

use super::{
    super::{LateCleanupProfile, SwitchLoweringStrategy},
    branch::canonicalize_machine_branch_conditions,
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
        FuncPassOverrides {
            funcs: Some(funcs),
            local_object_args: None,
            object_effects: None,
        },
    );
    let use_tree = match switch_strategy {
        SwitchLoweringStrategy::Auto => profile == LateCleanupProfile::Speed,
        SwitchLoweringStrategy::Linear => false,
        SwitchLoweringStrategy::Tree => true,
    };
    for &func in funcs {
        module.func_store.modify(func, |function| {
            if use_tree {
                lower_switches(function, reach_depth);
            }
            if profile == LateCleanupProfile::Size {
                canonicalize_machine_branch_conditions(function);
            }
        });
    }
    verify_machine_module(module, funcs)
}
