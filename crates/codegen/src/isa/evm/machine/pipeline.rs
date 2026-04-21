use sonatina_ir::{Module, module::FuncRef};
use tracing::debug_span;

use crate::optim::pipeline::{FuncPassOverrides, Pass, run_function_pass_round};

use super::verify::verify_machine_module;

const MACHINE_PASSES: &[Pass] = &[
    Pass::CfgCleanup,
    Pass::BranchCanonicalize,
    Pass::ScalarCanonicalize,
    Pass::KnownBitsSimplify,
    Pass::Sccp,
    Pass::Adce,
    Pass::CfgCleanup,
];

pub(crate) fn run_machine_opt_pipeline(module: &Module, funcs: &[FuncRef]) -> Result<(), String> {
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
    verify_machine_module(module, funcs)
}
