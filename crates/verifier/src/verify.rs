use rayon::prelude::*;
use sonatina_ir::{
    Function, Module,
    module::{FuncRef, ModuleCtx},
};

use crate::{
    VerifierConfig,
    diagnostic::{Diagnostic, DiagnosticCode, Location},
    report::VerificationReport,
};

mod function;
mod module_invariants;
mod type_utils;

pub fn verify_module(module: &Module, cfg: &VerifierConfig) -> VerificationReport {
    let mut report = verify_module_invariants(module, cfg);
    let declared_embed_symbols = module_invariants::collect_declared_embed_symbols(module);

    let mut func_reports: Vec<_> = module
        .func_store
        .funcs()
        .into_par_iter()
        .map(|func_ref| {
            let Some(func_report) = module.func_store.try_view(func_ref, |func| {
                function::verify_function_with_symbols(
                    &module.ctx,
                    func_ref,
                    func,
                    cfg,
                    Some(&declared_embed_symbols),
                )
            }) else {
                let mut report = VerificationReport::default();
                report.push(
                    Diagnostic::error(
                        DiagnosticCode::InvalidFuncRef,
                        "function reference is not present in function store",
                        Location::Function(func_ref),
                    ),
                    cfg.max_diagnostics,
                );
                return (func_ref, report);
            };

            (func_ref, func_report)
        })
        .collect();

    func_reports.sort_by_key(|(func_ref, _)| func_ref.as_u32());
    for (_, func_report) in func_reports {
        report.extend_with_limit(func_report.diagnostics, cfg.max_diagnostics);
        if cfg.max_diagnostics != 0 && report.diagnostics.len() >= cfg.max_diagnostics {
            break;
        }
    }

    report
}

pub fn verify_module_invariants(module: &Module, cfg: &VerifierConfig) -> VerificationReport {
    let mut report = VerificationReport::default();
    module_invariants::collect_module_invariants(module, cfg, &mut report);
    report
}

pub fn verify_function(
    ctx: &ModuleCtx,
    func_ref: FuncRef,
    func: &Function,
    cfg: &VerifierConfig,
) -> VerificationReport {
    function::verify_function_with_symbols(ctx, func_ref, func, cfg, None)
}

pub fn verify_module_or_panic(module: &Module, cfg: &VerifierConfig) {
    let report = verify_module(module, cfg);
    if report.has_errors() {
        eprintln!("SONATINA_IR_VERIFY_FAILURE: module");
        eprintln!("{report}");
        panic!("SONATINA_IR_VERIFY_FAILURE");
    }
}

pub fn verify_function_or_panic(
    ctx: &ModuleCtx,
    func_ref: FuncRef,
    func: &Function,
    cfg: &VerifierConfig,
) {
    let report = verify_function(ctx, func_ref, func, cfg);
    if report.has_errors() {
        eprintln!("SONATINA_IR_VERIFY_FAILURE: function {}", func_ref.as_u32());
        eprintln!("{report}");
        panic!("SONATINA_IR_VERIFY_FAILURE");
    }
}
