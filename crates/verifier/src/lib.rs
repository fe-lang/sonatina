mod config;
mod diagnostic;
mod report;
mod verify;

pub use config::{VerificationLevel, VerifierConfig};
pub use diagnostic::{Diagnostic, DiagnosticCode, Location, Note, Severity};
pub use report::VerificationReport;
pub use verify::{
    verify_function, verify_function_or_panic, verify_module, verify_module_or_panic,
};

#[macro_export]
macro_rules! debug_verify_module {
    ($module:expr) => {{
        if cfg!(debug_assertions) || cfg!(feature = "verify-ir") {
            let cfg = $crate::VerifierConfig::for_level($crate::VerificationLevel::Full);
            let report = $crate::verify_module($module, &cfg);
            if report.has_errors() {
                eprintln!("SONATINA_IR_VERIFY_FAILURE: module");
                eprintln!("{report}");
                panic!("SONATINA_IR_VERIFY_FAILURE");
            }
        }
    }};
}

#[macro_export]
macro_rules! debug_verify_func {
    ($ctx:expr, $func_ref:expr, $func:expr) => {{
        if cfg!(debug_assertions) || cfg!(feature = "verify-ir") {
            let cfg = $crate::VerifierConfig::for_level($crate::VerificationLevel::Full);
            let report = $crate::verify_function($ctx, $func_ref, $func, &cfg);
            if report.has_errors() {
                eprintln!(
                    "SONATINA_IR_VERIFY_FAILURE: function {}",
                    ($func_ref).as_u32()
                );
                eprintln!("{report}");
                panic!("SONATINA_IR_VERIFY_FAILURE");
            }
        }
    }};
}
