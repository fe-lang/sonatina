#[path = "enum_concrete.rs"]
pub mod concrete;

use sonatina_parser::parse_module;
use sonatina_verifier::{Location, VerificationLevel, VerifierConfig, verify_module};

pub fn execute(source: &str, limit: usize) -> concrete::Execution {
    let run = concrete::execute(source, limit);
    if run.exhausted == 0 {
        let parsed = parse_module(source).expect("valid fixture syntax");
        for level in [VerificationLevel::Standard, VerificationLevel::Full] {
            let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
            for (&(func, inst), &readable) in &run.reads {
                let rejected = report.errors().any(|diagnostic| matches!(diagnostic.primary, Location::Inst { func: at_func, inst: at, .. } if at_func == func && at == inst));
                assert_eq!(
                    rejected, !readable,
                    "{level:?} read {inst:?}: {source}\n{report}\n{run:?}"
                );
            }
            assert_eq!(
                report.is_ok(),
                run.invalid_reads() == 0,
                "{level:?}: {source}\n{report}\n{run:?}"
            );
        }
    }
    run
}
