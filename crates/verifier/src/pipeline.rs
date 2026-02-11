use std::fmt;

use sonatina_ir::{Module, builder::ModuleBuilder};
use sonatina_parser::{Error as ParseError, ParsedModule, parse_module};

use crate::{VerificationReport, VerifierConfig, verify_module};

#[derive(Debug)]
pub enum ParseVerifyError {
    Parse(Vec<ParseError>),
    Verify(VerificationReport),
}

impl fmt::Display for ParseVerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(errors) => {
                write!(f, "parse failed with {} error(s)", errors.len())
            }
            Self::Verify(report) => write!(f, "verification failed: {report}"),
        }
    }
}

impl std::error::Error for ParseVerifyError {}

pub fn parse_and_verify_module(
    input: &str,
    cfg: &VerifierConfig,
) -> Result<ParsedModule, ParseVerifyError> {
    let parsed = parse_module(input).map_err(ParseVerifyError::Parse)?;
    let report = verify_module(&parsed.module, cfg);
    if report.has_errors() {
        return Err(ParseVerifyError::Verify(report));
    }
    Ok(parsed)
}

pub fn build_and_verify(
    builder: ModuleBuilder,
    cfg: &VerifierConfig,
) -> Result<Module, VerificationReport> {
    let module = builder.build();
    let report = verify_module(&module, cfg);
    if report.has_errors() {
        return Err(report);
    }
    Ok(module)
}

pub trait ModuleBuilderVerifyExt {
    fn build_verified(self, cfg: &VerifierConfig) -> Result<Module, VerificationReport>;
}

impl ModuleBuilderVerifyExt for ModuleBuilder {
    fn build_verified(self, cfg: &VerifierConfig) -> Result<Module, VerificationReport> {
        build_and_verify(self, cfg)
    }
}
