//! Dedicated SP1 execution/proof suite; the compiler workspace does not depend
//! on the prover SDK. Tests require SONATINA_SP1_TOOLCHAIN and never skip missing
//! prerequisites. Run the ignored core-proof test explicitly.

use std::sync::OnceLock;

use sonatina_codegen::{Compile, compile::OptLevel, isa::cranelift::CraneliftObjectBackend};
use sonatina_sp1::{Sp1Runtime, Sp1Toolchain};
use sonatina_triple::TargetTriple;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};
use sp1_sdk::Elf;

pub fn runtime() -> &'static Sp1Runtime {
    static RUNTIME: OnceLock<Sp1Runtime> = OnceLock::new();
    RUNTIME.get_or_init(|| Sp1Runtime::build(Sp1Toolchain::from_env().unwrap()).unwrap())
}

pub fn compile(source: &str, level: OptLevel) -> Vec<u8> {
    let source = format!("target = \"{}\"\n{source}", TargetTriple::SP1);
    let module = sonatina_parser::parse_module(&source).unwrap().module;
    let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
    assert!(!report.has_errors(), "{report}");
    Compile::new(module, CraneliftObjectBackend::new())
        .with_opt_level(level)
        .compile()
        .unwrap()
        .as_bytes()
        .to_vec()
}

pub fn link(source: &str, level: OptLevel) -> Elf {
    runtime()
        .link_objects(&[&compile(source, level)])
        .unwrap()
        .into()
}
