pub mod artifact;
pub mod compile;
pub mod data;
pub mod error;
pub mod link;
pub mod lowering;
pub mod resolve;

use crate::isa::evm::PushWidthPolicy;
pub use artifact::{
    MachineInstId, OBSERVABILITY_SCHEMA_VERSION, ObjectArtifact, ObjectObservability,
    PcAttribution, PcMapEntry, PcMapUnit, SectionArtifact, SectionObservability, SymbolDef,
    SymbolId, UnmappedReason, UnmappedReasonCoverage,
};
pub use compile::{compile_all_objects, compile_object};
pub use data::encode_gv_initializer_to_bytes;
pub use error::ObjectCompileError;
pub use resolve::{
    ObjectId, ResolvedEmbed, ResolvedObject, ResolvedProgram, ResolvedSection, SectionId,
};
use sonatina_verifier::{VerificationLevel, VerifierConfig};

#[derive(Debug, Clone)]
pub struct CompileOptions {
    pub fixup_policy: PushWidthPolicy,
    pub emit_symtab: bool,
    pub emit_observability: bool,
    /// Keep each section's `SectionLowering`. The backend must record what it
    /// is built from (`EvmBackend::with_lowering_record`).
    pub emit_lowering: bool,
    pub verifier_cfg: VerifierConfig,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            fixup_policy: PushWidthPolicy::default(),
            emit_symtab: false,
            emit_observability: false,
            emit_lowering: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        }
    }
}
