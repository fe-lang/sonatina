pub mod artifact;
pub mod compile;
pub mod data;
pub mod error;
pub mod link;
pub mod resolve;

pub use artifact::{
    OBSERVABILITY_SCHEMA_VERSION, ObjectArtifact, ObjectObservability, PcMapEntry, SectionArtifact,
    SectionObservability, SymbolDef, SymbolId, UnmappedReason, UnmappedReasonCoverage,
};
pub use compile::{compile_all_objects, compile_object};
pub use data::encode_gv_initializer_to_bytes;
pub use error::ObjectCompileError;
pub use resolve::{
    ObjectId, ResolvedEmbed, ResolvedObject, ResolvedProgram, ResolvedSection, SectionId,
};
use sonatina_verifier::{VerificationLevel, VerifierConfig};

#[derive(Debug, Clone)]
pub struct CompileOptions<P> {
    pub fixup_policy: P,
    pub emit_symtab: bool,
    pub emit_observability: bool,
    pub verifier_cfg: VerifierConfig,
}

impl<P: Default> Default for CompileOptions<P> {
    fn default() -> Self {
        Self {
            fixup_policy: P::default(),
            emit_symtab: true,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        }
    }
}
