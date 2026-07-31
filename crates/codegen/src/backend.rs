use sonatina_ir::Module;

use crate::compile::OptLevel;

/// Options shared by the optimization pipeline and target backend.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BackendOptions {
    pub opt_level: OptLevel,
}

/// A compilation backend that transforms optimized Sonatina IR into a
/// target-specific artifact.
pub trait Backend {
    type Artifact;
    type Error: std::fmt::Debug + Send;

    /// Compile a module after the shared optimization pipeline has run.
    ///
    /// Backend-specific legalization belongs here. `options` is the same
    /// configuration used by the shared optimizer, so frontend and backend
    /// optimization levels cannot silently diverge.
    fn compile_module(
        &self,
        module: &Module,
        options: &BackendOptions,
    ) -> Result<Self::Artifact, Vec<Self::Error>>;
}
