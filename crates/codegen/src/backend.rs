use sonatina_ir::Module;

use crate::{compile::OptLevel, optim::Pipeline};

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

    /// The optimization pipeline for `options`, tuned to this backend's
    /// target.
    fn pipeline(&self, options: &BackendOptions) -> Pipeline;

    /// Compile a module after the pipeline from [`Backend::pipeline`] has run.
    ///
    /// Backend-specific legalization belongs here. `options` is the same
    /// configuration that chose the optimization pipeline, so optimizer and
    /// backend optimization levels cannot silently diverge.
    fn compile_module(
        &self,
        module: &Module,
        options: &BackendOptions,
    ) -> Result<Self::Artifact, Vec<Self::Error>>;
}
