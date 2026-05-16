use sonatina_ir::Module;

/// A compilation backend that transforms optimized Sonatina IR into
/// target-specific artifacts.
///
/// Each backend carries its own configuration (optimization profiles,
/// emission options, etc.) set at construction time.
///
/// The module passed to [`Backend::compile_module`] has already been through
/// the shared optimization pipeline. Backend-specific IR transformations
/// (e.g., EVM memory legalization, aggregate ABI lowering) should happen
/// inside `compile_module`.
pub trait Backend {
    /// The artifact type produced by compilation (e.g., EVM bytecode
    /// artifacts, native code blobs, WASM modules).
    type Artifact;

    /// Backend-specific error type.
    type Error: std::fmt::Debug + Send;

    /// Compile an optimized module into target-specific artifacts.
    fn compile_module(&self, module: &Module) -> Result<Self::Artifact, Vec<Self::Error>>;
}
