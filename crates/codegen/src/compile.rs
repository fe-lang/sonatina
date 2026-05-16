//! High-level compilation entrypoint that bundles the optimization pipeline
//! and backend codegen into a single API.
//!
//! [`Compile`] is the generic entry point: pair any [`Backend`] with a
//! [`Module`] and an [`OptLevel`], optionally inspect the optimized IR,
//! then produce artifacts.
//!
//! [`EvmCompile`] is a convenience wrapper that constructs an EVM backend
//! from the module's target triple.

use sonatina_ir::Module;

use crate::{backend::Backend, optim::Pipeline};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum OptLevel {
    #[default]
    O0,
    O1,
    Os,
    O2,
}

/// Generic compilation pipeline: shared optimization + backend-specific codegen.
pub struct Compile<B> {
    module: Module,
    opt_level: OptLevel,
    backend: B,
    optimized: bool,
}

impl<B> Compile<B> {
    pub fn new(module: Module, backend: B) -> Self {
        Self {
            module,
            opt_level: OptLevel::default(),
            backend,
            optimized: false,
        }
    }

    pub fn with_opt_level(mut self, level: OptLevel) -> Self {
        self.opt_level = level;
        self
    }

    /// Run the optimization pipeline (idempotent) and return a reference to
    /// the optimized module for inspection or IR dumping.
    pub fn optimize(&mut self) -> &Module {
        if !self.optimized {
            match self.opt_level {
                OptLevel::O0 => {}
                OptLevel::O1 => Pipeline::speed().run(&mut self.module),
                OptLevel::Os => Pipeline::size().run(&mut self.module),
                OptLevel::O2 => Pipeline::speed().run(&mut self.module),
            }
            self.optimized = true;
        }
        &self.module
    }

    pub fn opt_level(&self) -> OptLevel {
        self.opt_level
    }

    pub fn module(&self) -> &Module {
        &self.module
    }

    pub fn backend(&self) -> &B {
        &self.backend
    }
}

impl<B: Backend> Compile<B> {
    /// Optimize (if not already) and compile via the backend.
    pub fn compile(mut self) -> Result<B::Artifact, Vec<B::Error>> {
        self.optimize();
        self.backend.compile_module(&self.module)
    }
}

// ---------------------------------------------------------------------------
// EVM convenience wrapper
// ---------------------------------------------------------------------------

use sonatina_ir::isa::evm::Evm;
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

use crate::{
    isa::evm::{EvmBackend, ImmediateMaterializationMode, LateCleanupProfile},
    object::{CompileOptions, ObjectArtifact, ObjectCompileError, compile_all_objects},
    stackalloc::StackifySearchProfile,
};

/// EVM-specific backend wrapper that implements [`Backend`].
pub struct EvmCompiler {
    evm_backend: EvmBackend,
    compile_options: CompileOptions,
}

impl EvmCompiler {
    pub fn from_module(
        module: &Module,
        opt_level: OptLevel,
    ) -> Result<Self, Vec<ObjectCompileError>> {
        let backend = evm_backend_for_module(module, opt_level)?;
        Ok(Self {
            evm_backend: backend,
            compile_options: CompileOptions::default(),
        })
    }

    pub fn with_observability(mut self, on: bool) -> Self {
        self.compile_options.emit_observability = on;
        self
    }

    pub fn evm_backend(&self) -> &EvmBackend {
        &self.evm_backend
    }
}

impl Backend for EvmCompiler {
    type Artifact = Vec<ObjectArtifact>;
    type Error = ObjectCompileError;

    fn compile_module(&self, module: &Module) -> Result<Self::Artifact, Vec<Self::Error>> {
        compile_all_objects(module, &self.evm_backend, &self.compile_options)
    }
}

/// Convenience type for EVM compilation, preserving the existing API.
pub struct EvmCompile {
    inner: Compile<EvmCompiler>,
    emit_observability: bool,
}

impl EvmCompile {
    pub fn new(module: Module) -> Self {
        Self {
            inner: Compile {
                module,
                opt_level: OptLevel::default(),
                backend: EvmCompiler {
                    evm_backend: EvmBackend::new(Evm::new(evm_osaka_triple())),
                    compile_options: CompileOptions::default(),
                },
                optimized: false,
            },
            emit_observability: false,
        }
    }

    pub fn with_opt_level(mut self, level: OptLevel) -> Self {
        self.inner.opt_level = level;
        self
    }

    pub fn with_observability(mut self, on: bool) -> Self {
        self.emit_observability = on;
        self
    }

    /// Run the optimization pipeline (idempotent) and return a reference to
    /// the optimized module for inspection or IR dumping.
    pub fn optimize(&mut self) -> &Module {
        self.inner.optimize()
    }

    /// Optimize (if not already) and compile every object in the module.
    pub fn compile(mut self) -> Result<Vec<ObjectArtifact>, Vec<ObjectCompileError>> {
        self.inner.optimize();
        let backend = evm_backend_for_module(&self.inner.module, self.inner.opt_level)?;
        let opts = CompileOptions {
            emit_observability: self.emit_observability,
            ..CompileOptions::default()
        };
        compile_all_objects(&self.inner.module, &backend, &opts)
    }
}

impl OptLevel {
    pub(crate) fn late_cleanup_profile(self) -> LateCleanupProfile {
        match self {
            OptLevel::O0 => LateCleanupProfile::Off,
            OptLevel::O1 => LateCleanupProfile::Speed,
            OptLevel::Os => LateCleanupProfile::Size,
            OptLevel::O2 => LateCleanupProfile::Speed,
        }
    }

    pub(crate) fn stackify_search_profile(self) -> StackifySearchProfile {
        match self {
            OptLevel::O0 => StackifySearchProfile::Fast,
            OptLevel::O1 => StackifySearchProfile::GreedyWide,
            OptLevel::Os | OptLevel::O2 => StackifySearchProfile::Exact,
        }
    }

    pub(crate) fn immediate_materialization_mode(self) -> ImmediateMaterializationMode {
        match self {
            OptLevel::Os => ImmediateMaterializationMode::Size,
            OptLevel::O2 => ImmediateMaterializationMode::Balanced,
            OptLevel::O0 | OptLevel::O1 => ImmediateMaterializationMode::Gas,
        }
    }
}

fn evm_backend_for_module(
    module: &Module,
    opt_level: OptLevel,
) -> Result<EvmBackend, Vec<ObjectCompileError>> {
    let target = module.ctx.triple;
    if target != evm_osaka_triple() {
        return Err(vec![ObjectCompileError::UnsupportedTarget {
            target,
            message: "EVM codegen currently requires evm-ethereum-osaka".to_string(),
        }]);
    }

    Ok(EvmBackend::new(Evm::new(target))
        .with_late_cleanup_profile(opt_level.late_cleanup_profile())
        .with_stackify_search_profile(opt_level.stackify_search_profile())
        .with_immediate_materialization_mode(opt_level.immediate_materialization_mode()))
}

fn evm_osaka_triple() -> TargetTriple {
    TargetTriple::new(
        Architecture::Evm,
        Vendor::Ethereum,
        OperatingSystem::Evm(EvmVersion::Osaka),
    )
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{Module, isa::evm::Evm};
    use sonatina_triple::{EvmVersion, OperatingSystem, TargetTriple};

    use super::{EvmCompile, ObjectCompileError, evm_osaka_triple};

    fn module_for_evm(version: EvmVersion) -> Module {
        let triple = evm_osaka_triple();
        Module::new(&Evm::new(TargetTriple {
            operating_system: OperatingSystem::Evm(version),
            ..triple
        }))
    }

    #[test]
    fn compile_uses_module_target() {
        let errors = EvmCompile::new(module_for_evm(EvmVersion::London))
            .compile()
            .expect_err("London modules should not be compiled as Osaka");
        let [ObjectCompileError::UnsupportedTarget { target, .. }] = errors.as_slice() else {
            panic!("expected unsupported target error, got {errors:?}");
        };
        assert_eq!(
            target.operating_system,
            OperatingSystem::Evm(EvmVersion::London)
        );
    }
}
