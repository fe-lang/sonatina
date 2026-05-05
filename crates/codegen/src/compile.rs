//! High-level compilation entrypoint that bundles the optimization pipeline
//! and EVM codegen into a single API.
//!
//! Frontends typically only need [`EvmCompile`]: hand it a lowered [`Module`]
//! plus an [`OptLevel`], optionally inspect the optimized IR via
//! [`EvmCompile::optimize`], then produce object artifacts via
//! [`EvmCompile::compile`].

use sonatina_ir::{Module, isa::evm::Evm};
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

use crate::{
    isa::evm::{EvmBackend, LateCleanupProfile},
    object::{CompileOptions, ObjectArtifact, ObjectCompileError, compile_all_objects},
    optim::Pipeline,
};

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum OptLevel {
    #[default]
    O0,
    Os,
    O2,
}

pub struct EvmCompile {
    module: Module,
    opt_level: OptLevel,
    emit_observability: bool,
    optimized: bool,
}

impl EvmCompile {
    pub fn new(module: Module) -> Self {
        Self {
            module,
            opt_level: OptLevel::default(),
            emit_observability: false,
            optimized: false,
        }
    }

    pub fn with_opt_level(mut self, level: OptLevel) -> Self {
        self.opt_level = level;
        self
    }

    pub fn with_observability(mut self, on: bool) -> Self {
        self.emit_observability = on;
        self
    }

    /// Run the optimization pipeline (idempotent) and return a reference to
    /// the optimized module for inspection or IR dumping.
    pub fn optimize(&mut self) -> &Module {
        if !self.optimized {
            match self.opt_level {
                OptLevel::O0 => {}
                OptLevel::Os => Pipeline::size().run(&mut self.module),
                OptLevel::O2 => Pipeline::speed().run(&mut self.module),
            }
            self.optimized = true;
        }
        &self.module
    }

    /// Optimize (if not already) and compile every object in the module.
    pub fn compile(mut self) -> Result<Vec<ObjectArtifact>, Vec<ObjectCompileError>> {
        self.optimize();
        let backend = evm_backend_for_module(&self.module, self.opt_level)?;
        let opts = CompileOptions {
            emit_observability: self.emit_observability,
            ..CompileOptions::default()
        };
        compile_all_objects(&self.module, &backend, &opts)
    }
}

impl OptLevel {
    fn late_cleanup_profile(self) -> LateCleanupProfile {
        match self {
            OptLevel::O0 => LateCleanupProfile::Off,
            OptLevel::Os => LateCleanupProfile::Size,
            OptLevel::O2 => LateCleanupProfile::Speed,
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
        .with_late_cleanup_profile(opt_level.late_cleanup_profile()))
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
