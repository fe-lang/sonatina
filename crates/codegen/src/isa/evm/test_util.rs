use sonatina_ir::{Module, isa::evm::Evm, module::FuncRef};
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

use crate::machinst::lower::SectionWorkModule;

use super::{EvmBackend, EvmPreparedSection};

/// The target triple the EVM tests all build against.
pub fn osaka_triple() -> TargetTriple {
    TargetTriple::new(
        Architecture::Evm,
        Vendor::Ethereum,
        OperatingSystem::Evm(EvmVersion::Osaka),
    )
}

/// An [`EvmBackend`] for [`osaka_triple`].
pub fn osaka_backend() -> EvmBackend {
    EvmBackend::new(Evm::new(osaka_triple()))
}

pub fn prepare_root(
    module: &Module,
    backend: &EvmBackend,
    entry: FuncRef,
) -> Result<EvmPreparedSection, String> {
    backend.prepare_section(SectionWorkModule::from_roots(module, entry, &[], &[]))
}
