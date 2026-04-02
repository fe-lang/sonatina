use sonatina_ir::{Module, module::FuncRef};

use crate::machinst::lower::SectionWorkModule;

use super::{EvmBackend, EvmPreparedSection};

pub fn prepare_root(
    module: &Module,
    backend: &EvmBackend,
    entry: FuncRef,
) -> Result<EvmPreparedSection, String> {
    backend.prepare_section(SectionWorkModule::from_roots(module, entry, &[], &[]))
}
