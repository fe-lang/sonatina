use std::sync::LazyLock;

use sonatina_triple::{Architecture, Chain, EvmVersion, TargetTriple, Version};

use super::{Isa, TypeLayout};
use crate::inst::evm::inst_set::EvmInstSet;

#[derive(Debug, Clone, Copy)]
pub struct Evm {
    version: Version,
}

impl Evm {
    pub fn new(version: EvmVersion) -> Self {
        Self {
            version: Version::Evm(version),
        }
    }
}

impl TypeLayout for Evm {
    fn pointer_size(&self) -> usize {
        256
    }
}

impl Isa for Evm {
    type InstSet = EvmInstSet;

    fn triple(&self) -> TargetTriple {
        TargetTriple::new(Architecture::Evm, Chain::Ethereum, self.version)
    }

    fn type_layout(&self) -> &'static dyn TypeLayout {
        const TL: EvmTypeLayout = EvmTypeLayout {};
        &TL
    }

    fn inst_set(&self) -> &'static Self::InstSet {
        static IS: LazyLock<EvmInstSet> = LazyLock::new(|| EvmInstSet::new());
        &*IS
    }
}

struct EvmTypeLayout {}
impl TypeLayout for EvmTypeLayout {
    fn pointer_size(&self) -> usize {
        256
    }
}
