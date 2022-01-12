use sonatina_triple::{Architecture, TargetTriple};

use crate::Type;

pub mod evm_eth;

pub struct IsaBuilder {
    triple: TargetTriple,
}

impl IsaBuilder {
    pub fn new(triple: TargetTriple) -> Self {
        Self { triple }
    }
    pub fn build(self) -> TargetIsa {
        match self.triple.architecture {
            Architecture::Evm => evm_eth::EvmEth::build_isa(self.triple),
        }
    }
}

#[derive(Debug)]
pub struct TargetIsa {
    triple: TargetTriple,
    type_provider: Box<dyn IsaSpecificTypeProvider>,
}

impl TargetIsa {
    pub fn type_provider(&self) -> &dyn IsaSpecificTypeProvider {
        self.type_provider.as_ref()
    }

    pub fn triple(&self) -> &TargetTriple {
        &self.triple
    }

    fn new(triple: TargetTriple, type_provider: Box<dyn IsaSpecificTypeProvider>) -> Self {
        Self {
            triple,
            type_provider,
        }
    }
}

pub trait IsaSpecificTypeProvider: std::fmt::Debug {
    fn pointer_type(&self) -> Type;
    fn address_type(&self) -> Type;
    fn balance_type(&self) -> Type;
    fn gas_type(&self) -> Type;
}
