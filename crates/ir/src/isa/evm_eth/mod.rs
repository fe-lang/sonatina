use crate::Type;

use super::{IsaSpecificTypeProvider, TargetIsa};

use sonatina_triple::{Architecture, Chain, EvmVersion, TargetTriple, Version};

#[derive(Debug, Clone, Copy)]
pub struct EvmEth {
    #[allow(unused)]
    version: EvmVersion,
}

impl EvmEth {
    pub(super) fn build_isa(triple: TargetTriple) -> TargetIsa {
        debug_assert_eq!(triple.architecture, Architecture::Evm);
        debug_assert_eq!(triple.chain, Chain::Ethereum);
        let type_provider = match triple.version {
            Version::EvmVersion(version) => Self { version },
        };

        TargetIsa::new(triple, Box::new(type_provider))
    }
}

impl IsaSpecificTypeProvider for EvmEth {
    fn pointer_type(&self) -> Type {
        Type::I256
    }

    fn address_type(&self) -> Type {
        todo!()
    }

    fn balance_type(&self) -> Type {
        Type::I256
    }

    fn gas_type(&self) -> Type {
        Type::I256
    }
}
