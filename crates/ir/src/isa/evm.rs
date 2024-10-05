use std::sync::LazyLock;

use sonatina_triple::{Architecture, Chain, EvmVersion, TargetTriple, Version};

use super::{Isa, TypeLayout};
use crate::{inst::evm::inst_set::EvmInstSet, types::CompoundTypeData, Type};

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
    fn size_of(&self, ty: crate::Type, ty_store: &crate::types::TypeStore) -> usize {
        match ty {
            Type::Compound(cmpd) => {
                let cmpd_data = ty_store.resolve_compound(cmpd);
                match cmpd_data {
                    CompoundTypeData::Array { elem, len } => {
                        // TODO: alignment!
                        self.size_of(*elem, ty_store) * len
                    }

                    CompoundTypeData::Ptr(_) => 32,

                    CompoundTypeData::Struct(s) => {
                        if s.packed {
                            panic!("packed data is not supported yet!");
                        }
                        s.fields
                            .iter()
                            .copied()
                            .fold(0, |acc, ty| acc + self.size_of(ty, ty_store))
                    }
                }
            }

            Type::Void => 0,

            _ => 32,
        }
    }
}
