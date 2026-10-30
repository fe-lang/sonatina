use std::sync::LazyLock;

use sonatina_triple::{Architecture, TargetTriple};

use super::{Endian, Isa, TypeLayout, TypeLayoutError};
use crate::{
    AddressSpaceDesc, AddressSpaceId, AddressSpaceInfo, AddressSpaceKind, Type,
    inst::evm::{inst_set::EvmInstSet, machine_inst_set::EvmMachineInstSet},
    types::{CompoundType, EnumData, TypeStore},
};

pub mod space {
    use crate::AddressSpaceId;

    pub const MEMORY: AddressSpaceId = AddressSpaceId::new(0);
    pub const STORAGE: AddressSpaceId = AddressSpaceId::new(1);
    pub const TRANSIENT: AddressSpaceId = AddressSpaceId::new(2);
    pub const CALLDATA: AddressSpaceId = AddressSpaceId::new(3);
    pub const RETURNDATA: AddressSpaceId = AddressSpaceId::new(4);
    pub const CODE: AddressSpaceId = AddressSpaceId::new(5);
}

static EVM_ADDRESS_SPACES: [AddressSpaceDesc; 6] = [
    AddressSpaceDesc {
        id: space::MEMORY,
        name: "memory",
        kind: AddressSpaceKind::Linear,
        immutable: false,
    },
    AddressSpaceDesc {
        id: space::STORAGE,
        name: "storage",
        kind: AddressSpaceKind::Keyed,
        immutable: false,
    },
    AddressSpaceDesc {
        id: space::TRANSIENT,
        name: "transient",
        kind: AddressSpaceKind::Keyed,
        immutable: false,
    },
    AddressSpaceDesc {
        id: space::CALLDATA,
        name: "calldata",
        kind: AddressSpaceKind::Linear,
        immutable: true,
    },
    AddressSpaceDesc {
        id: space::RETURNDATA,
        name: "returndata",
        kind: AddressSpaceKind::Linear,
        immutable: false,
    },
    AddressSpaceDesc {
        id: space::CODE,
        name: "code",
        kind: AddressSpaceKind::Linear,
        immutable: true,
    },
];

struct EvmAddressSpaces;

impl AddressSpaceInfo for EvmAddressSpaces {
    fn default_space(&self) -> AddressSpaceId {
        space::MEMORY
    }

    fn desc(&self, id: AddressSpaceId) -> AddressSpaceDesc {
        EVM_ADDRESS_SPACES[id.as_u32() as usize]
    }

    fn all_spaces(&self) -> &'static [AddressSpaceDesc] {
        &EVM_ADDRESS_SPACES
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Evm {
    triple: TargetTriple,
}

impl Evm {
    pub fn new(triple: TargetTriple) -> Self {
        assert!(matches!(triple.architecture, Architecture::Evm));
        Self { triple }
    }
}

impl Isa for Evm {
    type InstSet = EvmInstSet;

    fn triple(&self) -> TargetTriple {
        self.triple
    }

    fn type_layout(&self) -> &'static dyn TypeLayout {
        const TL: EvmTypeLayout = EvmTypeLayout {};
        &TL
    }

    fn address_spaces(&self) -> &'static dyn AddressSpaceInfo {
        static SPACES: EvmAddressSpaces = EvmAddressSpaces;
        &SPACES
    }

    fn inst_set(&self) -> &'static Self::InstSet {
        static IS: LazyLock<EvmInstSet> = LazyLock::new(EvmInstSet::new);
        &IS
    }
}

#[derive(Debug, Clone, Copy)]
pub struct EvmMachine {
    triple: TargetTriple,
}

impl EvmMachine {
    pub fn new(triple: TargetTriple) -> Self {
        assert!(matches!(triple.architecture, Architecture::Evm));
        Self { triple }
    }
}

impl Isa for EvmMachine {
    type InstSet = EvmMachineInstSet;

    fn triple(&self) -> TargetTriple {
        self.triple
    }

    fn type_layout(&self) -> &'static dyn TypeLayout {
        const TL: EvmTypeLayout = EvmTypeLayout {};
        &TL
    }

    fn address_spaces(&self) -> &'static dyn AddressSpaceInfo {
        static SPACES: EvmAddressSpaces = EvmAddressSpaces;
        &SPACES
    }

    fn inst_set(&self) -> &'static Self::InstSet {
        static IS: LazyLock<EvmMachineInstSet> = LazyLock::new(EvmMachineInstSet::new);
        &IS
    }
}

struct EvmTypeLayout {}
impl TypeLayout for EvmTypeLayout {
    fn size_of(&self, ty: crate::Type, store: &TypeStore) -> Result<usize, TypeLayoutError> {
        let size = match ty {
            Type::Unit => 0,
            // EVM memory is word-addressed by the MLOAD/MSTORE family. For now we model all
            // scalar/pointer values as occupying one full 32-byte slot.
            Type::I1
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::I256
            | Type::EnumTag(_) => 32,

            Type::Compound(cmpd) => match store.resolve_compound(cmpd) {
                CompoundType::Array { elem, len } => self.size_of(*elem, store)? * len,

                CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => 32,

                CompoundType::Struct(s) => {
                    if s.packed {
                        panic!("packed data is not supported yet!");
                    }
                    let mut size = 0;
                    for &field in &s.fields {
                        size += self.size_of(field, store)?;
                    }

                    size
                }

                CompoundType::Enum(data) => {
                    let mut size = 32;
                    for variant in &data.variants {
                        for &field in &variant.fields {
                            size += self.size_of(field, store)?;
                        }
                    }
                    size
                }

                CompoundType::Func { .. } => {
                    return Err(TypeLayoutError::UnrepresentableType(ty));
                }
            },
        };

        Ok(size)
    }

    /// The tag's word, then every variant's fields in turn.
    fn enum_variant_field_offset(
        &self,
        data: &EnumData,
        variant: usize,
        field: usize,
        store: &TypeStore,
    ) -> Option<usize> {
        data.variants.get(variant)?.fields.get(field)?;
        data.variants[..variant]
            .iter()
            .flat_map(|variant| &variant.fields)
            .chain(&data.variants[variant].fields[..field])
            .try_fold(32, |offset, &ty| {
                Some(offset + self.size_of(ty, store).ok()?)
            })
    }

    fn pointer_repl(&self) -> Type {
        Type::I256
    }

    fn align_of(&self, ty: Type, store: &TypeStore) -> Result<usize, TypeLayoutError> {
        let size = self.size_of(ty, store)?;
        if size == 0 { Ok(1) } else { Ok(32) }
    }

    fn endian(&self) -> Endian {
        Endian::Be
    }
}

#[cfg(test)]
mod tests {
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use super::{Evm, EvmMachine, space};
    use crate::{AddressSpaceKind, inst::inst_set::InstSetBase, isa::Isa};

    #[test]
    fn evm_address_spaces_match_expected_layout() {
        let isa = Evm::new(TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        ));

        let spaces = isa.address_spaces();
        let all = spaces.all_spaces();
        assert_eq!(all.len(), 6);
        assert_eq!(spaces.default_space(), space::MEMORY);
        assert_eq!(spaces.desc(space::MEMORY).kind, AddressSpaceKind::Linear);
        assert_eq!(spaces.desc(space::STORAGE).kind, AddressSpaceKind::Keyed);
        assert!(spaces.desc(space::CALLDATA).immutable);
        assert!(spaces.desc(space::CODE).immutable);
        assert!(!spaces.desc(space::RETURNDATA).immutable);
    }

    #[test]
    fn evm_machine_reuses_evm_layout_and_has_machine_memory_ops() {
        let triple = TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        );
        let isa = EvmMachine::new(triple);

        assert_eq!(isa.type_layout().pointer_repl(), crate::Type::I256);
        assert_eq!(isa.address_spaces().default_space(), space::MEMORY);
        assert!(isa.inst_set().has_evm_mload().is_some());
        assert!(isa.inst_set().has_evm_mstore().is_some());
        assert!(isa.inst_set().has_evm_malloc().is_none());
        assert!(isa.inst_set().has_alloca().is_none());
    }
}
