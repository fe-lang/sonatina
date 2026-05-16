use std::sync::LazyLock;

use sonatina_triple::{Architecture, TargetTriple};

use super::{Endian, Isa, TypeLayout, TypeLayoutError};
use crate::{
    AddressSpaceDesc, AddressSpaceId, AddressSpaceInfo, AddressSpaceKind, Type,
    inst::native::inst_set::NativeInstSet, module::ModuleCtx, types::CompoundType,
};

pub mod space {
    use crate::AddressSpaceId;

    pub const MEMORY: AddressSpaceId = AddressSpaceId::new(0);
}

static NATIVE_ADDRESS_SPACES: [AddressSpaceDesc; 1] = [AddressSpaceDesc {
    id: space::MEMORY,
    name: "memory",
    kind: AddressSpaceKind::Linear,
    immutable: false,
}];

struct NativeAddressSpaces;

impl AddressSpaceInfo for NativeAddressSpaces {
    fn default_space(&self) -> AddressSpaceId {
        space::MEMORY
    }

    fn desc(&self, id: AddressSpaceId) -> AddressSpaceDesc {
        NATIVE_ADDRESS_SPACES[id.as_u32() as usize]
    }

    fn all_spaces(&self) -> &'static [AddressSpaceDesc] {
        &NATIVE_ADDRESS_SPACES
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Native {
    triple: TargetTriple,
}

impl Native {
    pub fn new(triple: TargetTriple) -> Self {
        assert!(matches!(
            triple.architecture,
            Architecture::X86_64 | Architecture::Aarch64
        ));
        Self { triple }
    }
}

impl Isa for Native {
    type InstSet = NativeInstSet;

    fn triple(&self) -> TargetTriple {
        self.triple
    }

    fn type_layout(&self) -> &'static dyn TypeLayout {
        const TL: NativeTypeLayout = NativeTypeLayout {};
        &TL
    }

    fn address_spaces(&self) -> &'static dyn AddressSpaceInfo {
        static SPACES: NativeAddressSpaces = NativeAddressSpaces;
        &SPACES
    }

    fn inst_set(&self) -> &'static Self::InstSet {
        static IS: LazyLock<NativeInstSet> = LazyLock::new(NativeInstSet::new);
        &IS
    }
}

struct NativeTypeLayout {}

impl TypeLayout for NativeTypeLayout {
    fn size_of(&self, ty: Type, ctx: &ModuleCtx) -> Result<usize, TypeLayoutError> {
        let size = match ty {
            Type::Unit => 0,
            Type::I1 => 1,
            Type::I8 => 1,
            Type::I16 => 2,
            Type::I32 => 4,
            Type::I64 => 8,
            Type::I128 => 16,
            Type::I256 => 32,
            Type::EnumTag(_) => return Err(TypeLayoutError::UnrepresentableType(ty)),
            Type::Compound(cmpd) => {
                let cmpd = ctx.with_ty_store(|s| s.resolve_compound(cmpd).clone());
                match cmpd {
                    CompoundType::Array { elem, len } => {
                        let elem_size = self.size_of(elem, ctx)?;
                        elem_size * len
                    }
                    CompoundType::Struct(s) => {
                        let mut total = 0;
                        for &field in &s.fields {
                            let align = self.align_of(field, ctx)?;
                            total = (total + align - 1) & !(align - 1);
                            total += self.size_of(field, ctx)?;
                        }
                        let struct_align = s
                            .fields
                            .iter()
                            .map(|f| self.align_of(*f, ctx).unwrap_or(1))
                            .max()
                            .unwrap_or(1);
                        (total + struct_align - 1) & !(struct_align - 1)
                    }
                    CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => 8,
                    _ => return Err(TypeLayoutError::UnsupportedType(ty)),
                }
            }
        };
        Ok(size)
    }

    fn align_of(&self, ty: Type, ctx: &ModuleCtx) -> Result<usize, TypeLayoutError> {
        let align = match ty {
            Type::Unit => 1,
            Type::I1 | Type::I8 => 1,
            Type::I16 => 2,
            Type::I32 => 4,
            Type::I64 => 8,
            Type::I128 => 16,
            Type::I256 => 32,
            Type::EnumTag(_) => return Err(TypeLayoutError::UnrepresentableType(ty)),
            Type::Compound(cmpd) => {
                let cmpd = ctx.with_ty_store(|s| s.resolve_compound(cmpd).clone());
                match cmpd {
                    CompoundType::Array { elem, .. } => self.align_of(elem, ctx)?,
                    CompoundType::Struct(s) => s
                        .fields
                        .iter()
                        .map(|f| self.align_of(*f, ctx).unwrap_or(1))
                        .max()
                        .unwrap_or(1),
                    CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => 8,
                    _ => return Err(TypeLayoutError::UnsupportedType(ty)),
                }
            }
        };
        Ok(align)
    }

    fn pointer_repl(&self) -> Type {
        Type::I64
    }

    fn endian(&self) -> Endian {
        Endian::Le
    }
}
