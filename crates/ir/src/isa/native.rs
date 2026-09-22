use std::sync::LazyLock;

use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

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
        assert!(
            matches!(
                (triple.architecture, triple.vendor, triple.operating_system),
                (
                    Architecture::X86_64 | Architecture::Aarch64,
                    Vendor::Unknown,
                    OperatingSystem::Native
                )
            ) || triple == TargetTriple::SP1
        );
        Self { triple }
    }
}

impl Isa for Native {
    type InstSet = NativeInstSet;

    fn triple(&self) -> TargetTriple {
        self.triple
    }

    fn type_layout(&self) -> &'static dyn TypeLayout {
        &NATIVE_TYPE_LAYOUT
    }

    fn address_spaces(&self) -> &'static dyn AddressSpaceInfo {
        static SPACES: NativeAddressSpaces = NativeAddressSpaces;
        &SPACES
    }

    fn inst_set(&self) -> &'static Self::InstSet {
        inst_set()
    }
}

struct NativeTypeLayout;

const NATIVE_TYPE_LAYOUT: NativeTypeLayout = NativeTypeLayout;

pub fn inst_set() -> &'static NativeInstSet {
    static INST_SET: LazyLock<NativeInstSet> = LazyLock::new(NativeInstSet::new);
    &INST_SET
}

impl TypeLayout for NativeTypeLayout {
    fn size_of(&self, ty: Type, ctx: &ModuleCtx) -> Result<usize, TypeLayoutError> {
        let size = match ty {
            Type::Unit => 0,
            Type::I1 | Type::I8 => 1,
            Type::I16 => 2,
            Type::I32 => 4,
            Type::I64 => 8,
            Type::I128 => 16,
            Type::I256 => 32,
            Type::EnumTag(_) => return Err(TypeLayoutError::UnrepresentableType(ty)),
            Type::Compound(compound) => {
                match ctx.with_ty_store(|store| store.resolve_compound(compound).clone()) {
                    CompoundType::Array { elem, len } => self.size_of(elem, ctx)? * len,
                    CompoundType::Struct(data) => {
                        if data.packed {
                            return Err(TypeLayoutError::UnsupportedType(ty));
                        }
                        let mut size = 0usize;
                        let mut struct_align = 1usize;
                        for field in data.fields {
                            let align = self.align_of(field, ctx)?;
                            size = size.next_multiple_of(align);
                            size += self.size_of(field, ctx)?;
                            struct_align = struct_align.max(align);
                        }
                        size.next_multiple_of(struct_align)
                    }
                    CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => 8,
                    CompoundType::Enum(_) | CompoundType::Func { .. } => {
                        return Err(TypeLayoutError::UnrepresentableType(ty));
                    }
                }
            }
        };
        Ok(size)
    }

    fn align_of(&self, ty: Type, ctx: &ModuleCtx) -> Result<usize, TypeLayoutError> {
        let align = match ty {
            Type::Unit | Type::I1 | Type::I8 => 1,
            Type::I16 => 2,
            Type::I32 => 4,
            Type::I64 => 8,
            Type::I128 => 16,
            Type::I256 => 16,
            Type::EnumTag(_) => return Err(TypeLayoutError::UnrepresentableType(ty)),
            Type::Compound(compound) => {
                match ctx.with_ty_store(|store| store.resolve_compound(compound).clone()) {
                    CompoundType::Array { elem, .. } => self.align_of(elem, ctx)?,
                    CompoundType::Struct(data) => {
                        if data.packed {
                            return Err(TypeLayoutError::UnsupportedType(ty));
                        }
                        let mut align = 1usize;
                        for field in data.fields {
                            align = align.max(self.align_of(field, ctx)?);
                        }
                        align
                    }
                    CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => 8,
                    CompoundType::Enum(_) | CompoundType::Func { .. } => {
                        return Err(TypeLayoutError::UnrepresentableType(ty));
                    }
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

#[cfg(test)]
mod tests {
    use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

    use super::Native;
    use crate::{
        Module, Type,
        isa::TypeLayoutError,
        types::{EnumReprHint, VariantData},
    };

    fn native_isa() -> Native {
        Native::new(TargetTriple::new(
            Architecture::Aarch64,
            Vendor::Unknown,
            OperatingSystem::Native,
        ))
    }

    #[test]
    fn native_layout_uses_64_bit_pointers_and_aligned_structs() {
        let module = Module::new(&native_isa());
        let pointer = module
            .ctx
            .with_ty_store_mut(|store| store.make_ptr(Type::I8));
        let structure = module
            .ctx
            .with_ty_store_mut(|store| store.make_struct("Aligned", &[Type::I8, Type::I64], false));
        let packed = module
            .ctx
            .with_ty_store_mut(|store| store.make_struct("Packed", &[Type::I8, Type::I64], true));

        assert_eq!(module.ctx.size_of_unchecked(pointer), 8);
        assert_eq!(module.ctx.align_of_unchecked(pointer), 8);
        assert_eq!(module.ctx.size_of_unchecked(Type::I256), 32);
        assert_eq!(module.ctx.align_of_unchecked(Type::I256), 16);
        assert_eq!(module.ctx.size_of_unchecked(structure), 16);
        assert_eq!(module.ctx.align_of_unchecked(structure), 8);
        for layout in [module.ctx.size_of(packed), module.ctx.align_of(packed)] {
            assert!(matches!(layout, Err(TypeLayoutError::UnsupportedType(ty)) if ty == packed));
        }
    }

    #[test]
    fn native_enum_layouts_remain_abstract_through_nested_aggregates() {
        let module = Module::new(&native_isa());
        let (enumeration, array, structure, references) = module.ctx.with_ty_store_mut(|store| {
            let enumeration = store.make_enum(
                "OptionI64",
                &[
                    VariantData {
                        name: "None".into(),
                        explicit_discriminant: None,
                        fields: vec![],
                    },
                    VariantData {
                        name: "Some".into(),
                        explicit_discriminant: None,
                        fields: vec![Type::I64],
                    },
                ],
                EnumReprHint::Default,
            );
            let array = store.make_array(enumeration, 2);
            let structure = store.make_struct("Options", &[Type::I8, array], false);
            let references = [
                store.make_ptr(enumeration),
                store.make_obj_ref(enumeration),
                store.make_const_ref(structure),
            ];
            (enumeration, array, structure, references)
        });
        for ty in [enumeration, array, structure] {
            for layout in [module.ctx.size_of(ty), module.ctx.align_of(ty)] {
                assert!(
                    matches!(layout, Err(TypeLayoutError::UnrepresentableType(inner)) if inner == enumeration),
                    "{ty:?}: {layout:?}"
                );
            }
        }
        for reference in references {
            assert_eq!(module.ctx.size_of(reference).unwrap(), 8);
            assert_eq!(module.ctx.align_of(reference).unwrap(), 8);
        }
    }

    #[test]
    fn native_function_types_are_abstract_not_unsupported() {
        let module = Module::new(&native_isa());
        let function = module
            .ctx
            .with_ty_store_mut(|store| store.make_func(&[Type::I64], &[Type::I64]));
        for layout in [module.ctx.size_of(function), module.ctx.align_of(function)] {
            assert!(
                matches!(layout, Err(TypeLayoutError::UnrepresentableType(ty)) if ty == function)
            );
        }
        let pointer = module
            .ctx
            .with_ty_store_mut(|store| store.make_ptr(function));
        assert_eq!(module.ctx.size_of(pointer).unwrap(), 8);
        assert_eq!(module.ctx.align_of(pointer).unwrap(), 8);
    }
}
