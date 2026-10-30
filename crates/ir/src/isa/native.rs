use std::sync::LazyLock;

use sonatina_triple::{Architecture, OperatingSystem, TargetTriple, Vendor};

use super::{Endian, EnumLayout, Isa, PartLayout, TypeLayout, TypeLayoutError, place_fields};
use crate::{
    AddressSpaceDesc, AddressSpaceId, AddressSpaceInfo, AddressSpaceKind, Type,
    inst::native::inst_set::NativeInstSet,
    types::{CompoundType, EnumData, TypeStore},
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

impl NativeTypeLayout {
    fn size(ty: Type, store: &TypeStore) -> Result<usize, TypeLayoutError> {
        let Type::Compound(compound) = ty else {
            return Self::scalar_layout(Self::tag_repr(ty, store)?).map(|(size, _)| size);
        };
        let size = match store.resolve_compound(compound) {
            CompoundType::Array { elem, len } => Self::size(*elem, store)? * len,
            CompoundType::Struct(data) => {
                if data.packed {
                    return Err(TypeLayoutError::UnsupportedType(ty));
                }
                let mut size = 0usize;
                let mut struct_align = 1usize;
                for &field in &data.fields {
                    let align = Self::align(field, store)?;
                    size = size.next_multiple_of(align);
                    size += Self::size(field, store)?;
                    struct_align = struct_align.max(align);
                }
                size.next_multiple_of(struct_align)
            }
            CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => 8,
            CompoundType::Enum(data) => Self::enum_layout(data, store)?.size,
            CompoundType::Func { .. } => {
                return Err(TypeLayoutError::UnrepresentableType(ty));
            }
        };
        Ok(size)
    }

    fn align(ty: Type, store: &TypeStore) -> Result<usize, TypeLayoutError> {
        let Type::Compound(compound) = ty else {
            return Self::scalar_layout(Self::tag_repr(ty, store)?).map(|(_, align)| align);
        };
        let align = match store.resolve_compound(compound) {
            CompoundType::Array { elem, .. } => Self::align(*elem, store)?,
            CompoundType::Struct(data) => {
                if data.packed {
                    return Err(TypeLayoutError::UnsupportedType(ty));
                }
                let mut align = 1usize;
                for &field in &data.fields {
                    align = align.max(Self::align(field, store)?);
                }
                align
            }
            CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_) => 8,
            CompoundType::Enum(data) => Self::enum_layout(data, store)?.align,
            CompoundType::Func { .. } => {
                return Err(TypeLayoutError::UnrepresentableType(ty));
            }
        };
        Ok(align)
    }

    fn enum_layout(data: &EnumData, store: &TypeStore) -> Result<EnumLayout, TypeLayoutError> {
        let (tag, variants) = Self::enum_part_layouts(data, store)?;
        Ok(EnumLayout::new(tag, &variants))
    }

    /// The layouts of an enum's tag and of each variant's fields.
    fn enum_part_layouts(
        data: &EnumData,
        store: &TypeStore,
    ) -> Result<(PartLayout, Vec<Vec<PartLayout>>), TypeLayoutError> {
        let layout = |ty| Ok((Self::size(ty, store)?, Self::align(ty, store)?));
        let variants = data
            .variants
            .iter()
            .map(|variant| variant.fields.iter().map(|&field| layout(field)).collect())
            .collect::<Result<_, _>>()?;
        Ok((layout(data.tag_ty())?, variants))
    }

    /// An enum tag's integer type; any other scalar is its own.
    fn tag_repr(ty: Type, store: &TypeStore) -> Result<Type, TypeLayoutError> {
        let Type::EnumTag(enum_ty) = ty else {
            return Ok(ty);
        };
        store
            .enum_data(enum_ty)
            .map(EnumData::tag_ty)
            .ok_or(TypeLayoutError::UnrepresentableType(ty))
    }

    fn scalar_layout(ty: Type) -> Result<(usize, usize), TypeLayoutError> {
        Ok(match ty {
            Type::Unit => (0, 1),
            Type::I1 | Type::I8 => (1, 1),
            Type::I16 => (2, 2),
            Type::I32 => (4, 4),
            Type::I64 => (8, 8),
            Type::I128 => (16, 16),
            Type::I256 => (32, 16),
            Type::EnumTag(_) | Type::Compound(_) => {
                unreachable!("tag and compound layouts need their type store")
            }
        })
    }
}

impl TypeLayout for NativeTypeLayout {
    fn size_of(&self, ty: Type, store: &TypeStore) -> Result<usize, TypeLayoutError> {
        Self::size(ty, store)
    }

    fn align_of(&self, ty: Type, store: &TypeStore) -> Result<usize, TypeLayoutError> {
        Self::align(ty, store)
    }

    fn enum_variant_field_offset(
        &self,
        data: &EnumData,
        variant: usize,
        field: usize,
        store: &TypeStore,
    ) -> Option<usize> {
        let (tag, variants) = Self::enum_part_layouts(data, store).ok()?;
        let payload_offset = EnumLayout::new(tag, &variants).payload_offset;
        let (offsets, _) = place_fields(variants.get(variant)?);
        Some(payload_offset + offsets.get(field)?)
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
    fn enum_variants_share_an_aligned_payload() {
        let module = Module::new(&native_isa());
        let variant = |name: &str, fields: &[Type]| VariantData {
            name: name.to_string(),
            explicit_discriminant: None,
            fields: fields.to_vec(),
        };
        let [choice, option] = [
            vec![
                variant("None", &[]),
                variant("Some", &[Type::I256]),
                variant("Pair", &[Type::I8, Type::I64]),
            ],
            vec![variant("None", &[]), variant("Some", &[Type::I64])],
        ]
        .map(|variants| {
            module.ctx.with_ty_store_mut(|store| {
                store.make_enum(
                    &format!("E{}", variants.len()),
                    &variants,
                    EnumReprHint::Default,
                )
            })
        });
        // An i8 tag, then every payload from the i256's 16-byte alignment.
        assert_eq!(module.ctx.size_of_unchecked(choice), 48);
        assert_eq!(module.ctx.align_of_unchecked(choice), 16);
        let offset = |ty, variant, field| module.ctx.enum_variant_field_offset(ty, variant, field);
        assert_eq!(offset(choice, 1, 0), Some((16, Type::I256)));
        assert_eq!(offset(choice, 2, 0), Some((16, Type::I8)));
        assert_eq!(offset(choice, 2, 1), Some((24, Type::I64)));
        assert_eq!(offset(choice, 0, 0), None);
        // A two-variant enum's i1 tag pads to its payload's alignment.
        assert_eq!(module.ctx.size_of_unchecked(option), 16);
        assert_eq!(offset(option, 1, 0), Some((8, Type::I64)));
        let Type::Compound(option) = option else {
            unreachable!()
        };
        assert_eq!(module.ctx.size_of_unchecked(Type::EnumTag(option)), 1);
    }

    #[test]
    fn native_enum_layouts_nest_in_aggregates() {
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
        for (ty, size) in [(enumeration, 16), (array, 32), (structure, 40)] {
            assert_eq!(module.ctx.size_of(ty).unwrap(), size, "{ty:?}");
            assert_eq!(module.ctx.align_of(ty).unwrap(), 8, "{ty:?}");
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
