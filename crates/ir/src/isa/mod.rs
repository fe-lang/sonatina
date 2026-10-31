use sonatina_triple::TargetTriple;

use crate::{
    AddressSpaceInfo, InstSetBase, Type,
    types::{EnumData, TypeStore},
};

pub mod evm;
pub mod native;

pub trait Isa {
    type InstSet: InstSetBase + 'static;

    fn triple(&self) -> TargetTriple;
    fn inst_set(&self) -> &'static Self::InstSet;
    fn type_layout(&self) -> &'static dyn TypeLayout;
    fn address_spaces(&self) -> &'static dyn AddressSpaceInfo;
}

/// Lays out types; compound types resolve through `store`.
pub trait TypeLayout: Send + Sync {
    /// The size and alignment of `ty` in bytes, from one walk of its parts.
    fn size_align_of(&self, ty: Type, store: &TypeStore)
    -> Result<(usize, usize), TypeLayoutError>;
    /// The offset of field `field` of variant `variant` in an enum `data`.
    fn enum_variant_field_offset(
        &self,
        data: &EnumData,
        variant: usize,
        field: usize,
        store: &TypeStore,
    ) -> Option<usize> {
        let (tag, variants) = enum_part_layouts(self, data, store).ok()?;
        let payload_offset = EnumLayout::new(tag, &variants).payload_offset;
        let (offsets, _) = place_fields(variants.get(variant)?);
        Some(payload_offset + offsets.get(field)?)
    }
    fn pointer_repl(&self) -> Type;
    fn endian(&self) -> Endian;
}

/// A part's size and alignment in bytes.
type PartLayout = (usize, usize);

/// The layout of an enum `data` under `layout`.
pub(crate) fn enum_layout(
    layout: &(impl TypeLayout + ?Sized),
    data: &EnumData,
    store: &TypeStore,
) -> Result<EnumLayout, TypeLayoutError> {
    let (tag, variants) = enum_part_layouts(layout, data, store)?;
    Ok(EnumLayout::new(tag, &variants))
}

/// The layouts of an enum's tag and of each variant's fields.
fn enum_part_layouts(
    layout: &(impl TypeLayout + ?Sized),
    data: &EnumData,
    store: &TypeStore,
) -> Result<(PartLayout, Vec<Vec<PartLayout>>), TypeLayoutError> {
    let part = |ty| layout.size_align_of(ty, store);
    let variants = data
        .variants
        .iter()
        .map(|variant| variant.fields.iter().map(|&field| part(field)).collect())
        .collect::<Result<_, _>>()?;
    Ok((part(data.tag_ty())?, variants))
}

/// Where an enum's parts go when its variants share payload storage: the tag
/// at offset zero, then each variant's fields placed like a struct's, from one
/// payload offset aligned for every field of every variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct EnumLayout {
    pub payload_offset: usize,
    pub size: usize,
    pub align: usize,
}

impl EnumLayout {
    /// The layout for a tag and variant fields.
    fn new(tag: PartLayout, variants: &[Vec<PartLayout>]) -> Self {
        let payload_align = variants
            .iter()
            .flatten()
            .map(|&(_, align)| align)
            .fold(1, usize::max);
        let payload_offset = tag.0.next_multiple_of(payload_align);
        let extent = variants
            .iter()
            .map(|fields| place_fields(fields).1)
            .max()
            .unwrap_or(0);
        let align = tag.1.max(payload_align);
        Self {
            payload_offset,
            size: (payload_offset + extent).next_multiple_of(align),
            align,
        }
    }
}

/// The offsets of `fields` placed like a struct's fields, and the end of the
/// last.
fn place_fields(fields: &[PartLayout]) -> (Vec<usize>, usize) {
    let mut end = 0usize;
    let offsets = fields
        .iter()
        .map(|&(size, align)| {
            let offset = end.next_multiple_of(align);
            end = offset + size;
            offset
        })
        .collect();
    (offsets, end)
}

#[derive(Debug, Clone)]
pub enum TypeLayoutError {
    /// The type is unsupported by the ISA.
    UnsupportedType(Type),

    /// An error indicating that the given type cannot be represented in memory.
    ///
    /// This error occurs when attempting to compute the size or alignment of a
    /// type that is abstract or has no concrete representation in memory.
    /// For example, function types or unresolved abstract types cannot be
    /// laid out in memory.
    UnrepresentableType(Type),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Endian {
    Be,
    Le,
}

#[cfg(test)]
mod tests {
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use super::{evm::Evm, native::Native};
    use crate::{
        Module, Type,
        types::{EnumReprHint, VariantData},
    };

    #[test]
    fn nested_enums_lay_out_each_level_once() {
        let evm = Module::new(&Evm::new(TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        )));
        let native = Module::new(&Native::new(TargetTriple::new(
            Architecture::Aarch64,
            Vendor::Unknown,
            OperatingSystem::Native,
        )));
        // `E{n}` is `enum { #None, #Some(E{n - 1}) }`. Laying out a level's
        // size and alignment separately would lay out the one below twice.
        for (module, outer, step) in [(evm, 64, 32), (native, 16, 8)] {
            let nested = module.ctx.with_ty_store_mut(|store| {
                (0..64).fold(Type::I64, |inner, level| {
                    let variant = |name: &str, fields: &[Type]| VariantData {
                        name: name.to_string(),
                        explicit_discriminant: None,
                        fields: fields.to_vec(),
                    };
                    store.make_enum(
                        &format!("E{level}"),
                        &[variant("None", &[]), variant("Some", &[inner])],
                        EnumReprHint::Default,
                    )
                })
            });
            // Each level adds a tag `step` bytes wide with its padding.
            assert_eq!(module.ctx.size_of_unchecked(nested), outer + 63 * step);
        }
    }
}
