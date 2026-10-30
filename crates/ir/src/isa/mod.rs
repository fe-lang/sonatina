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
    fn size_of(&self, ty: Type, store: &TypeStore) -> Result<usize, TypeLayoutError>;
    fn align_of(&self, ty: Type, store: &TypeStore) -> Result<usize, TypeLayoutError>;
    /// The offset of field `field` of variant `variant` in an enum `data`.
    fn enum_variant_field_offset(
        &self,
        data: &EnumData,
        variant: usize,
        field: usize,
        store: &TypeStore,
    ) -> Option<usize>;
    fn pointer_repl(&self) -> Type;
    fn endian(&self) -> Endian;
}

/// Where an enum's parts go when its variants share payload storage: the tag
/// at offset zero, then each variant's fields placed like a struct's, from one
/// payload offset aligned for every field of every variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnumLayout {
    pub payload_offset: usize,
    pub size: usize,
    pub align: usize,
}

impl EnumLayout {
    /// The layout for a tag and variant fields given as `(size, align)`.
    pub fn new(tag: (usize, usize), variants: &[Vec<(usize, usize)>]) -> Self {
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

/// The offsets of `fields`, given as `(size, align)`, placed like a struct's
/// fields, and the end of the last.
pub fn place_fields(fields: &[(usize, usize)]) -> (Vec<usize>, usize) {
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
