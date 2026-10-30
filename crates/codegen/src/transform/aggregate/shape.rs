use std::{cmp::Ordering, ops::Range};

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    DataFlowGraph, Type, U256, ValueId,
    module::ModuleCtx,
    types::{CompoundType, EnumData, EnumVariantRef, TypeStore},
};

// Object references embedded in SSA aggregates have no object slice/capture
// identity. Classify by type so arguments, phi results and call returns share
// the boundary. A raw pointer publishes what it reaches when it enters an
// aggregate, so it does not make one a reference aggregate.
pub(crate) fn is_reference_aggregate(module: &ModuleCtx, ty: Type) -> bool {
    module.with_ty_store(|types| {
        if !matches!(
            compound_ty(types, ty),
            Some(CompoundType::Array { .. } | CompoundType::Struct(_) | CompoundType::Enum(_))
        ) {
            return false;
        }
        let mut pending = vec![ty];
        let mut seen = FxHashSet::default();
        while let Some(ty) = pending.pop() {
            if !seen.insert(ty) {
                continue;
            }
            match compound_ty(types, ty) {
                Some(CompoundType::ObjRef(_) | CompoundType::ConstRef(_)) => {
                    return true;
                }
                Some(CompoundType::Array { elem, len }) if *len != 0 => pending.push(*elem),
                Some(CompoundType::Struct(data)) => pending.extend(data.fields.iter().copied()),
                Some(CompoundType::Enum(data)) => {
                    pending.extend(
                        data.variants
                            .iter()
                            .flat_map(|variant| variant.fields.iter().copied()),
                    );
                }
                _ => {}
            }
        }
        false
    })
}

pub type FieldPath = SmallVec<[u32; 4]>;
pub type RuntimeLeaves = SmallVec<[AggregateLeaf; 4]>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AggregateLeaf {
    pub path: FieldPath,
    pub ty: Type,
    pub offset_bytes: u32,
    pub size_bytes: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AggregateShape {
    pub root_ty: Type,
    pub leaves: SmallVec<[AggregateLeaf; 4]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AggregateSlice {
    pub ty: Type,
    pub first_leaf: usize,
    pub leaf_count: usize,
}

/// An arbitrary total order, which lets a set of slices take one canonical
/// order. `Type`'s own partial order compares integer widths.
impl Ord for AggregateSlice {
    fn cmp(&self, other: &Self) -> Ordering {
        let key = |slice: &Self| {
            let ty = match slice.ty {
                Type::I1 => (0, None),
                Type::I8 => (1, None),
                Type::I16 => (2, None),
                Type::I32 => (3, None),
                Type::I64 => (4, None),
                Type::I128 => (5, None),
                Type::I256 => (6, None),
                Type::EnumTag(compound) => (7, Some(compound)),
                Type::Compound(compound) => (8, Some(compound)),
                Type::Unit => (9, None),
            };
            (ty, slice.first_leaf, slice.leaf_count)
        };
        key(self).cmp(&key(other))
    }
}

impl PartialOrd for AggregateSlice {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Where a type's enums put their variants' payloads, in leaf coordinates.
/// One enum's variants share payload storage, so a leaf range in one
/// variant's payload may overlap any range in another's.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum PayloadPartition {
    /// Consecutive children, struct fields or one variant's fields: each
    /// child's first leaf, leaf count and partition if it holds an enum.
    Fields(Vec<(usize, usize, Option<PayloadPartition>)>),
    Array {
        stride: usize,
        elem: Box<PayloadPartition>,
    },
    /// Each variant's fields, after the tag leaf.
    Enum(Vec<(usize, usize, PayloadPartition)>),
}

impl PayloadPartition {
    /// Whether leaf ranges `a` and `b`, which share no leaf, lie in the
    /// payloads of different variants of one enum.
    pub(crate) fn separates_variants(&self, a: Range<usize>, b: Range<usize>) -> bool {
        let within = |first: usize, count: usize, range: &Range<usize>| {
            first <= range.start && range.end <= first + count
        };
        let shift = |range: &Range<usize>, by: usize| range.start - by..range.end - by;
        match self {
            Self::Fields(children) => children.iter().any(|(first, count, child)| {
                child.as_ref().is_some_and(|child| {
                    within(*first, *count, &a)
                        && within(*first, *count, &b)
                        && child.separates_variants(shift(&a, *first), shift(&b, *first))
                })
            }),
            Self::Array { stride, elem } => {
                let first = a.start / stride * stride;
                within(first, *stride, &a)
                    && within(first, *stride, &b)
                    && elem.separates_variants(shift(&a, first), shift(&b, first))
            }
            Self::Enum(variants) => {
                let variant = |range: &Range<usize>| {
                    variants
                        .iter()
                        .position(|&(first, count, _)| within(first, count, range))
                };
                match (variant(&a), variant(&b)) {
                    (Some(x), Some(y)) if x != y => true,
                    (Some(x), Some(_)) => {
                        let (first, _, fields) = &variants[x];
                        fields.separates_variants(shift(&a, *first), shift(&b, *first))
                    }
                    _ => false,
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnumSlotInfo {
    Tag {
        ty: Type,
    },
    VariantField {
        variant: EnumVariantRef,
        field: u32,
        ty: Type,
    },
}

impl EnumSlotInfo {
    pub fn ty(self) -> Type {
        match self {
            Self::Tag { ty } | Self::VariantField { ty, .. } => ty,
        }
    }
}

#[derive(Default)]
pub struct AggregateLayoutCache {
    shape_cache: FxHashMap<Type, AggregateShape>,
    runtime_leaf_cache: FxHashMap<Type, RuntimeLeaves>,
    size_align_cache: FxHashMap<Type, Option<(u32, u32)>>,
    flattened_leaf_count_cache: FxHashMap<Type, Option<usize>>,
    supported_aggregate_cache: FxHashMap<Type, bool>,
    supported_scalar_shape_cache: FxHashMap<Type, bool>,
    slice_path_cache: FxHashMap<(Type, FieldPath), Option<AggregateSlice>>,
}

impl AggregateLayoutCache {
    pub fn clear(&mut self) {
        self.shape_cache.clear();
        self.runtime_leaf_cache.clear();
        self.size_align_cache.clear();
        self.flattened_leaf_count_cache.clear();
        self.supported_aggregate_cache.clear();
        self.supported_scalar_shape_cache.clear();
        self.slice_path_cache.clear();
    }

    fn with_layout<R>(&mut self, module: &ModuleCtx, f: impl FnOnce(&mut LayoutCtx<'_>) -> R) -> R {
        module.with_ty_store(|types| {
            let mut layout = LayoutCtx {
                module,
                types,
                cache: Some(self),
            };
            f(&mut layout)
        })
    }

    pub fn shape(&mut self, module: &ModuleCtx, ty: Type) -> Option<AggregateShape> {
        self.with_layout(module, |layout| layout.shape(ty))
    }

    /// Count coordinates without constructing paths or layouts for every leaf.
    pub fn shape_leaf_count(&mut self, module: &ModuleCtx, ty: Type) -> Option<usize> {
        self.with_layout(module, |layout| {
            if !layout.is_supported_scalar_shape_ty(ty) {
                return None;
            }
            layout.flattened_leaf_count(ty)
        })
    }

    /// The largest child slices of `ty` outside leaves `range` (`[start, end)`,
    /// relative to `ty`), splitting each struct or array child the range
    /// partly covers. A partly covered enum or packed struct, which cannot
    /// split, is kept whole when `keep_unsplit` and left out otherwise. `None`
    /// when the parts would exceed `limit` slices.
    pub(crate) fn slices_outside(
        &mut self,
        module: &ModuleCtx,
        ty: Type,
        range: (usize, usize),
        keep_unsplit: bool,
        limit: usize,
    ) -> Option<SmallVec<[AggregateSlice; 4]>> {
        self.with_layout(module, |layout| {
            let mut parts = SmallVec::new();
            let mut split = SliceSplit {
                range,
                keep_unsplit,
                limit,
                parts: &mut parts,
            };
            layout.push_slices_outside(ty, 0, &mut split)?;
            Some(parts)
        })
    }

    pub(crate) fn child_containing_slice(
        &mut self,
        module: &ModuleCtx,
        ty: Type,
        slice: AggregateSlice,
    ) -> Option<(u32, AggregateSlice)> {
        self.with_layout(module, |layout| {
            if let Some(CompoundType::Array { elem, len }) = compound_ty(layout.types, ty) {
                let (elem, len) = (*elem, *len);
                let count = layout.flattened_leaf_count(elem)?;
                let index = slice.first_leaf.checked_div(count)?;
                if index >= len
                    || slice.first_leaf.checked_add(slice.leaf_count)?
                        > (index + 1).checked_mul(count)?
                {
                    return None;
                }
                return Some((
                    u32::try_from(index).ok()?,
                    AggregateSlice {
                        ty: elem,
                        first_leaf: index * count,
                        leaf_count: count,
                    },
                ));
            }
            let count = layout.aggregate_child_count(ty)?;
            (0..count).find_map(|index| {
                let index = u32::try_from(index).ok()?;
                let child = layout.aggregate_slice_for_index(ty, index)?;
                (child.first_leaf <= slice.first_leaf
                    && slice.first_leaf.checked_add(slice.leaf_count)?
                        <= child.first_leaf.checked_add(child.leaf_count)?)
                .then_some((index, child))
            })
        })
    }

    pub fn runtime_leaves(&mut self, module: &ModuleCtx, ty: Type) -> Option<RuntimeLeaves> {
        self.with_layout(module, |layout| layout.runtime_leaves(ty))
    }

    pub fn single_runtime_word_leaf(
        &mut self,
        module: &ModuleCtx,
        ty: Type,
    ) -> Option<AggregateLeaf> {
        self.with_layout(module, |layout| layout.single_runtime_word_leaf(ty))
    }

    pub fn compatible_bitcast_runtime_leaves(
        &mut self,
        module: &ModuleCtx,
        from_ty: Type,
        to_ty: Type,
    ) -> Option<(RuntimeLeaves, RuntimeLeaves)> {
        self.with_layout(module, |layout| {
            layout.compatible_bitcast_runtime_leaves(from_ty, to_ty)
        })
    }

    pub fn compatible_bitcast_source_slice(
        &mut self,
        module: &ModuleCtx,
        from_ty: Type,
        to_ty: Type,
        to_slice: AggregateSlice,
    ) -> Option<AggregateSlice> {
        self.with_layout(module, |layout| {
            layout.compatible_bitcast_source_slice(from_ty, to_ty, to_slice)
        })
    }

    pub fn runtime_size_bytes(&mut self, module: &ModuleCtx, ty: Type) -> Option<u32> {
        self.with_layout(module, |layout| layout.runtime_size_bytes(ty))
    }

    pub fn is_supported_scalar_shape_ty(&mut self, module: &ModuleCtx, ty: Type) -> bool {
        self.with_layout(module, |layout| layout.is_supported_scalar_shape_ty(ty))
    }

    pub fn is_supported_aggregate_ty(&mut self, module: &ModuleCtx, ty: Type) -> bool {
        self.with_layout(module, |layout| layout.is_supported_aggregate_ty(ty))
    }

    pub fn aggregate_slice_for_gep_path(
        &mut self,
        module: &ModuleCtx,
        base_pointee_ty: Type,
        indices: &[ValueId],
        dfg: &DataFlowGraph,
    ) -> Option<AggregateSlice> {
        self.with_layout(module, |layout| {
            layout.aggregate_slice_for_gep_path(base_pointee_ty, indices, dfg)
        })
    }

    pub fn aggregate_slice_for_object_path(
        &mut self,
        module: &ModuleCtx,
        root_ty: Type,
        indices: &[ValueId],
        dfg: &DataFlowGraph,
    ) -> Option<AggregateSlice> {
        self.with_layout(module, |layout| {
            layout.aggregate_slice_for_object_path(root_ty, indices, dfg)
        })
    }

    pub fn enum_variant_field_slice(
        &mut self,
        module: &ModuleCtx,
        enum_ty: Type,
        variant: EnumVariantRef,
        field: u32,
    ) -> Option<AggregateSlice> {
        self.with_layout(module, |layout| {
            layout.enum_variant_field_slice(enum_ty, variant, field)
        })
    }
}

/// The state of [`AggregateLayoutCache::slices_outside`].
struct SliceSplit<'a> {
    range: (usize, usize),
    keep_unsplit: bool,
    limit: usize,
    parts: &'a mut SmallVec<[AggregateSlice; 4]>,
}

impl SliceSplit<'_> {
    fn push(&mut self, part: AggregateSlice) -> Option<()> {
        (self.parts.len() < self.limit).then(|| self.parts.push(part))
    }
}

struct LayoutCtx<'a> {
    module: &'a ModuleCtx,
    types: &'a TypeStore,
    cache: Option<&'a mut AggregateLayoutCache>,
}

fn with_uncached_layout<R>(module: &ModuleCtx, f: impl FnOnce(&mut LayoutCtx<'_>) -> R) -> R {
    module.with_ty_store(|types| {
        let mut layout = LayoutCtx {
            module,
            types,
            cache: None,
        };
        f(&mut layout)
    })
}

fn compound_ty(types: &TypeStore, ty: Type) -> Option<&CompoundType> {
    let Type::Compound(cmpd) = ty else {
        return None;
    };
    Some(types.resolve_compound(cmpd))
}

fn enum_field_tys(data: &EnumData) -> SmallVec<[Type; 4]> {
    data.variants
        .iter()
        .flat_map(|variant| variant.fields.iter().copied())
        .collect()
}

impl LayoutCtx<'_> {
    fn shape(&mut self, ty: Type) -> Option<AggregateShape> {
        if let Some(cache) = &mut self.cache
            && let Some(shape) = cache.shape_cache.get(&ty)
        {
            return Some(shape.clone());
        }

        let shape = self.compute_shape(ty)?;
        if let Some(cache) = &mut self.cache {
            cache.shape_cache.insert(ty, shape.clone());
        }
        Some(shape)
    }

    fn runtime_leaves(&mut self, ty: Type) -> Option<RuntimeLeaves> {
        if let Some(cache) = &mut self.cache
            && let Some(leaves) = cache.runtime_leaf_cache.get(&ty)
        {
            return Some(leaves.clone());
        }

        let leaves: RuntimeLeaves = self
            .shape(ty)?
            .leaves
            .into_iter()
            .filter(|leaf| leaf.size_bytes != 0)
            .collect();
        if let Some(cache) = &mut self.cache {
            cache.runtime_leaf_cache.insert(ty, leaves.clone());
        }
        Some(leaves)
    }

    fn single_runtime_word_leaf(&mut self, ty: Type) -> Option<AggregateLeaf> {
        let runtime_leaves = self.runtime_leaves(ty)?;
        let [leaf] = runtime_leaves.as_slice() else {
            return None;
        };
        (leaf.size_bytes == 32).then(|| leaf.clone())
    }

    fn compatible_bitcast_runtime_leaves(
        &mut self,
        from_ty: Type,
        to_ty: Type,
    ) -> Option<(RuntimeLeaves, RuntimeLeaves)> {
        let src_leaves = self.runtime_leaves(from_ty)?;
        let dst_leaves = self.runtime_leaves(to_ty)?;
        if src_leaves.len() != dst_leaves.len() {
            return None;
        }
        src_leaves
            .iter()
            .zip(&dst_leaves)
            .all(|(src_leaf, dst_leaf)| {
                src_leaf.offset_bytes == dst_leaf.offset_bytes
                    && src_leaf.size_bytes == dst_leaf.size_bytes
            })
            .then_some((src_leaves, dst_leaves))
    }

    fn compatible_bitcast_source_slice(
        &mut self,
        from_ty: Type,
        to_ty: Type,
        to_slice: AggregateSlice,
    ) -> Option<AggregateSlice> {
        self.compatible_bitcast_runtime_leaves(from_ty, to_ty)?;
        let (first_runtime_leaf, runtime_leaf_count) =
            self.runtime_leaf_range_for_slice(to_ty, to_slice)?;
        self.aggregate_slice_for_runtime_leaf_range(from_ty, first_runtime_leaf, runtime_leaf_count)
    }

    fn runtime_size_bytes(&mut self, ty: Type) -> Option<u32> {
        self.runtime_size_align_bytes(ty).map(|(size, _)| size)
    }

    fn runtime_size_align_bytes(&mut self, ty: Type) -> Option<(u32, u32)> {
        if let Some(cache) = &mut self.cache
            && let Some(size_align) = cache.size_align_cache.get(&ty)
        {
            return *size_align;
        }

        let size_align = self.compute_runtime_size_align_bytes(ty);
        if let Some(cache) = &mut self.cache {
            cache.size_align_cache.insert(ty, size_align);
        }
        size_align
    }

    fn is_supported_scalar_shape_ty(&mut self, ty: Type) -> bool {
        if let Some(cache) = &mut self.cache
            && let Some(supported) = cache.supported_scalar_shape_cache.get(&ty)
        {
            return *supported;
        }

        let supported = self.compute_is_supported_scalar_shape_ty(ty);
        if let Some(cache) = &mut self.cache {
            cache.supported_scalar_shape_cache.insert(ty, supported);
        }
        supported
    }

    fn is_supported_aggregate_ty(&mut self, ty: Type) -> bool {
        if let Some(cache) = &mut self.cache
            && let Some(supported) = cache.supported_aggregate_cache.get(&ty)
        {
            return *supported;
        }

        let supported = self.compute_is_supported_aggregate_ty(ty);
        if let Some(cache) = &mut self.cache {
            cache.supported_aggregate_cache.insert(ty, supported);
        }
        supported
    }

    fn compute_is_supported_scalar_shape_ty(&mut self, ty: Type) -> bool {
        let types = self.types;
        match compound_ty(types, ty) {
            Some(CompoundType::Struct(s)) => {
                !s.packed
                    && s.fields
                        .iter()
                        .copied()
                        .all(|field_ty| self.runtime_size_align_bytes(field_ty).is_some())
            }
            Some(CompoundType::Array { elem, .. }) => {
                self.runtime_size_align_bytes(*elem).is_some()
            }
            Some(CompoundType::Enum(data)) => enum_field_tys(data)
                .into_iter()
                .all(|field_ty| self.runtime_size_align_bytes(field_ty).is_some()),
            _ => false,
        }
    }

    fn compute_is_supported_aggregate_ty(&mut self, ty: Type) -> bool {
        let types = self.types;
        match compound_ty(types, ty) {
            Some(CompoundType::Struct(s)) => {
                !s.packed
                    && s.fields
                        .iter()
                        .copied()
                        .all(|field_ty| self.runtime_size_align_bytes(field_ty).is_some())
            }
            Some(CompoundType::Array { elem, .. }) => {
                self.runtime_size_align_bytes(*elem).is_some()
            }
            _ => false,
        }
    }

    fn aggregate_slice_for_gep_path(
        &mut self,
        base_pointee_ty: Type,
        indices: &[ValueId],
        dfg: &DataFlowGraph,
    ) -> Option<AggregateSlice> {
        if !self.is_supported_aggregate_ty(base_pointee_ty) {
            return None;
        }
        let (&first, rest) = indices.split_first()?;
        if const_u32(dfg, first)? != 0 {
            return None;
        }

        self.aggregate_slice_for_object_path(base_pointee_ty, rest, dfg)
    }

    fn aggregate_slice_for_object_path(
        &mut self,
        root_ty: Type,
        indices: &[ValueId],
        dfg: &DataFlowGraph,
    ) -> Option<AggregateSlice> {
        if !self.is_supported_aggregate_ty(root_ty) {
            return None;
        }

        let mut current_ty = root_ty;
        let mut path: FieldPath = smallvec![];
        for &idx_value in indices {
            let idx = usize::try_from(const_u32(dfg, idx_value)?).ok()?;
            match compound_ty(self.types, current_ty)? {
                CompoundType::Struct(s) => {
                    if s.packed {
                        return None;
                    }
                    current_ty = *s.fields.get(idx)?;
                    path.push(u32::try_from(idx).ok()?);
                }
                CompoundType::Array { elem, len } => {
                    if idx >= *len {
                        return None;
                    }
                    current_ty = *elem;
                    path.push(u32::try_from(idx).ok()?);
                }
                CompoundType::Enum(_)
                | CompoundType::Ptr(_)
                | CompoundType::ObjRef(_)
                | CompoundType::ConstRef(_)
                | CompoundType::Func { .. } => return None,
            }
        }

        self.aggregate_slice_for_path(root_ty, &path)
    }

    fn enum_variant_field_slice(
        &mut self,
        enum_ty: Type,
        variant: EnumVariantRef,
        field: u32,
    ) -> Option<AggregateSlice> {
        let slot = self.enum_variant_field_slot(variant, field)?;
        self.aggregate_slice_for_index(enum_ty, slot)
    }

    fn compute_shape(&mut self, ty: Type) -> Option<AggregateShape> {
        if !self.is_supported_scalar_shape_ty(ty) {
            return None;
        }

        let mut leaves: SmallVec<[AggregateLeaf; 4]> = SmallVec::new();
        let mut path: FieldPath = SmallVec::new();
        self.flatten_aggregate(ty, 0, &mut path, &mut leaves)?;

        Some(AggregateShape {
            root_ty: ty,
            leaves,
        })
    }

    fn aggregate_slice_for_index(&mut self, agg_ty: Type, idx: u32) -> Option<AggregateSlice> {
        self.aggregate_slice_for_path(agg_ty, &[idx])
    }

    fn aggregate_slice_for_path(&mut self, root_ty: Type, path: &[u32]) -> Option<AggregateSlice> {
        let path: FieldPath = path.iter().copied().collect();
        if let Some(cache) = &mut self.cache
            && let Some(slice) = cache.slice_path_cache.get(&(root_ty, path.clone()))
        {
            return *slice;
        }

        let slice = if self.is_supported_scalar_shape_ty(root_ty) {
            self.aggregate_slice_info(root_ty, &path)
                .map(|(ty, first_leaf, leaf_count)| AggregateSlice {
                    ty,
                    first_leaf,
                    leaf_count,
                })
        } else {
            None
        };
        if let Some(cache) = &mut self.cache {
            cache.slice_path_cache.insert((root_ty, path), slice);
        }
        slice
    }

    fn aggregate_slice_info(&mut self, ty: Type, path: &[u32]) -> Option<(Type, usize, usize)> {
        if path.is_empty() {
            return Some((ty, 0, self.flattened_leaf_count(ty)?));
        }

        let idx = usize::try_from(path[0]).ok()?;
        match compound_ty(self.types, ty)? {
            CompoundType::Struct(s) => {
                if s.packed {
                    return None;
                }

                let child_ty = *s.fields.get(idx)?;
                let prefix_fields: SmallVec<[Type; 4]> =
                    s.fields.iter().take(idx).copied().collect();
                let mut first_leaf = 0usize;
                for field_ty in prefix_fields {
                    first_leaf = first_leaf.checked_add(self.flattened_leaf_count(field_ty)?)?;
                }

                let (nested_ty, nested_first_leaf, leaf_count) =
                    self.aggregate_slice_info(child_ty, &path[1..])?;
                Some((
                    nested_ty,
                    first_leaf.checked_add(nested_first_leaf)?,
                    leaf_count,
                ))
            }
            CompoundType::Array { elem, len } => {
                if idx >= *len {
                    return None;
                }

                let elem = *elem;
                let elem_leaf_count = self.flattened_leaf_count(elem)?;
                let first_leaf = elem_leaf_count.checked_mul(idx)?;
                let (nested_ty, nested_first_leaf, leaf_count) =
                    self.aggregate_slice_info(elem, &path[1..])?;
                Some((
                    nested_ty,
                    first_leaf.checked_add(nested_first_leaf)?,
                    leaf_count,
                ))
            }
            CompoundType::Enum(_) => {
                let slot = self.enum_slot_info(ty, path[0])?;
                match slot {
                    EnumSlotInfo::Tag { ty: tag_ty } => (path.len() == 1).then_some((tag_ty, 0, 1)),
                    EnumSlotInfo::VariantField {
                        variant,
                        field,
                        ty: field_ty,
                    } => {
                        let first_leaf = self.enum_variant_field_first_leaf(ty, variant, field)?;
                        let (nested_ty, nested_first_leaf, leaf_count) =
                            self.aggregate_slice_info(field_ty, &path[1..])?;
                        Some((
                            nested_ty,
                            first_leaf.checked_add(nested_first_leaf)?,
                            leaf_count,
                        ))
                    }
                }
            }
            CompoundType::Ptr(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => None,
        }
    }

    fn enum_variant_field_first_leaf(
        &mut self,
        enum_ty: Type,
        variant: EnumVariantRef,
        field: u32,
    ) -> Option<usize> {
        let slot = usize::try_from(self.enum_variant_field_slot(variant, field)?).ok()?;
        let mut first_leaf = 0usize;
        for idx in 0..slot {
            let child_ty = self.aggregate_child_ty(enum_ty, u32::try_from(idx).ok()?)?;
            first_leaf = first_leaf.checked_add(self.flattened_leaf_count(child_ty)?)?;
        }
        Some(first_leaf)
    }

    fn flattened_leaf_count(&mut self, ty: Type) -> Option<usize> {
        if let Some(cache) = &mut self.cache
            && let Some(count) = cache.flattened_leaf_count_cache.get(&ty)
        {
            return *count;
        }

        let count = self.compute_flattened_leaf_count(ty);
        if let Some(cache) = &mut self.cache {
            cache.flattened_leaf_count_cache.insert(ty, count);
        }
        count
    }

    fn struct_field_offset_bytes(
        &mut self,
        fields: &[Type],
        packed: bool,
        idx: usize,
    ) -> Option<(u32, Type)> {
        if packed {
            return None;
        }
        let &field_ty = fields.get(idx)?;
        let mut offset = 0u32;

        for &ty in fields.iter().take(idx) {
            let (_, align) = self.runtime_size_align_bytes(ty)?;
            offset = align_to(offset, align)?;

            let (size, _) = self.runtime_size_align_bytes(ty)?;
            offset = offset.checked_add(size)?;
        }

        let (_, align) = self.runtime_size_align_bytes(field_ty)?;
        offset = align_to(offset, align)?;
        Some((offset, field_ty))
    }

    fn flatten_aggregate(
        &mut self,
        ty: Type,
        base_offset: u32,
        path: &mut FieldPath,
        out: &mut SmallVec<[AggregateLeaf; 4]>,
    ) -> Option<()> {
        match compound_ty(self.types, ty) {
            Some(CompoundType::Struct(s)) => {
                if s.packed {
                    return None;
                }

                let fields = s.fields.clone();
                for (idx, &field_ty) in fields.iter().enumerate() {
                    let (field_offset, _) = self.struct_field_offset_bytes(&fields, false, idx)?;
                    let total_offset = base_offset.checked_add(field_offset)?;

                    path.push(u32::try_from(idx).ok()?);
                    self.flatten_aggregate(field_ty, total_offset, path, out)?;
                    path.pop();
                }
                Some(())
            }
            Some(CompoundType::Array { elem, len }) => {
                let elem = *elem;
                let len = *len;
                let elem_size = self.runtime_size_bytes(elem)?;
                for idx in 0..len {
                    let offset = elem_size.checked_mul(u32::try_from(idx).ok()?)?;
                    let total_offset = base_offset.checked_add(offset)?;
                    path.push(u32::try_from(idx).ok()?);
                    self.flatten_aggregate(elem, total_offset, path, out)?;
                    path.pop();
                }
                Some(())
            }
            Some(CompoundType::Enum(data)) => {
                let tag_ty = enum_tag_ty(ty)?;
                let tag_size = self.runtime_size_bytes(tag_ty)?;
                path.push(0);
                out.push(AggregateLeaf {
                    path: path.clone(),
                    ty: tag_ty,
                    offset_bytes: base_offset,
                    size_bytes: tag_size,
                });
                path.pop();

                // Leaves of different variants share the target's payload
                // storage, so their bytes may overlap.
                let mut slot = 1u32;
                for (variant, data_variant) in data.variants.iter().enumerate() {
                    for (field, &field_ty) in data_variant.fields.iter().enumerate() {
                        let offset = self
                            .module
                            .type_layout
                            .enum_variant_field_offset(data, variant, field, self.types)?;
                        let offset = base_offset.checked_add(u32::try_from(offset).ok()?)?;
                        path.push(slot);
                        self.flatten_aggregate(field_ty, offset, path, out)?;
                        path.pop();
                        slot = slot.checked_add(1)?;
                    }
                }
                Some(())
            }
            Some(CompoundType::Ptr(_))
            | Some(CompoundType::ObjRef(_))
            | Some(CompoundType::ConstRef(_))
            | None => {
                let size = self.runtime_size_bytes(ty)?;
                out.push(AggregateLeaf {
                    path: path.clone(),
                    ty,
                    offset_bytes: base_offset,
                    size_bytes: size,
                });
                Some(())
            }
            Some(CompoundType::Func { .. }) => None,
        }
    }

    fn payload_partition(&mut self, ty: Type) -> Option<PayloadPartition> {
        match compound_ty(self.types, ty)? {
            CompoundType::Struct(s) if !s.packed => {
                let fields = s.fields.clone();
                self.fields_partition(&fields)
            }
            CompoundType::Array { elem, len } if *len != 0 => {
                let elem = *elem;
                Some(PayloadPartition::Array {
                    stride: self.flattened_leaf_count(elem)?,
                    elem: Box::new(self.payload_partition(elem)?),
                })
            }
            CompoundType::Enum(data) => {
                let variants: Vec<SmallVec<[Type; 4]>> = data
                    .variants
                    .iter()
                    .map(|variant| variant.fields.iter().copied().collect())
                    .collect();
                let mut first = 1;
                let mut parts = Vec::with_capacity(variants.len());
                for fields in variants {
                    let count = fields.iter().try_fold(0usize, |count, &field| {
                        count.checked_add(self.flattened_leaf_count(field)?)
                    })?;
                    let fields = self
                        .fields_partition(&fields)
                        .unwrap_or(PayloadPartition::Fields(Vec::new()));
                    parts.push((first, count, fields));
                    first += count;
                }
                Some(PayloadPartition::Enum(parts))
            }
            _ => None,
        }
    }

    /// The partition of consecutive `fields`, if any of them holds an enum.
    fn fields_partition(&mut self, fields: &[Type]) -> Option<PayloadPartition> {
        let mut first = 0;
        let mut children = Vec::with_capacity(fields.len());
        for &field in fields {
            let count = self.flattened_leaf_count(field)?;
            children.push((first, count, self.payload_partition(field)));
            first += count;
        }
        children
            .iter()
            .any(|(_, _, child)| child.is_some())
            .then_some(PayloadPartition::Fields(children))
    }

    fn compute_flattened_leaf_count(&mut self, ty: Type) -> Option<usize> {
        match compound_ty(self.types, ty) {
            Some(CompoundType::Struct(s)) => {
                if s.packed {
                    return None;
                }

                let fields = s.fields.clone();
                let mut count = 0usize;
                for field_ty in fields {
                    count = count.checked_add(self.flattened_leaf_count(field_ty)?)?;
                }
                Some(count)
            }
            Some(CompoundType::Array { elem, len }) => {
                self.flattened_leaf_count(*elem)?.checked_mul(*len)
            }
            Some(CompoundType::Enum(data)) => {
                let mut count = 1usize;
                for field_ty in enum_field_tys(data) {
                    count = count.checked_add(self.flattened_leaf_count(field_ty)?)?;
                }
                Some(count)
            }
            Some(CompoundType::Func { .. }) => None,
            Some(CompoundType::Ptr(_))
            | Some(CompoundType::ObjRef(_))
            | Some(CompoundType::ConstRef(_))
            | None => Some(1),
        }
    }

    fn compute_runtime_size_align_bytes(&mut self, ty: Type) -> Option<(u32, u32)> {
        match compound_ty(self.types, ty) {
            Some(CompoundType::Struct(s)) => {
                if s.packed {
                    return None;
                }

                let fields = s.fields.clone();
                let mut size = 0u32;
                let mut align = 1u32;
                for field_ty in fields {
                    let (field_size, field_align) = self.runtime_size_align_bytes(field_ty)?;
                    size = align_to(size, field_align)?;
                    size = size.checked_add(field_size)?;
                    align = align.max(field_align);
                }
                Some((size, align))
            }
            Some(CompoundType::Array { elem, len }) => {
                let (elem_size, elem_align) = self.runtime_size_align_bytes(*elem)?;
                Some((
                    elem_size.checked_mul(u32::try_from(*len).ok()?)?,
                    elem_align,
                ))
            }
            // Variants share payload storage as the target lays them out.
            Some(CompoundType::Enum(_)) => self.primitive_size_align(ty),
            Some(CompoundType::Func { .. }) => None,
            Some(CompoundType::Ptr(_))
            | Some(CompoundType::ObjRef(_))
            | Some(CompoundType::ConstRef(_)) => {
                self.primitive_size_align(self.module.type_layout.pointer_repl())
            }
            None => self.primitive_size_align(ty),
        }
    }

    /// The target's layout of `ty`, through the type store this context holds.
    fn primitive_size_align(&self, ty: Type) -> Option<(u32, u32)> {
        let layout = self.module.type_layout;
        let size = u32::try_from(layout.size_of(ty, self.types).ok()?).ok()?;
        let align = u32::try_from(layout.align_of(ty, self.types).ok()?).ok()?;
        Some((size, align))
    }
    fn runtime_leaf_range_for_slice(
        &mut self,
        root_ty: Type,
        slice: AggregateSlice,
    ) -> Option<(usize, usize)> {
        if !self.is_supported_scalar_shape_ty(root_ty) {
            return None;
        }

        let slice_end = slice.first_leaf.checked_add(slice.leaf_count)?;
        let shape = self.shape(root_ty)?;
        if slice_end > shape.leaves.len() {
            return None;
        }

        let first_runtime_leaf = shape.leaves[..slice.first_leaf]
            .iter()
            .filter(|leaf| leaf.size_bytes != 0)
            .count();
        let runtime_leaf_count = shape.leaves[slice.first_leaf..slice_end]
            .iter()
            .filter(|leaf| leaf.size_bytes != 0)
            .count();
        Some((first_runtime_leaf, runtime_leaf_count))
    }

    fn aggregate_slice_for_runtime_leaf_range(
        &mut self,
        root_ty: Type,
        first_runtime_leaf: usize,
        target_runtime_leaf_count: usize,
    ) -> Option<AggregateSlice> {
        if !self.is_supported_scalar_shape_ty(root_ty) {
            return None;
        }

        let total_runtime_leaf_count = self.runtime_leaf_count_for_ty(root_ty)?;
        if first_runtime_leaf.checked_add(target_runtime_leaf_count)? > total_runtime_leaf_count {
            return None;
        }
        if target_runtime_leaf_count == 0 {
            return Some(AggregateSlice {
                ty: root_ty,
                first_leaf: self
                    .flattened_leaf_boundary_for_runtime_leaf(root_ty, first_runtime_leaf)?,
                leaf_count: 0,
            });
        }

        let total_leaf_count = self.flattened_leaf_count(root_ty)?;
        if first_runtime_leaf == 0 && target_runtime_leaf_count == total_runtime_leaf_count {
            return Some(AggregateSlice {
                ty: root_ty,
                first_leaf: 0,
                leaf_count: total_leaf_count,
            });
        }

        self.aggregate_slice_for_runtime_leaf_range_impl(
            root_ty,
            (first_runtime_leaf, target_runtime_leaf_count),
            (0, 0),
        )
    }

    fn aggregate_child_ty(&mut self, agg_ty: Type, idx: u32) -> Option<Type> {
        let idx = usize::try_from(idx).ok()?;
        match compound_ty(self.types, agg_ty)? {
            CompoundType::Struct(s) => (!s.packed).then_some(*s.fields.get(idx)?),
            CompoundType::Array { elem, len } => (idx < *len).then_some(*elem),
            CompoundType::Enum(_) => self
                .enum_slot_info(agg_ty, u32::try_from(idx).ok()?)
                .map(|slot| slot.ty()),
            CompoundType::Ptr(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => None,
        }
    }

    /// Pushes the parts of `ty`, whose first leaf is `base`, outside the
    /// split's range; see [`AggregateLayoutCache::slices_outside`].
    fn push_slices_outside(
        &mut self,
        ty: Type,
        base: usize,
        split: &mut SliceSplit<'_>,
    ) -> Option<()> {
        let (start, end) = split.range;
        let visit = |layout: &mut Self, split: &mut SliceSplit<'_>, child: AggregateSlice| {
            let first = base.checked_add(child.first_leaf)?;
            let last = first.checked_add(child.leaf_count)?;
            if child.leaf_count == 0 || (start <= first && last <= end) {
                Some(())
            } else if last <= start || end <= first {
                split.push(AggregateSlice {
                    first_leaf: first,
                    ..child
                })
            } else {
                layout.push_slices_outside(child.ty, first, split)
            }
        };
        match compound_ty(self.types, ty) {
            Some(CompoundType::Struct(s)) if !s.packed => {
                for index in 0..s.fields.len() {
                    let child = self.aggregate_slice_for_index(ty, u32::try_from(index).ok()?)?;
                    visit(self, split, child)?;
                }
            }
            Some(&CompoundType::Array { elem, len }) => {
                let count = self.flattened_leaf_count(elem)?;
                if count == 0 || len == 0 {
                    return Some(());
                }
                // Only the elements holding the write's first and last leaves
                // can be partly covered; skip the fully covered ones between.
                let first_hit = (start.saturating_sub(base) / count).min(len - 1);
                let last_hit = (end.saturating_sub(base).saturating_sub(1) / count).min(len - 1);
                for index in (0..=first_hit).chain(last_hit.max(first_hit + 1)..len) {
                    visit(
                        self,
                        split,
                        AggregateSlice {
                            ty: elem,
                            first_leaf: index.checked_mul(count)?,
                            leaf_count: count,
                        },
                    )?;
                }
            }
            _ if split.keep_unsplit => {
                let leaf_count = self.flattened_leaf_count(ty)?;
                split.push(AggregateSlice {
                    ty,
                    first_leaf: base,
                    leaf_count,
                })?;
            }
            _ => {}
        }
        Some(())
    }

    fn aggregate_child_count(&mut self, agg_ty: Type) -> Option<usize> {
        match compound_ty(self.types, agg_ty)? {
            CompoundType::Struct(s) => (!s.packed).then_some(s.fields.len()),
            CompoundType::Array { len, .. } => Some(*len),
            CompoundType::Enum(_) => self.enum_child_count(agg_ty),
            CompoundType::Ptr(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => None,
        }
    }

    fn is_leaf_reifiable_ty(&mut self, ty: Type) -> bool {
        match compound_ty(self.types, ty) {
            Some(CompoundType::Struct(s)) => {
                !s.packed
                    && s.fields
                        .iter()
                        .copied()
                        .all(|field_ty| self.is_leaf_reifiable_ty(field_ty))
            }
            Some(CompoundType::Array { elem, .. }) => self.is_leaf_reifiable_ty(*elem),
            Some(CompoundType::Enum(_)) => false,
            _ => true,
        }
    }

    fn aggregate_slice_for_runtime_leaf_range_impl(
        &mut self,
        ty: Type,
        target: (usize, usize),
        base: (usize, usize),
    ) -> Option<AggregateSlice> {
        let (target_first_runtime_leaf, target_runtime_leaf_count) = target;
        let (base_first_leaf, base_first_runtime_leaf) = base;
        match compound_ty(self.types, ty)? {
            CompoundType::Struct(s) => {
                if s.packed {
                    return None;
                }

                let fields = s.fields.clone();
                let mut child_first_leaf = base_first_leaf;
                let mut child_first_runtime_leaf = base_first_runtime_leaf;
                for field_ty in fields {
                    let child_leaf_count = self.flattened_leaf_count(field_ty)?;
                    let child_runtime_leaf_count = self.runtime_leaf_count_for_ty(field_ty)?;
                    if child_first_runtime_leaf == target_first_runtime_leaf
                        && child_runtime_leaf_count == target_runtime_leaf_count
                    {
                        return Some(AggregateSlice {
                            ty: field_ty,
                            first_leaf: child_first_leaf,
                            leaf_count: child_leaf_count,
                        });
                    }
                    if child_runtime_leaf_count != 0
                        && target_first_runtime_leaf >= child_first_runtime_leaf
                        && target_first_runtime_leaf + target_runtime_leaf_count
                            <= child_first_runtime_leaf + child_runtime_leaf_count
                        && let Some(slice) = self.aggregate_slice_for_runtime_leaf_range_impl(
                            field_ty,
                            target,
                            (child_first_leaf, child_first_runtime_leaf),
                        )
                    {
                        return Some(slice);
                    }
                    child_first_leaf = child_first_leaf.checked_add(child_leaf_count)?;
                    child_first_runtime_leaf =
                        child_first_runtime_leaf.checked_add(child_runtime_leaf_count)?;
                }
                None
            }
            CompoundType::Array { elem, len } => {
                let elem = *elem;
                let elem_leaf_count = self.flattened_leaf_count(elem)?;
                let elem_runtime_leaf_count = self.runtime_leaf_count_for_ty(elem)?;
                let mut child_first_leaf = base_first_leaf;
                let mut child_first_runtime_leaf = base_first_runtime_leaf;
                for _ in 0..*len {
                    if child_first_runtime_leaf == target_first_runtime_leaf
                        && elem_runtime_leaf_count == target_runtime_leaf_count
                    {
                        return Some(AggregateSlice {
                            ty: elem,
                            first_leaf: child_first_leaf,
                            leaf_count: elem_leaf_count,
                        });
                    }
                    if elem_runtime_leaf_count != 0
                        && target_first_runtime_leaf >= child_first_runtime_leaf
                        && target_first_runtime_leaf + target_runtime_leaf_count
                            <= child_first_runtime_leaf + elem_runtime_leaf_count
                        && let Some(slice) = self.aggregate_slice_for_runtime_leaf_range_impl(
                            elem,
                            target,
                            (child_first_leaf, child_first_runtime_leaf),
                        )
                    {
                        return Some(slice);
                    }
                    child_first_leaf = child_first_leaf.checked_add(elem_leaf_count)?;
                    child_first_runtime_leaf =
                        child_first_runtime_leaf.checked_add(elem_runtime_leaf_count)?;
                }
                None
            }
            CompoundType::Enum(data) => {
                if target_first_runtime_leaf == base_first_runtime_leaf
                    && target_runtime_leaf_count == 1
                {
                    return Some(AggregateSlice {
                        ty: enum_tag_ty(ty)?,
                        first_leaf: base_first_leaf,
                        leaf_count: 1,
                    });
                }

                let mut child_first_leaf = base_first_leaf.checked_add(1)?;
                let mut child_first_runtime_leaf = base_first_runtime_leaf.checked_add(1)?;
                for field_ty in enum_field_tys(data) {
                    let child_leaf_count = self.flattened_leaf_count(field_ty)?;
                    let child_runtime_leaf_count = self.runtime_leaf_count_for_ty(field_ty)?;
                    if child_first_runtime_leaf == target_first_runtime_leaf
                        && child_runtime_leaf_count == target_runtime_leaf_count
                    {
                        return Some(AggregateSlice {
                            ty: field_ty,
                            first_leaf: child_first_leaf,
                            leaf_count: child_leaf_count,
                        });
                    }
                    if child_runtime_leaf_count != 0
                        && target_first_runtime_leaf >= child_first_runtime_leaf
                        && target_first_runtime_leaf + target_runtime_leaf_count
                            <= child_first_runtime_leaf + child_runtime_leaf_count
                        && let Some(slice) = self.aggregate_slice_for_runtime_leaf_range_impl(
                            field_ty,
                            target,
                            (child_first_leaf, child_first_runtime_leaf),
                        )
                    {
                        return Some(slice);
                    }
                    child_first_leaf = child_first_leaf.checked_add(child_leaf_count)?;
                    child_first_runtime_leaf =
                        child_first_runtime_leaf.checked_add(child_runtime_leaf_count)?;
                }
                None
            }
            CompoundType::Ptr(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => None,
        }
    }

    fn runtime_leaf_count_for_ty(&mut self, ty: Type) -> Option<usize> {
        match compound_ty(self.types, ty) {
            Some(CompoundType::Struct(s)) => {
                if s.packed {
                    return None;
                }

                let fields = s.fields.clone();
                let mut count = 0usize;
                for field_ty in fields {
                    count = count.checked_add(self.runtime_leaf_count_for_ty(field_ty)?)?;
                }
                Some(count)
            }
            Some(CompoundType::Array { elem, len }) => {
                self.runtime_leaf_count_for_ty(*elem)?.checked_mul(*len)
            }
            Some(CompoundType::Enum(data)) => {
                let mut count = 1usize;
                for field_ty in enum_field_tys(data) {
                    count = count.checked_add(self.runtime_leaf_count_for_ty(field_ty)?)?;
                }
                Some(count)
            }
            Some(CompoundType::Func { .. }) => None,
            Some(CompoundType::Ptr(_))
            | Some(CompoundType::ObjRef(_))
            | Some(CompoundType::ConstRef(_))
            | None => Some(usize::from(self.runtime_size_bytes(ty)? != 0)),
        }
    }

    fn flattened_leaf_boundary_for_runtime_leaf(
        &mut self,
        root_ty: Type,
        runtime_leaf_boundary: usize,
    ) -> Option<usize> {
        let shape = self.shape(root_ty)?;
        let total_runtime_leaf_count = shape
            .leaves
            .iter()
            .filter(|leaf| leaf.size_bytes != 0)
            .count();
        if runtime_leaf_boundary > total_runtime_leaf_count {
            return None;
        }

        let mut seen_runtime_leaves = 0usize;
        for (idx, leaf) in shape.leaves.iter().enumerate() {
            if seen_runtime_leaves == runtime_leaf_boundary {
                return Some(idx);
            }
            if leaf.size_bytes != 0 {
                seen_runtime_leaves = seen_runtime_leaves.checked_add(1)?;
            }
        }
        (seen_runtime_leaves == runtime_leaf_boundary).then_some(shape.leaves.len())
    }

    fn enum_child_count(&self, enum_ty: Type) -> Option<usize> {
        let Type::Compound(enum_cmpd) = enum_ty else {
            return None;
        };
        let data = self.types.enum_data(enum_cmpd)?;
        let mut count = 1usize;
        for variant in &data.variants {
            count = count.checked_add(variant.fields.len())?;
        }
        Some(count)
    }

    fn enum_variant_field_slot(&self, variant: EnumVariantRef, field: u32) -> Option<u32> {
        let data = self.types.enum_data(variant.enum_ty())?;
        let field = usize::try_from(field).ok()?;
        let variant_idx = usize::try_from(variant.index()).ok()?;
        let mut slot = 1u32;
        for (idx, variant_data) in data.variants.iter().enumerate() {
            if idx == variant_idx {
                variant_data.fields.get(field)?;
                return slot.checked_add(u32::try_from(field).ok()?);
            }
            slot = slot.checked_add(u32::try_from(variant_data.fields.len()).ok()?)?;
        }
        None
    }

    fn enum_slot_info(&self, enum_ty: Type, idx: u32) -> Option<EnumSlotInfo> {
        if idx == 0 {
            return Some(EnumSlotInfo::Tag {
                ty: enum_tag_ty(enum_ty)?,
            });
        }

        let Type::Compound(enum_cmpd) = enum_ty else {
            return None;
        };
        let data = self.types.enum_data(enum_cmpd)?;
        let mut slot = 1u32;
        for (variant_idx, variant_data) in data.variants.iter().enumerate() {
            for (field_idx, &field_ty) in variant_data.fields.iter().enumerate() {
                if slot == idx {
                    return Some(EnumSlotInfo::VariantField {
                        variant: EnumVariantRef::new(
                            enum_cmpd,
                            u32::try_from(variant_idx).expect("enum variant index overflow"),
                        ),
                        field: u32::try_from(field_idx).ok()?,
                        ty: field_ty,
                    });
                }
                slot = slot.checked_add(1)?;
            }
        }
        None
    }
}

pub fn aggregate_shape(module: &ModuleCtx, ty: Type) -> Option<AggregateShape> {
    with_uncached_layout(module, |layout| layout.shape(ty))
}

pub fn runtime_leaf_range_for_slice(
    module: &ModuleCtx,
    root_ty: Type,
    slice: AggregateSlice,
) -> Option<(usize, usize)> {
    with_uncached_layout(module, |layout| {
        layout.runtime_leaf_range_for_slice(root_ty, slice)
    })
}

pub fn aggregate_slice_for_index(
    module: &ModuleCtx,
    agg_ty: Type,
    idx: u32,
) -> Option<AggregateSlice> {
    with_uncached_layout(module, |layout| {
        layout.aggregate_slice_for_index(agg_ty, idx)
    })
}

pub fn aggregate_slice_for_path(
    module: &ModuleCtx,
    root_ty: Type,
    path: &[u32],
) -> Option<AggregateSlice> {
    with_uncached_layout(module, |layout| {
        layout.aggregate_slice_for_path(root_ty, path)
    })
}

pub fn aggregate_slice_for_runtime_leaf_range(
    module: &ModuleCtx,
    root_ty: Type,
    first_runtime_leaf: usize,
    target_runtime_leaf_count: usize,
) -> Option<AggregateSlice> {
    with_uncached_layout(module, |layout| {
        layout.aggregate_slice_for_runtime_leaf_range(
            root_ty,
            first_runtime_leaf,
            target_runtime_leaf_count,
        )
    })
}

pub fn aggregate_slice_for_gep_path(
    module: &ModuleCtx,
    base_pointee_ty: Type,
    indices: &[ValueId],
    dfg: &DataFlowGraph,
) -> Option<AggregateSlice> {
    with_uncached_layout(module, |layout| {
        layout.aggregate_slice_for_gep_path(base_pointee_ty, indices, dfg)
    })
}

pub fn aggregate_slice_for_object_path(
    module: &ModuleCtx,
    root_ty: Type,
    indices: &[ValueId],
    dfg: &DataFlowGraph,
) -> Option<AggregateSlice> {
    with_uncached_layout(module, |layout| {
        layout.aggregate_slice_for_object_path(root_ty, indices, dfg)
    })
}

pub fn aggregate_child_ty(module: &ModuleCtx, agg_ty: Type, idx: u32) -> Option<Type> {
    with_uncached_layout(module, |layout| layout.aggregate_child_ty(agg_ty, idx))
}

pub fn aggregate_child_count(module: &ModuleCtx, agg_ty: Type) -> Option<usize> {
    with_uncached_layout(module, |layout| layout.aggregate_child_count(agg_ty))
}

pub fn struct_field_offset_bytes(
    fields: &[Type],
    packed: bool,
    idx: usize,
    module: &ModuleCtx,
) -> Option<(u32, Type)> {
    with_uncached_layout(module, |layout| {
        layout.struct_field_offset_bytes(fields, packed, idx)
    })
}

pub fn align_to(offset: u32, align: u32) -> Option<u32> {
    if align <= 1 {
        return Some(offset);
    }
    if !align.is_power_of_two() {
        return None;
    }
    offset.checked_add(align - 1).map(|v| v & !(align - 1))
}

pub fn const_u32(dfg: &DataFlowGraph, value: ValueId) -> Option<u32> {
    let imm = dfg.value_imm(value)?;
    if imm.is_negative() {
        return None;
    }
    let u256 = imm.as_i256().to_u256();
    (u256 <= U256::from(u32::MAX)).then_some(u256.low_u32())
}

/// Returns whether `ty` can be reified with generic aggregate ops such as
/// `insert_value` and `extract_value`.
///
/// This intentionally excludes enums. Enums participate in scalar-shape
/// flattening, but they must be rebuilt with enum-specific ops.
pub fn is_supported_aggregate_ty(module: &ModuleCtx, ty: Type) -> bool {
    with_uncached_layout(module, |layout| layout.is_supported_aggregate_ty(ty))
}

/// Returns whether `ty` can be flattened into runtime leaves for scalar-shape
/// transforms.
///
/// This is broader than [`is_supported_aggregate_ty`]: it includes enums so
/// enum-bearing structs and arrays can still participate in scalar-shape
/// analyses, even though enums are not generic aggregate-op destinations.
pub fn is_supported_scalar_shape_ty(module: &ModuleCtx, ty: Type) -> bool {
    with_uncached_layout(module, |layout| layout.is_supported_scalar_shape_ty(ty))
}

/// Returns whether `ty` can always be rebuilt from an arbitrary runtime leaf
/// slice without value-dependent reconstruction.
///
/// This is stricter than [`is_supported_scalar_shape_ty`]. Enums, and aggregates
/// containing enums, are excluded because rebuilding a full value from arbitrary
/// leaf SSA state would require recovering the active variant from dynamic tag
/// leaves.
pub fn is_leaf_reifiable_ty(module: &ModuleCtx, ty: Type) -> bool {
    with_uncached_layout(module, |layout| layout.is_leaf_reifiable_ty(ty))
}

pub fn runtime_size_bytes(module: &ModuleCtx, ty: Type) -> Option<u32> {
    with_uncached_layout(module, |layout| layout.runtime_size_bytes(ty))
}

pub fn enum_tag_ty(ty: Type) -> Option<Type> {
    let Type::Compound(enum_ty) = ty else {
        return None;
    };
    Some(Type::EnumTag(enum_ty))
}

/// The payload partition of `ty`, if it holds an enum.
pub(crate) fn payload_partition(module: &ModuleCtx, ty: Type) -> Option<PayloadPartition> {
    with_uncached_layout(module, |layout| layout.payload_partition(ty))
}

pub fn enum_slot_info(module: &ModuleCtx, enum_ty: Type, idx: u32) -> Option<EnumSlotInfo> {
    with_uncached_layout(module, |layout| layout.enum_slot_info(enum_ty, idx))
}

pub fn enum_tag_slice(module: &ModuleCtx, enum_ty: Type) -> Option<AggregateSlice> {
    aggregate_slice_for_index(module, enum_ty, 0)
}

pub fn enum_variant_field_slice(
    module: &ModuleCtx,
    enum_ty: Type,
    variant: EnumVariantRef,
    field: u32,
) -> Option<AggregateSlice> {
    with_uncached_layout(module, |layout| {
        layout.enum_variant_field_slice(enum_ty, variant, field)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::parse_test_module;
    use sonatina_ir::{
        DataFlowGraph, Type, ValueId,
        types::{EnumReprHint, VariantData},
    };

    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use crate::transform::aggregate::{
        compute_object_effect_summaries, object_tracking::AggregateFacts, objref_element_ty,
        provenance::ProvenanceSnapshot,
    };

    #[test]
    fn large_object_access_facts_do_not_materialize_leaf_layouts() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<[i256; 1000000]>) -> i256 {
block0:
    v1.objref<i256> = obj.index v0 999999.i256;
    obj.store v1 42.i256;
    v2.i256 = obj.load v1;
    return v2;
}
"#,
        );
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(report.is_ok(), "{report}");
        let effects = compute_object_effect_summaries(&module);
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let mut cache = AggregateLayoutCache::default();
            let mut snapshot = ProvenanceSnapshot::new(func, Some(&effects));
            let facts = AggregateFacts::for_call_planner(func, &mut cache, &mut snapshot);
            assert_eq!(
                facts.root_slices()[&func.arg_values[0]].leaf_count,
                1_000_000
            );
            let field = facts
                .complete()
                .exact_projection(ValueId::from_u32(1))
                .unwrap();
            assert_eq!(
                (field.slice.first_leaf, field.slice.leaf_count),
                (999_999, 1)
            );
            assert!(cache.shape_cache.is_empty());
            assert!(cache.runtime_leaf_cache.is_empty());
            assert!(cache.flattened_leaf_count_cache.len() <= 2);
        });
    }

    #[test]
    fn sparse_leaf_counts_match_nested_shape_coordinates() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"
type @Empty = {};
type @Bytes = { [i8; 3] };
type @Choice = enum { #None, #Pair(i256,@Bytes) };
type @Nested = { @Empty, [@Choice; 2], objref<i256>, [i256; 0] };
func private %f() {
block0:
    return;
}
"#,
        );
        let mut cache = AggregateLayoutCache::default();
        for name in ["Empty", "Nested"] {
            let ty = module
                .ctx
                .with_ty_store(|types| Type::Compound(types.lookup_struct(name).unwrap()));
            let count = cache.shape_leaf_count(&module.ctx, ty).unwrap();
            let shape = cache.shape(&module.ctx, ty).unwrap();
            assert_eq!(count, shape.leaves.len(), "{name}");
        }
    }

    #[test]
    fn flattens_nested_struct_array_offsets() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

type @inner = { i256, [i256; 2] };
type @outer = { @inner, i256 };

func private %f() {
block0:
    return;
}
"#,
        );
        let outer = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("outer").unwrap()));
        let shape = aggregate_shape(&module.ctx, outer).expect("shape");
        assert_eq!(shape.leaves.len(), 4);
        assert_eq!(shape.leaves[0].path.as_slice(), &[0, 0]);
        assert_eq!(shape.leaves[0].offset_bytes, 0);
        assert_eq!(shape.leaves[1].path.as_slice(), &[0, 1, 0]);
        assert_eq!(shape.leaves[1].offset_bytes, 32);
        assert_eq!(shape.leaves[2].path.as_slice(), &[0, 1, 1]);
        assert_eq!(shape.leaves[2].offset_bytes, 64);
        assert_eq!(shape.leaves[3].path.as_slice(), &[1]);
        assert_eq!(shape.leaves[3].offset_bytes, 96);
    }

    #[test]
    fn computes_gep_slice_and_rejects_dynamic_indices() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

type @pair = { i256, [i256; 2] };

func private %f() {
block0:
    return;
}
"#,
        );
        let pair = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("pair").unwrap()));
        let mut dfg = DataFlowGraph::new(module.ctx.clone());
        let zero = dfg.make_imm_value(0i8);
        let one = dfg.make_imm_value(1i8);
        let dyn_idx = dfg.make_undef_value(Type::I8);

        let arr_slice =
            aggregate_slice_for_gep_path(&module.ctx, pair, &[zero, one], &dfg).expect("slice");
        assert_eq!(
            arr_slice.ty,
            module
                .ctx
                .with_ty_store_mut(|s| s.make_array(Type::I256, 2))
        );
        assert_eq!(arr_slice.leaf_count, 2);

        let elem_slice = aggregate_slice_for_gep_path(&module.ctx, pair, &[zero, one, one], &dfg)
            .expect("slice");
        assert_eq!(elem_slice.ty, Type::I256);
        assert_eq!(elem_slice.leaf_count, 1);

        assert!(
            aggregate_slice_for_gep_path(&module.ctx, pair, &[zero, one, dyn_idx], &dfg).is_none()
        );
    }

    #[test]
    fn computes_empty_subaggregate_slice() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

type @empty = {};
type @outer = { @empty, i256 };

func private %f() {
block0:
    return;
}
"#,
        );
        let empty = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("empty").unwrap()));
        let outer = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("outer").unwrap()));

        let empty_slice = aggregate_slice_for_index(&module.ctx, outer, 0).expect("empty slice");
        assert_eq!(empty_slice.ty, empty);
        assert_eq!(empty_slice.first_leaf, 0);
        assert_eq!(empty_slice.leaf_count, 0);

        let payload_slice =
            aggregate_slice_for_index(&module.ctx, outer, 1).expect("payload slice");
        assert_eq!(payload_slice.ty, Type::I256);
        assert_eq!(payload_slice.first_leaf, 0);
        assert_eq!(payload_slice.leaf_count, 1);

        let whole_empty = aggregate_slice_for_path(&module.ctx, empty, &[]).expect("whole empty");
        assert_eq!(whole_empty.ty, empty);
        assert_eq!(whole_empty.first_leaf, 0);
        assert_eq!(whole_empty.leaf_count, 0);
    }

    #[test]
    fn flattens_pointer_leaves_in_structs() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

type @pair = { *i8, i256 };

func private %f() {
block0:
    return;
}
"#,
        );
        let pair = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("pair").unwrap()));
        let ptr_i8 = Type::I8.to_ptr(&module.ctx);
        let shape = aggregate_shape(&module.ctx, pair).expect("shape");
        assert_eq!(shape.leaves.len(), 2);
        assert_eq!(shape.leaves[0].path.as_slice(), &[0]);
        assert_eq!(shape.leaves[0].ty, ptr_i8);
        assert_eq!(shape.leaves[0].offset_bytes, 0);
        assert_eq!(shape.leaves[0].size_bytes, 32);
        assert_eq!(shape.leaves[1].path.as_slice(), &[1]);
        assert_eq!(shape.leaves[1].ty, Type::I256);
        assert_eq!(shape.leaves[1].offset_bytes, 32);
        assert_eq!(shape.leaves[1].size_bytes, 32);
    }

    #[test]
    fn flattens_pointer_leaves_in_arrays() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

func private %f() {
block0:
    return;
}
"#,
        );
        let ptr_i8 = Type::I8.to_ptr(&module.ctx);
        let ptrs = module.ctx.with_ty_store_mut(|s| s.make_array(ptr_i8, 2));
        let shape = aggregate_shape(&module.ctx, ptrs).expect("shape");
        assert_eq!(shape.leaves.len(), 2);
        assert_eq!(shape.leaves[0].path.as_slice(), &[0]);
        assert_eq!(shape.leaves[0].ty, ptr_i8);
        assert_eq!(shape.leaves[0].offset_bytes, 0);
        assert_eq!(shape.leaves[1].path.as_slice(), &[1]);
        assert_eq!(shape.leaves[1].ty, ptr_i8);
        assert_eq!(shape.leaves[1].offset_bytes, 32);
        assert_eq!(shape.leaves[1].size_bytes, 32);
    }

    #[test]
    fn supports_structs_with_recursive_enum_leaves() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

func private %f() {
block0:
    return;
}
"#,
        );
        let holder = module.ctx.with_ty_store_mut(|s| {
            let option = s.make_enum(
                "option",
                &[
                    VariantData {
                        name: "Some".to_string(),
                        explicit_discriminant: None,
                        fields: vec![Type::I256],
                    },
                    VariantData {
                        name: "None".to_string(),
                        explicit_discriminant: None,
                        fields: vec![],
                    },
                ],
                EnumReprHint::Default,
            );
            s.make_struct("holder", &[option, Type::I256], false)
        });
        let option = aggregate_child_ty(&module.ctx, holder, 0).expect("enum field");
        let Type::Compound(option_cmpd) = option else {
            panic!("enum field must be a compound enum type");
        };
        let option_size = runtime_size_bytes(&module.ctx, option).expect("enum size");
        let shape = aggregate_shape(&module.ctx, holder).expect("shape");
        assert!(is_supported_aggregate_ty(&module.ctx, holder));
        assert!(!is_supported_aggregate_ty(&module.ctx, option));
        assert!(is_supported_scalar_shape_ty(&module.ctx, option));
        assert_eq!(shape.leaves.len(), 3);
        assert_eq!(shape.leaves[0].path.as_slice(), &[0, 0]);
        assert_eq!(shape.leaves[0].ty, Type::EnumTag(option_cmpd));
        assert_eq!(shape.leaves[0].offset_bytes, 0);
        assert_eq!(shape.leaves[1].path.as_slice(), &[0, 1]);
        assert_eq!(shape.leaves[1].ty, Type::I256);
        assert_eq!(shape.leaves[1].offset_bytes, 32);
        assert_eq!(shape.leaves[2].path.as_slice(), &[1]);
        assert_eq!(shape.leaves[2].ty, Type::I256);
        assert_eq!(
            shape.leaves[2].offset_bytes,
            align_to(option_size, 32).expect("offset")
        );
    }

    #[test]
    fn enum_leaves_follow_the_target_layout() {
        for target in ["evm-ethereum-osaka", "aarch64-unknown-native"] {
            let module = parse_test_module(&format!(
                r#"
target = "{target}"
type @E = enum {{ #A(i64), #B(i64) }};
type @O = enum {{ #None, #Some(i64) }};
type @Pair = {{ i8, i64 }};
func private %f(v0.objref<@E>, v1.objref<@O>, v2.objref<[i64; 3]>, v3.objref<@Pair>) {{
block0:
    return;
}}
"#
            ));
            let func_ref = module.funcs()[0];
            let args = module.ctx.func_sig(func_ref, |sig| sig.args().to_vec());
            let [e, option, words, pair] = args
                .iter()
                .map(|&arg| objref_element_ty(&module.ctx, arg).unwrap())
                .collect::<Vec<_>>()[..]
            else {
                unreachable!()
            };
            let leaves = |ty| {
                aggregate_shape(&module.ctx, ty)
                    .unwrap()
                    .leaves
                    .iter()
                    .map(|leaf| (leaf.offset_bytes, leaf.size_bytes))
                    .collect::<Vec<_>>()
            };
            let mut cache = AggregateLayoutCache::default();
            let mut compatible = |from, to| {
                cache
                    .compatible_bitcast_runtime_leaves(&module.ctx, from, to)
                    .is_some()
            };
            if target.starts_with("evm") {
                // `B`'s i64 shares the word of `A`'s.
                assert_eq!(leaves(e), [(0, 32), (32, 32), (32, 32)]);
                assert_eq!(runtime_size_bytes(&module.ctx, e), Some(64));
            } else {
                // One i8 tag, then both payloads at the i64's offset.
                assert_eq!(leaves(e), [(0, 1), (8, 8), (8, 8)]);
                assert_eq!(runtime_size_bytes(&module.ctx, e), Some(16));
                assert_eq!(leaves(option), [(0, 1), (8, 8)]);
                assert!(compatible(option, pair));
            }
            assert_eq!(
                runtime_size_bytes(&module.ctx, e),
                module.ctx.size_of(e).ok().map(|size| size as u32)
            );
            assert!(!compatible(words, e));
        }
    }

    #[test]
    fn supports_arrays_of_recursive_enum_leaves() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

type @option = enum {
    #Some(i256),
    #None,
};

func private %f() {
block0:
    return;
}
"#,
        );
        let option = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_enum("option").unwrap()));
        let Type::Compound(option_cmpd) = option else {
            panic!("array element must be an enum type");
        };
        let options = module.ctx.with_ty_store_mut(|s| s.make_array(option, 2));
        let option_size = runtime_size_bytes(&module.ctx, option).expect("enum size");
        let shape = aggregate_shape(&module.ctx, options).expect("shape");
        assert!(is_supported_aggregate_ty(&module.ctx, options));
        assert_eq!(shape.leaves.len(), 4);
        assert_eq!(shape.leaves[0].path.as_slice(), &[0, 0]);
        assert_eq!(shape.leaves[0].ty, Type::EnumTag(option_cmpd));
        assert_eq!(shape.leaves[0].offset_bytes, 0);
        assert_eq!(shape.leaves[1].path.as_slice(), &[0, 1]);
        assert_eq!(shape.leaves[1].ty, Type::I256);
        assert_eq!(shape.leaves[1].offset_bytes, 32);
        assert_eq!(shape.leaves[2].path.as_slice(), &[1, 0]);
        assert_eq!(shape.leaves[2].offset_bytes, option_size);
        assert_eq!(shape.leaves[3].path.as_slice(), &[1, 1]);
        assert_eq!(shape.leaves[3].ty, Type::I256);
        assert_eq!(shape.leaves[3].offset_bytes, option_size + 32);
    }

    #[test]
    fn maps_compatible_bitcast_slices_back_to_source_layout() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

type @inner = { i256 };
type @pair = { i256, i256 };
type @nested = { @inner, i256 };

func private %f() {
block0:
    return;
}
"#,
        );
        let pair = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("pair").unwrap()));
        let nested = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("nested").unwrap()));
        let inner = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("inner").unwrap()));

        let nested_inner = aggregate_slice_for_index(&module.ctx, nested, 0).expect("nested field");
        assert_eq!(nested_inner.ty, inner);
        assert_eq!(nested_inner.first_leaf, 0);
        assert_eq!(nested_inner.leaf_count, 1);

        let mut cache = AggregateLayoutCache::default();
        let source_slice = cache
            .compatible_bitcast_source_slice(&module.ctx, pair, nested, nested_inner)
            .expect("source slice");
        assert_eq!(source_slice.ty, Type::I256);
        assert_eq!(source_slice.first_leaf, 0);
        assert_eq!(source_slice.leaf_count, 1);
    }

    #[test]
    fn maps_compatible_bitcast_slices_back_to_source_layout_with_zero_sized_fields() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

type @src = { unit, i256, i256 };
type @dst = { i256, i256 };

func private %f() {
block0:
    return;
}
"#,
        );
        let src = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("src").unwrap()));
        let dst = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("dst").unwrap()));

        let dst_second = aggregate_slice_for_index(&module.ctx, dst, 1).expect("dst second field");
        let dst_whole = aggregate_slice_for_path(&module.ctx, dst, &[]).expect("whole dst");

        let mut cache = AggregateLayoutCache::default();
        let second_source = cache
            .compatible_bitcast_source_slice(&module.ctx, src, dst, dst_second)
            .expect("source slice for second field");
        assert_eq!(second_source.ty, Type::I256);
        assert_eq!(second_source.first_leaf, 2);
        assert_eq!(second_source.leaf_count, 1);

        let whole_source = cache
            .compatible_bitcast_source_slice(&module.ctx, src, dst, dst_whole)
            .expect("whole source slice");
        assert_eq!(whole_source.ty, src);
        assert_eq!(whole_source.first_leaf, 0);
        assert_eq!(whole_source.leaf_count, 3);
    }
}
