use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    DataFlowGraph, Type, U256, ValueId,
    module::ModuleCtx,
    types::{CompoundType, EnumVariantRef},
};

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

    pub fn shape(&mut self, module: &ModuleCtx, ty: Type) -> Option<AggregateShape> {
        if let Some(shape) = self.shape_cache.get(&ty) {
            return Some(shape.clone());
        }

        let shape = self.aggregate_shape(module, ty)?;
        self.shape_cache.insert(ty, shape.clone());
        Some(shape)
    }

    pub fn runtime_leaves(&mut self, module: &ModuleCtx, ty: Type) -> Option<RuntimeLeaves> {
        if let Some(leaves) = self.runtime_leaf_cache.get(&ty) {
            return Some(leaves.clone());
        }

        let leaves: RuntimeLeaves = self
            .shape(module, ty)?
            .leaves
            .into_iter()
            .filter(|leaf| leaf.size_bytes != 0)
            .collect();
        self.runtime_leaf_cache.insert(ty, leaves.clone());
        Some(leaves)
    }

    pub fn single_runtime_word_leaf(
        &mut self,
        module: &ModuleCtx,
        ty: Type,
    ) -> Option<AggregateLeaf> {
        let runtime_leaves = self.runtime_leaves(module, ty)?;
        let [leaf] = runtime_leaves.as_slice() else {
            return None;
        };
        (leaf.size_bytes == 32).then(|| leaf.clone())
    }

    pub fn compatible_bitcast_runtime_leaves(
        &mut self,
        module: &ModuleCtx,
        from_ty: Type,
        to_ty: Type,
    ) -> Option<(RuntimeLeaves, RuntimeLeaves)> {
        let src_leaves = self.runtime_leaves(module, from_ty)?;
        let dst_leaves = self.runtime_leaves(module, to_ty)?;
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

    pub fn compatible_bitcast_source_slice(
        &mut self,
        module: &ModuleCtx,
        from_ty: Type,
        to_ty: Type,
        to_slice: AggregateSlice,
    ) -> Option<AggregateSlice> {
        self.compatible_bitcast_runtime_leaves(module, from_ty, to_ty)?;
        let (first_runtime_leaf, runtime_leaf_count) =
            runtime_leaf_range_for_slice(module, to_ty, to_slice)?;
        aggregate_slice_for_runtime_leaf_range(
            module,
            from_ty,
            first_runtime_leaf,
            runtime_leaf_count,
        )
    }

    pub fn runtime_size_bytes(&mut self, module: &ModuleCtx, ty: Type) -> Option<u32> {
        self.runtime_size_align_bytes(module, ty)
            .map(|(size, _)| size)
    }

    pub fn runtime_size_align_bytes(&mut self, module: &ModuleCtx, ty: Type) -> Option<(u32, u32)> {
        if let Some(size_align) = self.size_align_cache.get(&ty) {
            return *size_align;
        }

        let size_align = self.compute_runtime_size_align_bytes(module, ty);
        self.size_align_cache.insert(ty, size_align);
        size_align
    }

    pub fn is_supported_scalar_shape_ty(&mut self, module: &ModuleCtx, ty: Type) -> bool {
        if let Some(supported) = self.supported_scalar_shape_cache.get(&ty) {
            return *supported;
        }

        let supported = self.compute_is_supported_scalar_shape_ty(module, ty);
        self.supported_scalar_shape_cache.insert(ty, supported);
        supported
    }

    pub fn is_supported_aggregate_ty(&mut self, module: &ModuleCtx, ty: Type) -> bool {
        if let Some(supported) = self.supported_aggregate_cache.get(&ty) {
            return *supported;
        }

        let supported = self.compute_is_supported_aggregate_ty(module, ty);
        self.supported_aggregate_cache.insert(ty, supported);
        supported
    }

    fn compute_is_supported_scalar_shape_ty(&mut self, module: &ModuleCtx, ty: Type) -> bool {
        match ty.resolve_compound(module) {
            Some(CompoundType::Struct(s)) => {
                !s.packed
                    && s.fields
                        .iter()
                        .copied()
                        .all(|field_ty| self.runtime_size_align_bytes(module, field_ty).is_some())
            }
            Some(CompoundType::Array { elem, .. }) => {
                self.runtime_size_align_bytes(module, elem).is_some()
            }
            Some(CompoundType::Enum(data)) => data.variants.iter().all(|variant| {
                variant
                    .fields
                    .iter()
                    .copied()
                    .all(|field_ty| self.runtime_size_align_bytes(module, field_ty).is_some())
            }),
            _ => false,
        }
    }

    fn compute_is_supported_aggregate_ty(&mut self, module: &ModuleCtx, ty: Type) -> bool {
        match ty.resolve_compound(module) {
            Some(CompoundType::Struct(s)) => {
                !s.packed
                    && s.fields
                        .iter()
                        .copied()
                        .all(|field_ty| self.runtime_size_align_bytes(module, field_ty).is_some())
            }
            Some(CompoundType::Array { elem, .. }) => {
                self.runtime_size_align_bytes(module, elem).is_some()
            }
            _ => false,
        }
    }

    pub fn aggregate_slice_for_gep_path(
        &mut self,
        module: &ModuleCtx,
        base_pointee_ty: Type,
        indices: &[ValueId],
        dfg: &DataFlowGraph,
    ) -> Option<AggregateSlice> {
        if !self.is_supported_aggregate_ty(module, base_pointee_ty) {
            return None;
        }
        let (&first, rest) = indices.split_first()?;
        if const_u32(dfg, first)? != 0 {
            return None;
        }

        self.aggregate_slice_for_object_path(module, base_pointee_ty, rest, dfg)
    }

    pub fn aggregate_slice_for_object_path(
        &mut self,
        module: &ModuleCtx,
        root_ty: Type,
        indices: &[ValueId],
        dfg: &DataFlowGraph,
    ) -> Option<AggregateSlice> {
        if !self.is_supported_aggregate_ty(module, root_ty) {
            return None;
        }

        let mut current_ty = root_ty;
        let mut path: FieldPath = smallvec![];
        for &idx_value in indices {
            let idx = usize::try_from(const_u32(dfg, idx_value)?).ok()?;
            match current_ty.resolve_compound(module)? {
                CompoundType::Struct(s) => {
                    if s.packed {
                        return None;
                    }
                    let field_ty = *s.fields.get(idx)?;
                    path.push(u32::try_from(idx).ok()?);
                    current_ty = field_ty;
                }
                CompoundType::Array { elem, len } => {
                    if idx >= len {
                        return None;
                    }
                    path.push(u32::try_from(idx).ok()?);
                    current_ty = elem;
                }
                CompoundType::Enum(_)
                | CompoundType::Ptr(_)
                | CompoundType::ObjRef(_)
                | CompoundType::ConstRef(_)
                | CompoundType::Func { .. } => return None,
            }
        }

        self.aggregate_slice_for_path(module, root_ty, &path)
    }

    pub fn enum_variant_field_slice(
        &mut self,
        module: &ModuleCtx,
        enum_ty: Type,
        variant: EnumVariantRef,
        field: u32,
    ) -> Option<AggregateSlice> {
        self.aggregate_slice_for_index(
            module,
            enum_ty,
            enum_variant_field_slot(module, variant, field)?,
        )
    }

    fn aggregate_shape(&mut self, module: &ModuleCtx, ty: Type) -> Option<AggregateShape> {
        if !self.is_supported_scalar_shape_ty(module, ty) {
            return None;
        }

        let mut leaves: SmallVec<[AggregateLeaf; 4]> = SmallVec::new();
        let mut path: FieldPath = SmallVec::new();
        self.flatten_aggregate(module, ty, 0, &mut path, &mut leaves)?;

        Some(AggregateShape {
            root_ty: ty,
            leaves,
        })
    }

    fn aggregate_slice_for_index(
        &mut self,
        module: &ModuleCtx,
        agg_ty: Type,
        idx: u32,
    ) -> Option<AggregateSlice> {
        self.aggregate_slice_for_path(module, agg_ty, &[idx])
    }

    fn aggregate_slice_for_path(
        &mut self,
        module: &ModuleCtx,
        root_ty: Type,
        path: &[u32],
    ) -> Option<AggregateSlice> {
        let path: FieldPath = path.iter().copied().collect();
        if let Some(slice) = self.slice_path_cache.get(&(root_ty, path.clone())) {
            return *slice;
        }

        let slice = if self.is_supported_scalar_shape_ty(module, root_ty) {
            self.aggregate_slice_info(module, root_ty, &path)
                .map(|(ty, first_leaf, leaf_count)| AggregateSlice {
                    ty,
                    first_leaf,
                    leaf_count,
                })
        } else {
            None
        };
        self.slice_path_cache.insert((root_ty, path), slice);
        slice
    }

    fn aggregate_slice_info(
        &mut self,
        module: &ModuleCtx,
        ty: Type,
        path: &[u32],
    ) -> Option<(Type, usize, usize)> {
        if path.is_empty() {
            return Some((ty, 0, self.flattened_leaf_count(module, ty)?));
        }

        let idx = usize::try_from(path[0]).ok()?;
        match ty.resolve_compound(module)? {
            CompoundType::Struct(s) => {
                if s.packed {
                    return None;
                }

                let child_ty = *s.fields.get(idx)?;
                let mut first_leaf = 0usize;
                for &field_ty in s.fields.iter().take(idx) {
                    first_leaf =
                        first_leaf.checked_add(self.flattened_leaf_count(module, field_ty)?)?;
                }

                let (nested_ty, nested_first_leaf, leaf_count) =
                    self.aggregate_slice_info(module, child_ty, &path[1..])?;
                Some((
                    nested_ty,
                    first_leaf.checked_add(nested_first_leaf)?,
                    leaf_count,
                ))
            }
            CompoundType::Array { elem, len } => {
                if idx >= len {
                    return None;
                }

                let elem_leaf_count = self.flattened_leaf_count(module, elem)?;
                let first_leaf = elem_leaf_count.checked_mul(idx)?;
                let (nested_ty, nested_first_leaf, leaf_count) =
                    self.aggregate_slice_info(module, elem, &path[1..])?;
                Some((
                    nested_ty,
                    first_leaf.checked_add(nested_first_leaf)?,
                    leaf_count,
                ))
            }
            CompoundType::Enum(_) => {
                let slot = enum_slot_info(module, ty, path[0])?;
                match slot {
                    EnumSlotInfo::Tag { ty: tag_ty } => (path.len() == 1).then_some((tag_ty, 0, 1)),
                    EnumSlotInfo::VariantField {
                        variant,
                        field,
                        ty: field_ty,
                    } => {
                        let first_leaf =
                            self.enum_variant_field_first_leaf(module, ty, variant, field)?;
                        let (nested_ty, nested_first_leaf, leaf_count) =
                            self.aggregate_slice_info(module, field_ty, &path[1..])?;
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
        module: &ModuleCtx,
        enum_ty: Type,
        variant: EnumVariantRef,
        field: u32,
    ) -> Option<usize> {
        let slot = usize::try_from(enum_variant_field_slot(module, variant, field)?).ok()?;
        let mut first_leaf = 0usize;
        for idx in 0..slot {
            let child_ty = aggregate_child_ty(module, enum_ty, u32::try_from(idx).ok()?)?;
            first_leaf = first_leaf.checked_add(self.flattened_leaf_count(module, child_ty)?)?;
        }
        Some(first_leaf)
    }

    fn flattened_leaf_count(&mut self, module: &ModuleCtx, ty: Type) -> Option<usize> {
        if let Some(count) = self.flattened_leaf_count_cache.get(&ty) {
            return *count;
        }

        let count = self.compute_flattened_leaf_count(module, ty);
        self.flattened_leaf_count_cache.insert(ty, count);
        count
    }

    fn struct_field_offset_bytes(
        &mut self,
        fields: &[Type],
        packed: bool,
        idx: usize,
        module: &ModuleCtx,
    ) -> Option<(u32, Type)> {
        if packed {
            return None;
        }
        let &field_ty = fields.get(idx)?;
        let mut offset = 0u32;

        for &ty in fields.iter().take(idx) {
            let (_, align) = self.runtime_size_align_bytes(module, ty)?;
            offset = align_to(offset, align)?;

            let (size, _) = self.runtime_size_align_bytes(module, ty)?;
            offset = offset.checked_add(size)?;
        }

        let (_, align) = self.runtime_size_align_bytes(module, field_ty)?;
        offset = align_to(offset, align)?;
        Some((offset, field_ty))
    }

    fn flatten_aggregate(
        &mut self,
        module: &ModuleCtx,
        ty: Type,
        base_offset: u32,
        path: &mut FieldPath,
        out: &mut SmallVec<[AggregateLeaf; 4]>,
    ) -> Option<()> {
        match ty.resolve_compound(module) {
            Some(CompoundType::Struct(s)) => {
                if s.packed {
                    return None;
                }

                for (idx, &field_ty) in s.fields.iter().enumerate() {
                    let (field_offset, _) =
                        self.struct_field_offset_bytes(&s.fields, s.packed, idx, module)?;
                    let total_offset = base_offset.checked_add(field_offset)?;

                    path.push(u32::try_from(idx).ok()?);
                    self.flatten_aggregate(module, field_ty, total_offset, path, out)?;
                    path.pop();
                }
                Some(())
            }
            Some(CompoundType::Array { elem, len }) => {
                let elem_size = self.runtime_size_bytes(module, elem)?;
                for idx in 0..len {
                    let offset = elem_size.checked_mul(u32::try_from(idx).ok()?)?;
                    let total_offset = base_offset.checked_add(offset)?;
                    path.push(u32::try_from(idx).ok()?);
                    self.flatten_aggregate(module, elem, total_offset, path, out)?;
                    path.pop();
                }
                Some(())
            }
            Some(CompoundType::Enum(data)) => {
                let tag_ty = enum_tag_ty(ty)?;
                let tag_size = self.runtime_size_bytes(module, tag_ty)?;
                path.push(0);
                out.push(AggregateLeaf {
                    path: path.clone(),
                    ty: tag_ty,
                    offset_bytes: base_offset,
                    size_bytes: tag_size,
                });
                path.pop();

                let mut slot = 1u32;
                let mut offset = base_offset.checked_add(tag_size)?;
                for variant in &data.variants {
                    for &field_ty in &variant.fields {
                        let (field_size, field_align) =
                            self.runtime_size_align_bytes(module, field_ty)?;
                        offset = align_to(offset, field_align)?;
                        path.push(slot);
                        self.flatten_aggregate(module, field_ty, offset, path, out)?;
                        path.pop();
                        offset = offset.checked_add(field_size)?;
                        slot = slot.checked_add(1)?;
                    }
                }
                Some(())
            }
            Some(CompoundType::Ptr(_))
            | Some(CompoundType::ObjRef(_))
            | Some(CompoundType::ConstRef(_))
            | None => {
                let size = self.runtime_size_bytes(module, ty)?;
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

    fn compute_flattened_leaf_count(&mut self, module: &ModuleCtx, ty: Type) -> Option<usize> {
        match ty.resolve_compound(module) {
            Some(CompoundType::Struct(s)) => {
                if s.packed {
                    return None;
                }

                let mut count = 0usize;
                for &field_ty in &s.fields {
                    count = count.checked_add(self.flattened_leaf_count(module, field_ty)?)?;
                }
                Some(count)
            }
            Some(CompoundType::Array { elem, len }) => {
                self.flattened_leaf_count(module, elem)?.checked_mul(len)
            }
            Some(CompoundType::Enum(data)) => {
                let mut count = 1usize;
                for variant in &data.variants {
                    for &field_ty in &variant.fields {
                        count = count.checked_add(self.flattened_leaf_count(module, field_ty)?)?;
                    }
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

    fn compute_runtime_size_align_bytes(
        &mut self,
        module: &ModuleCtx,
        ty: Type,
    ) -> Option<(u32, u32)> {
        if ty.is_enum_tag() {
            let word_ty = module.type_layout.pointer_repl();
            let size = u32::try_from(module.size_of(word_ty).ok()?).ok()?;
            let align = u32::try_from(module.align_of(word_ty).ok()?).ok()?;
            return Some((size, align));
        }

        match ty.resolve_compound(module) {
            Some(CompoundType::Struct(s)) => {
                if s.packed {
                    return None;
                }

                let mut size = 0u32;
                let mut align = 1u32;
                for &field_ty in &s.fields {
                    let (field_size, field_align) =
                        self.runtime_size_align_bytes(module, field_ty)?;
                    size = align_to(size, field_align)?;
                    size = size.checked_add(field_size)?;
                    align = align.max(field_align);
                }
                Some((size, align))
            }
            Some(CompoundType::Array { elem, len }) => {
                let (elem_size, elem_align) = self.runtime_size_align_bytes(module, elem)?;
                Some((elem_size.checked_mul(u32::try_from(len).ok()?)?, elem_align))
            }
            Some(CompoundType::Enum(_)) => {
                let size = u32::try_from(module.size_of(ty).ok()?).ok()?;
                let align = u32::try_from(module.align_of(ty).ok()?).ok()?;
                Some((size, align))
            }
            Some(CompoundType::Func { .. }) => None,
            Some(CompoundType::Ptr(_))
            | Some(CompoundType::ObjRef(_))
            | Some(CompoundType::ConstRef(_)) => {
                let word_ty = module.type_layout.pointer_repl();
                let size = u32::try_from(module.size_of(word_ty).ok()?).ok()?;
                let align = u32::try_from(module.align_of(word_ty).ok()?).ok()?;
                Some((size, align))
            }
            None => {
                let size = u32::try_from(module.size_of(ty).ok()?).ok()?;
                let align = u32::try_from(module.align_of(ty).ok()?).ok()?;
                Some((size, align))
            }
        }
    }
}

pub fn aggregate_shape(module: &ModuleCtx, ty: Type) -> Option<AggregateShape> {
    if !is_supported_scalar_shape_ty(module, ty) {
        return None;
    }

    let mut leaves: SmallVec<[AggregateLeaf; 4]> = SmallVec::new();
    let mut path: FieldPath = SmallVec::new();
    flatten_aggregate(module, ty, 0, &mut path, &mut leaves)?;

    Some(AggregateShape {
        root_ty: ty,
        leaves,
    })
}

pub fn aggregate_runtime_leaves(module: &ModuleCtx, ty: Type) -> Option<RuntimeLeaves> {
    Some(
        aggregate_shape(module, ty)?
            .leaves
            .into_iter()
            .filter(|leaf| leaf.size_bytes != 0)
            .collect(),
    )
}

pub fn aggregate_single_runtime_word_leaf(module: &ModuleCtx, ty: Type) -> Option<AggregateLeaf> {
    let runtime_leaves = aggregate_runtime_leaves(module, ty)?;
    let [leaf] = runtime_leaves.as_slice() else {
        return None;
    };
    (leaf.size_bytes == 32).then(|| leaf.clone())
}

pub fn compatible_aggregate_bitcast_runtime_leaves(
    module: &ModuleCtx,
    from_ty: Type,
    to_ty: Type,
) -> Option<(RuntimeLeaves, RuntimeLeaves)> {
    let src_leaves = aggregate_runtime_leaves(module, from_ty)?;
    let dst_leaves = aggregate_runtime_leaves(module, to_ty)?;
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

pub fn runtime_leaf_range_for_slice(
    module: &ModuleCtx,
    root_ty: Type,
    slice: AggregateSlice,
) -> Option<(usize, usize)> {
    if !is_supported_scalar_shape_ty(module, root_ty) {
        return None;
    }

    let total_leaf_count = flattened_leaf_count(module, root_ty)?;
    let slice_end = slice.first_leaf.checked_add(slice.leaf_count)?;
    if slice_end > total_leaf_count {
        return None;
    }

    let shape = aggregate_shape(module, root_ty)?;
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

pub fn aggregate_slice_for_index(
    module: &ModuleCtx,
    agg_ty: Type,
    idx: u32,
) -> Option<AggregateSlice> {
    aggregate_slice_for_path(module, agg_ty, &[idx])
}

pub fn aggregate_slice_for_path(
    module: &ModuleCtx,
    root_ty: Type,
    path: &[u32],
) -> Option<AggregateSlice> {
    if !is_supported_scalar_shape_ty(module, root_ty) {
        return None;
    }

    let (ty, first_leaf, leaf_count) = aggregate_slice_info(module, root_ty, path)?;
    Some(AggregateSlice {
        ty,
        first_leaf,
        leaf_count,
    })
}

pub fn aggregate_slice_for_leaf_range(
    module: &ModuleCtx,
    root_ty: Type,
    first_leaf: usize,
    leaf_count: usize,
) -> Option<AggregateSlice> {
    if !is_supported_scalar_shape_ty(module, root_ty) {
        return None;
    }

    let total_leaf_count = flattened_leaf_count(module, root_ty)?;
    if first_leaf.checked_add(leaf_count)? > total_leaf_count {
        return None;
    }
    if first_leaf == 0 && leaf_count == total_leaf_count {
        return Some(AggregateSlice {
            ty: root_ty,
            first_leaf: 0,
            leaf_count,
        });
    }

    aggregate_slice_for_leaf_range_impl(module, root_ty, first_leaf, leaf_count, 0)
}

pub fn aggregate_slice_for_runtime_leaf_range(
    module: &ModuleCtx,
    root_ty: Type,
    first_runtime_leaf: usize,
    target_runtime_leaf_count: usize,
) -> Option<AggregateSlice> {
    if !is_supported_scalar_shape_ty(module, root_ty) {
        return None;
    }

    let total_runtime_leaf_count = runtime_leaf_count_for_ty(module, root_ty)?;
    if first_runtime_leaf.checked_add(target_runtime_leaf_count)? > total_runtime_leaf_count {
        return None;
    }
    if target_runtime_leaf_count == 0 {
        return Some(AggregateSlice {
            ty: root_ty,
            first_leaf: flattened_leaf_boundary_for_runtime_leaf(
                module,
                root_ty,
                first_runtime_leaf,
            )?,
            leaf_count: 0,
        });
    }

    let total_leaf_count = flattened_leaf_count(module, root_ty)?;
    if first_runtime_leaf == 0 && target_runtime_leaf_count == total_runtime_leaf_count {
        return Some(AggregateSlice {
            ty: root_ty,
            first_leaf: 0,
            leaf_count: total_leaf_count,
        });
    }

    aggregate_slice_for_runtime_leaf_range_impl(
        module,
        root_ty,
        first_runtime_leaf,
        target_runtime_leaf_count,
        0,
        0,
    )
}

pub fn aggregate_slice_for_gep_path(
    module: &ModuleCtx,
    base_pointee_ty: Type,
    indices: &[ValueId],
    dfg: &DataFlowGraph,
) -> Option<AggregateSlice> {
    if !is_supported_aggregate_ty(module, base_pointee_ty) {
        return None;
    }
    let (&first, rest) = indices.split_first()?;
    if const_u32(dfg, first)? != 0 {
        return None;
    }

    let mut current_ty = base_pointee_ty;
    let mut path: FieldPath = smallvec![];
    for &idx_value in rest {
        let idx = const_u32(dfg, idx_value)? as usize;
        let cmpd = current_ty.resolve_compound(module)?;
        match cmpd {
            CompoundType::Struct(s) => {
                if s.packed {
                    return None;
                }
                let field_ty = *s.fields.get(idx)?;
                path.push(u32::try_from(idx).ok()?);
                current_ty = field_ty;
            }
            CompoundType::Array { elem, len } => {
                if idx >= len {
                    return None;
                }
                path.push(u32::try_from(idx).ok()?);
                current_ty = elem;
            }
            CompoundType::Enum(_) => {
                return None;
            }
            CompoundType::Ptr(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => {
                return None;
            }
        }
    }

    aggregate_slice_for_path(module, base_pointee_ty, &path)
}

pub fn aggregate_slice_for_object_path(
    module: &ModuleCtx,
    root_ty: Type,
    indices: &[ValueId],
    dfg: &DataFlowGraph,
) -> Option<AggregateSlice> {
    if !is_supported_aggregate_ty(module, root_ty) {
        return None;
    }

    let mut current_ty = root_ty;
    let mut path: FieldPath = smallvec![];
    for &idx_value in indices {
        let idx = usize::try_from(const_u32(dfg, idx_value)?).ok()?;
        match current_ty.resolve_compound(module)? {
            CompoundType::Struct(s) => {
                if s.packed {
                    return None;
                }
                let field_ty = *s.fields.get(idx)?;
                path.push(u32::try_from(idx).ok()?);
                current_ty = field_ty;
            }
            CompoundType::Array { elem, len } => {
                if idx >= len {
                    return None;
                }
                path.push(u32::try_from(idx).ok()?);
                current_ty = elem;
            }
            CompoundType::Enum(_) => {
                return None;
            }
            CompoundType::Ptr(_)
            | CompoundType::ObjRef(_)
            | CompoundType::ConstRef(_)
            | CompoundType::Func { .. } => {
                return None;
            }
        }
    }

    aggregate_slice_for_path(module, root_ty, &path)
}

pub fn aggregate_child_ty(module: &ModuleCtx, agg_ty: Type, idx: u32) -> Option<Type> {
    let idx = usize::try_from(idx).ok()?;
    match agg_ty.resolve_compound(module)? {
        CompoundType::Struct(s) => (!s.packed).then_some(*s.fields.get(idx)?),
        CompoundType::Array { elem, len } => (idx < len).then_some(elem),
        CompoundType::Enum(_) => {
            enum_slot_info(module, agg_ty, u32::try_from(idx).ok()?).map(|slot| slot.ty())
        }
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Func { .. } => None,
    }
}

pub fn aggregate_child_count(module: &ModuleCtx, agg_ty: Type) -> Option<usize> {
    match agg_ty.resolve_compound(module)? {
        CompoundType::Struct(s) => (!s.packed).then_some(s.fields.len()),
        CompoundType::Array { len, .. } => Some(len),
        CompoundType::Enum(_) => enum_child_count(module, agg_ty),
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Func { .. } => None,
    }
}

pub fn struct_field_offset_bytes(
    fields: &[Type],
    packed: bool,
    idx: usize,
    module: &ModuleCtx,
) -> Option<(u32, Type)> {
    if packed {
        return None;
    }
    let &field_ty = fields.get(idx)?;
    let mut offset = 0u32;

    for &ty in fields.iter().take(idx) {
        let (_, align) = runtime_size_align_bytes(module, ty)?;
        offset = align_to(offset, align)?;

        let (size, _) = runtime_size_align_bytes(module, ty)?;
        offset = offset.checked_add(size)?;
    }

    let (_, align) = runtime_size_align_bytes(module, field_ty)?;
    offset = align_to(offset, align)?;
    Some((offset, field_ty))
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
    match ty.resolve_compound(module) {
        Some(CompoundType::Struct(s)) => {
            !s.packed
                && s.fields
                    .iter()
                    .copied()
                    .all(|field_ty| runtime_size_align_bytes(module, field_ty).is_some())
        }
        Some(CompoundType::Array { elem, .. }) => runtime_size_align_bytes(module, elem).is_some(),
        _ => false,
    }
}

/// Returns whether `ty` can be flattened into runtime leaves for scalar-shape
/// transforms.
///
/// This is broader than [`is_supported_aggregate_ty`]: it includes enums so
/// enum-bearing structs and arrays can still participate in scalar-shape
/// analyses, even though enums are not generic aggregate-op destinations.
pub fn is_supported_scalar_shape_ty(module: &ModuleCtx, ty: Type) -> bool {
    match ty.resolve_compound(module) {
        Some(CompoundType::Struct(s)) => {
            !s.packed
                && s.fields
                    .iter()
                    .copied()
                    .all(|field_ty| runtime_size_align_bytes(module, field_ty).is_some())
        }
        Some(CompoundType::Array { elem, .. }) => runtime_size_align_bytes(module, elem).is_some(),
        Some(CompoundType::Enum(data)) => data.variants.iter().all(|variant| {
            variant
                .fields
                .iter()
                .copied()
                .all(|field_ty| runtime_size_align_bytes(module, field_ty).is_some())
        }),
        _ => false,
    }
}

/// Returns whether `ty` can always be rebuilt from an arbitrary runtime leaf
/// slice without value-dependent reconstruction.
///
/// This is stricter than [`is_supported_scalar_shape_ty`]. Enums, and aggregates
/// containing enums, are excluded because rebuilding a full value from arbitrary
/// leaf SSA state would require recovering the active variant from dynamic tag
/// leaves.
pub fn is_leaf_reifiable_ty(module: &ModuleCtx, ty: Type) -> bool {
    match ty.resolve_compound(module) {
        Some(CompoundType::Struct(s)) => {
            !s.packed
                && s.fields
                    .iter()
                    .copied()
                    .all(|field| is_leaf_reifiable_ty(module, field))
        }
        Some(CompoundType::Array { elem, .. }) => is_leaf_reifiable_ty(module, elem),
        Some(CompoundType::Enum(_)) => false,
        _ => true,
    }
}

pub fn runtime_size_bytes(module: &ModuleCtx, ty: Type) -> Option<u32> {
    runtime_size_align_bytes(module, ty).map(|(size, _)| size)
}

fn runtime_size_align_bytes(module: &ModuleCtx, ty: Type) -> Option<(u32, u32)> {
    if ty.is_enum_tag() {
        let word_ty = module.type_layout.pointer_repl();
        let size = u32::try_from(module.size_of(word_ty).ok()?).ok()?;
        let align = u32::try_from(module.align_of(word_ty).ok()?).ok()?;
        return Some((size, align));
    }

    match ty.resolve_compound(module) {
        Some(CompoundType::Struct(s)) => {
            if s.packed {
                return None;
            }

            let mut size = 0u32;
            let mut align = 1u32;
            for &field_ty in &s.fields {
                let (field_size, field_align) = runtime_size_align_bytes(module, field_ty)?;
                size = align_to(size, field_align)?;
                size = size.checked_add(field_size)?;
                align = align.max(field_align);
            }
            Some((size, align))
        }
        Some(CompoundType::Array { elem, len }) => {
            let (elem_size, elem_align) = runtime_size_align_bytes(module, elem)?;
            Some((elem_size.checked_mul(u32::try_from(len).ok()?)?, elem_align))
        }
        Some(CompoundType::Enum(_)) => {
            let size = u32::try_from(module.size_of(ty).ok()?).ok()?;
            let align = u32::try_from(module.align_of(ty).ok()?).ok()?;
            Some((size, align))
        }
        Some(CompoundType::Func { .. }) => None,
        Some(CompoundType::Ptr(_))
        | Some(CompoundType::ObjRef(_))
        | Some(CompoundType::ConstRef(_)) => {
            let word_ty = module.type_layout.pointer_repl();
            let size = u32::try_from(module.size_of(word_ty).ok()?).ok()?;
            let align = u32::try_from(module.align_of(word_ty).ok()?).ok()?;
            Some((size, align))
        }
        None => {
            let size = u32::try_from(module.size_of(ty).ok()?).ok()?;
            let align = u32::try_from(module.align_of(ty).ok()?).ok()?;
            Some((size, align))
        }
    }
}

fn aggregate_slice_info(
    module: &ModuleCtx,
    ty: Type,
    path: &[u32],
) -> Option<(Type, usize, usize)> {
    if path.is_empty() {
        return Some((ty, 0, flattened_leaf_count(module, ty)?));
    }

    let idx = usize::try_from(path[0]).ok()?;
    match ty.resolve_compound(module)? {
        CompoundType::Struct(s) => {
            if s.packed {
                return None;
            }

            let child_ty = *s.fields.get(idx)?;
            let mut first_leaf = 0usize;
            for &field_ty in s.fields.iter().take(idx) {
                first_leaf = first_leaf.checked_add(flattened_leaf_count(module, field_ty)?)?;
            }

            let (nested_ty, nested_first_leaf, leaf_count) =
                aggregate_slice_info(module, child_ty, &path[1..])?;
            Some((
                nested_ty,
                first_leaf.checked_add(nested_first_leaf)?,
                leaf_count,
            ))
        }
        CompoundType::Array { elem, len } => {
            if idx >= len {
                return None;
            }

            let elem_leaf_count = flattened_leaf_count(module, elem)?;
            let first_leaf = elem_leaf_count.checked_mul(idx)?;
            let (nested_ty, nested_first_leaf, leaf_count) =
                aggregate_slice_info(module, elem, &path[1..])?;
            Some((
                nested_ty,
                first_leaf.checked_add(nested_first_leaf)?,
                leaf_count,
            ))
        }
        CompoundType::Enum(_) => {
            let slot = enum_slot_info(module, ty, path[0])?;
            match slot {
                EnumSlotInfo::Tag { ty: tag_ty } => (path.len() == 1).then_some((tag_ty, 0, 1)),
                EnumSlotInfo::VariantField {
                    variant,
                    field,
                    ty: field_ty,
                } => {
                    let first_leaf = enum_variant_field_first_leaf(module, ty, variant, field)?;
                    let (nested_ty, nested_first_leaf, leaf_count) =
                        aggregate_slice_info(module, field_ty, &path[1..])?;
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

fn aggregate_slice_for_leaf_range_impl(
    module: &ModuleCtx,
    ty: Type,
    target_first_leaf: usize,
    target_leaf_count: usize,
    base_first_leaf: usize,
) -> Option<AggregateSlice> {
    match ty.resolve_compound(module)? {
        CompoundType::Struct(s) => {
            if s.packed {
                return None;
            }

            let mut child_first_leaf = base_first_leaf;
            for &field_ty in &s.fields {
                let child_leaf_count = flattened_leaf_count(module, field_ty)?;
                if child_first_leaf == target_first_leaf && child_leaf_count == target_leaf_count {
                    return Some(AggregateSlice {
                        ty: field_ty,
                        first_leaf: target_first_leaf,
                        leaf_count: target_leaf_count,
                    });
                }
                if target_first_leaf >= child_first_leaf
                    && target_first_leaf + target_leaf_count <= child_first_leaf + child_leaf_count
                    && let Some(slice) = aggregate_slice_for_leaf_range_impl(
                        module,
                        field_ty,
                        target_first_leaf,
                        target_leaf_count,
                        child_first_leaf,
                    )
                {
                    return Some(slice);
                }
                child_first_leaf = child_first_leaf.checked_add(child_leaf_count)?;
            }
            None
        }
        CompoundType::Array { elem, len } => {
            let elem_leaf_count = flattened_leaf_count(module, elem)?;
            let mut child_first_leaf = base_first_leaf;
            for _ in 0..len {
                if child_first_leaf == target_first_leaf && elem_leaf_count == target_leaf_count {
                    return Some(AggregateSlice {
                        ty: elem,
                        first_leaf: target_first_leaf,
                        leaf_count: target_leaf_count,
                    });
                }
                if target_first_leaf >= child_first_leaf
                    && target_first_leaf + target_leaf_count <= child_first_leaf + elem_leaf_count
                    && let Some(slice) = aggregate_slice_for_leaf_range_impl(
                        module,
                        elem,
                        target_first_leaf,
                        target_leaf_count,
                        child_first_leaf,
                    )
                {
                    return Some(slice);
                }
                child_first_leaf = child_first_leaf.checked_add(elem_leaf_count)?;
            }
            None
        }
        CompoundType::Enum(_) => {
            if target_first_leaf == base_first_leaf && target_leaf_count == 1 {
                return Some(AggregateSlice {
                    ty: enum_tag_ty(ty)?,
                    first_leaf: target_first_leaf,
                    leaf_count: target_leaf_count,
                });
            }

            let Type::Compound(enum_ty) = ty else {
                return None;
            };
            let data = module.with_ty_store(|store| store.enum_data(enum_ty).cloned())?;
            let mut child_first_leaf = base_first_leaf.checked_add(1)?;
            for variant_data in &data.variants {
                for &field_ty in &variant_data.fields {
                    let child_leaf_count = flattened_leaf_count(module, field_ty)?;
                    if child_first_leaf == target_first_leaf
                        && child_leaf_count == target_leaf_count
                    {
                        return Some(AggregateSlice {
                            ty: field_ty,
                            first_leaf: target_first_leaf,
                            leaf_count: target_leaf_count,
                        });
                    }
                    if target_first_leaf >= child_first_leaf
                        && target_first_leaf + target_leaf_count
                            <= child_first_leaf + child_leaf_count
                        && let Some(slice) = aggregate_slice_for_leaf_range_impl(
                            module,
                            field_ty,
                            target_first_leaf,
                            target_leaf_count,
                            child_first_leaf,
                        )
                    {
                        return Some(slice);
                    }
                    child_first_leaf = child_first_leaf.checked_add(child_leaf_count)?;
                }
            }
            None
        }
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Func { .. } => None,
    }
}

fn aggregate_slice_for_runtime_leaf_range_impl(
    module: &ModuleCtx,
    ty: Type,
    target_first_runtime_leaf: usize,
    target_runtime_leaf_count: usize,
    base_first_leaf: usize,
    base_first_runtime_leaf: usize,
) -> Option<AggregateSlice> {
    match ty.resolve_compound(module)? {
        CompoundType::Struct(s) => {
            if s.packed {
                return None;
            }

            let mut child_first_leaf = base_first_leaf;
            let mut child_first_runtime_leaf = base_first_runtime_leaf;
            for &field_ty in &s.fields {
                let child_leaf_count = flattened_leaf_count(module, field_ty)?;
                let child_runtime_leaf_count = runtime_leaf_count_for_ty(module, field_ty)?;
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
                    && let Some(slice) = aggregate_slice_for_runtime_leaf_range_impl(
                        module,
                        field_ty,
                        target_first_runtime_leaf,
                        target_runtime_leaf_count,
                        child_first_leaf,
                        child_first_runtime_leaf,
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
            let elem_leaf_count = flattened_leaf_count(module, elem)?;
            let elem_runtime_leaf_count = runtime_leaf_count_for_ty(module, elem)?;
            let mut child_first_leaf = base_first_leaf;
            let mut child_first_runtime_leaf = base_first_runtime_leaf;
            for _ in 0..len {
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
                    && let Some(slice) = aggregate_slice_for_runtime_leaf_range_impl(
                        module,
                        elem,
                        target_first_runtime_leaf,
                        target_runtime_leaf_count,
                        child_first_leaf,
                        child_first_runtime_leaf,
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
        CompoundType::Enum(_) => {
            if target_first_runtime_leaf == base_first_runtime_leaf
                && target_runtime_leaf_count == 1
            {
                return Some(AggregateSlice {
                    ty: enum_tag_ty(ty)?,
                    first_leaf: base_first_leaf,
                    leaf_count: 1,
                });
            }

            let Type::Compound(enum_ty) = ty else {
                return None;
            };
            let data = module.with_ty_store(|store| store.enum_data(enum_ty).cloned())?;
            let mut child_first_leaf = base_first_leaf.checked_add(1)?;
            let mut child_first_runtime_leaf = base_first_runtime_leaf.checked_add(1)?;
            for variant_data in &data.variants {
                for &field_ty in &variant_data.fields {
                    let child_leaf_count = flattened_leaf_count(module, field_ty)?;
                    let child_runtime_leaf_count = runtime_leaf_count_for_ty(module, field_ty)?;
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
                        && let Some(slice) = aggregate_slice_for_runtime_leaf_range_impl(
                            module,
                            field_ty,
                            target_first_runtime_leaf,
                            target_runtime_leaf_count,
                            child_first_leaf,
                            child_first_runtime_leaf,
                        )
                    {
                        return Some(slice);
                    }
                    child_first_leaf = child_first_leaf.checked_add(child_leaf_count)?;
                    child_first_runtime_leaf =
                        child_first_runtime_leaf.checked_add(child_runtime_leaf_count)?;
                }
            }
            None
        }
        CompoundType::Ptr(_)
        | CompoundType::ObjRef(_)
        | CompoundType::ConstRef(_)
        | CompoundType::Func { .. } => None,
    }
}

fn flattened_leaf_count(module: &ModuleCtx, ty: Type) -> Option<usize> {
    match ty.resolve_compound(module) {
        Some(CompoundType::Struct(s)) => {
            if s.packed {
                return None;
            }

            let mut count = 0usize;
            for &field_ty in &s.fields {
                count = count.checked_add(flattened_leaf_count(module, field_ty)?)?;
            }
            Some(count)
        }
        Some(CompoundType::Array { elem, len }) => {
            flattened_leaf_count(module, elem)?.checked_mul(len)
        }
        Some(CompoundType::Enum(data)) => {
            let mut count = 1usize;
            for variant in &data.variants {
                for &field_ty in &variant.fields {
                    count = count.checked_add(flattened_leaf_count(module, field_ty)?)?;
                }
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

fn runtime_leaf_count_for_ty(module: &ModuleCtx, ty: Type) -> Option<usize> {
    match ty.resolve_compound(module) {
        Some(CompoundType::Struct(s)) => {
            if s.packed {
                return None;
            }

            let mut count = 0usize;
            for &field_ty in &s.fields {
                count = count.checked_add(runtime_leaf_count_for_ty(module, field_ty)?)?;
            }
            Some(count)
        }
        Some(CompoundType::Array { elem, len }) => {
            runtime_leaf_count_for_ty(module, elem)?.checked_mul(len)
        }
        Some(CompoundType::Enum(data)) => {
            let mut count = 1usize;
            for variant in &data.variants {
                for &field_ty in &variant.fields {
                    count = count.checked_add(runtime_leaf_count_for_ty(module, field_ty)?)?;
                }
            }
            Some(count)
        }
        Some(CompoundType::Func { .. }) => None,
        Some(CompoundType::Ptr(_))
        | Some(CompoundType::ObjRef(_))
        | Some(CompoundType::ConstRef(_))
        | None => Some(usize::from(runtime_size_bytes(module, ty)? != 0)),
    }
}

fn flattened_leaf_boundary_for_runtime_leaf(
    module: &ModuleCtx,
    root_ty: Type,
    runtime_leaf_boundary: usize,
) -> Option<usize> {
    let shape = aggregate_shape(module, root_ty)?;
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

fn flatten_aggregate(
    module: &ModuleCtx,
    ty: Type,
    base_offset: u32,
    path: &mut FieldPath,
    out: &mut SmallVec<[AggregateLeaf; 4]>,
) -> Option<()> {
    match ty.resolve_compound(module) {
        Some(CompoundType::Struct(s)) => {
            if s.packed {
                return None;
            }

            for (idx, &field_ty) in s.fields.iter().enumerate() {
                let (field_offset, _) =
                    struct_field_offset_bytes(&s.fields, s.packed, idx, module)?;
                let total_offset = base_offset.checked_add(field_offset)?;

                path.push(u32::try_from(idx).ok()?);
                flatten_aggregate(module, field_ty, total_offset, path, out)?;
                path.pop();
            }
            Some(())
        }
        Some(CompoundType::Array { elem, len }) => {
            let elem_size = runtime_size_bytes(module, elem)?;
            for idx in 0..len {
                let offset = elem_size.checked_mul(u32::try_from(idx).ok()?)?;
                let total_offset = base_offset.checked_add(offset)?;
                path.push(u32::try_from(idx).ok()?);
                flatten_aggregate(module, elem, total_offset, path, out)?;
                path.pop();
            }
            Some(())
        }
        Some(CompoundType::Enum(data)) => {
            let tag_ty = enum_tag_ty(ty)?;
            let tag_size = runtime_size_bytes(module, tag_ty)?;
            path.push(0);
            out.push(AggregateLeaf {
                path: path.clone(),
                ty: tag_ty,
                offset_bytes: base_offset,
                size_bytes: tag_size,
            });
            path.pop();

            let Type::Compound(_enum_ty) = ty else {
                return None;
            };
            let mut slot = 1u32;
            let mut offset = base_offset.checked_add(tag_size)?;
            for variant in &data.variants {
                for &field_ty in &variant.fields {
                    let (field_size, field_align) = runtime_size_align_bytes(module, field_ty)?;
                    offset = align_to(offset, field_align)?;
                    path.push(slot);
                    flatten_aggregate(module, field_ty, offset, path, out)?;
                    path.pop();
                    offset = offset.checked_add(field_size)?;
                    slot = slot.checked_add(1)?;
                }
            }
            Some(())
        }
        Some(CompoundType::Ptr(_))
        | Some(CompoundType::ObjRef(_))
        | Some(CompoundType::ConstRef(_))
        | None => {
            let size = runtime_size_bytes(module, ty)?;
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

pub fn enum_tag_ty(ty: Type) -> Option<Type> {
    let Type::Compound(enum_ty) = ty else {
        return None;
    };
    Some(Type::EnumTag(enum_ty))
}

pub fn enum_child_count(module: &ModuleCtx, enum_ty: Type) -> Option<usize> {
    let Type::Compound(enum_cmpd) = enum_ty else {
        return None;
    };
    let data = module.with_ty_store(|store| store.enum_data(enum_cmpd).cloned())?;
    let mut count = 1usize;
    for variant in &data.variants {
        count = count.checked_add(variant.fields.len())?;
    }
    Some(count)
}

pub fn enum_variant_field_slot(
    module: &ModuleCtx,
    variant: EnumVariantRef,
    field: u32,
) -> Option<u32> {
    let data = module.with_ty_store(|store| store.enum_data(variant.enum_ty()).cloned())?;
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

pub fn enum_slot_info(module: &ModuleCtx, enum_ty: Type, idx: u32) -> Option<EnumSlotInfo> {
    if idx == 0 {
        return Some(EnumSlotInfo::Tag {
            ty: enum_tag_ty(enum_ty)?,
        });
    }

    let Type::Compound(enum_cmpd) = enum_ty else {
        return None;
    };
    let data = module.with_ty_store(|store| store.enum_data(enum_cmpd).cloned())?;
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

pub fn enum_tag_slice(module: &ModuleCtx, enum_ty: Type) -> Option<AggregateSlice> {
    aggregate_slice_for_index(module, enum_ty, 0)
}

pub fn enum_variant_field_slice(
    module: &ModuleCtx,
    enum_ty: Type,
    variant: EnumVariantRef,
    field: u32,
) -> Option<AggregateSlice> {
    aggregate_slice_for_index(
        module,
        enum_ty,
        enum_variant_field_slot(module, variant, field)?,
    )
}

fn enum_variant_field_first_leaf(
    module: &ModuleCtx,
    enum_ty: Type,
    variant: EnumVariantRef,
    field: u32,
) -> Option<usize> {
    let slot = usize::try_from(enum_variant_field_slot(module, variant, field)?).ok()?;
    let mut first_leaf = 0usize;
    for idx in 0..slot {
        let child_ty = aggregate_child_ty(module, enum_ty, u32::try_from(idx).ok()?)?;
        first_leaf = first_leaf.checked_add(flattened_leaf_count(module, child_ty)?)?;
    }
    Some(first_leaf)
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        DataFlowGraph, Type,
        module::Module,
        types::{EnumReprHint, VariantData},
    };
    use sonatina_parser::parse_module;

    fn parse_test_module(src: &str) -> Module {
        parse_module(src).expect("parse should succeed").module
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
