use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    Function, Type, ValueId,
    inst::{data, downcast},
    module::ModuleCtx,
};

use super::{
    LocalObjectArgInfo,
    provenance::{CompleteProvenance, CompleteRootSet},
    shape,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ObjectSlice {
    pub(crate) root: ValueId,
    pub(crate) ty: Type,
    pub(crate) first_leaf: usize,
    pub(crate) leaf_count: usize,
    pub(crate) total_leaves: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TrackedObject {
    Exact(ObjectSlice),
    RootUnknown { root: ValueId, total_leaves: usize },
}

pub(crate) fn collect_root_slices(
    func: &Function,
    local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> FxHashMap<ValueId, shape::AggregateSlice> {
    let mut root_slices = FxHashMap::default();

    if let Some(local_object_args) = local_object_args {
        for &idx in local_object_args.keys() {
            if let Some(&root) = func.arg_values.get(idx)
                && let Some(root_ty) = objref_element_ty(func.ctx(), func.dfg.value_ty(root))
            {
                root_slices.insert(root, whole_root_slice(layout_cache, func.ctx(), root_ty));
            }
        }
    }

    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if let Some(obj_alloc) =
                downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                && let Some(result) = func.dfg.inst_result(inst)
                && objref_element_ty(func.ctx(), func.dfg.value_ty(result)).is_some()
            {
                root_slices.insert(
                    result,
                    whole_root_slice(layout_cache, func.ctx(), *obj_alloc.ty()),
                );
            }
        }
    }

    root_slices
}

pub(crate) fn collect_tracked_objects(
    func: &Function,
    provenance: CompleteProvenance<'_>,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> SecondaryMap<ValueId, Option<TrackedObject>> {
    let mut tracked = SecondaryMap::default();

    for value in func.dfg.value_ids() {
        if objref_element_ty(func.ctx(), func.dfg.value_ty(value)).is_none() {
            continue;
        }
        tracked[value] = tracked_object_from_provenance(func, provenance, value, layout_cache);
    }

    tracked
}

fn tracked_object_from_provenance(
    func: &Function,
    provenance: CompleteProvenance<'_>,
    value: ValueId,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> Option<TrackedObject> {
    if let Some(projection) = provenance.exact_projection(value) {
        return Some(TrackedObject::Exact(ObjectSlice {
            root: projection.root_value,
            ty: projection.slice.ty,
            first_leaf: projection.slice.first_leaf,
            leaf_count: projection.slice.leaf_count,
            total_leaves: root_leaf_count_for_value(func, layout_cache, projection.root_value)?,
        }));
    }

    match provenance.root_set(value)? {
        CompleteRootSet::Single(root) => Some(TrackedObject::RootUnknown {
            root,
            total_leaves: root_leaf_count_for_value(func, layout_cache, root)?,
        }),
        CompleteRootSet::Multiple(_) => None,
    }
}

pub(crate) fn whole_root_slice(
    layout_cache: &mut shape::AggregateLayoutCache,
    ctx: &ModuleCtx,
    pointee_ty: Type,
) -> shape::AggregateSlice {
    shape::AggregateSlice {
        ty: pointee_ty,
        first_leaf: 0,
        leaf_count: root_leaf_count_for_ty(layout_cache, ctx, pointee_ty),
    }
}

pub(crate) fn root_leaf_count_for_value(
    func: &Function,
    layout_cache: &mut shape::AggregateLayoutCache,
    root: ValueId,
) -> Option<usize> {
    let ty = objref_element_ty(func.ctx(), func.dfg.value_ty(root))?;
    Some(root_leaf_count_for_ty(layout_cache, func.ctx(), ty))
}

pub(crate) fn root_leaf_count_for_ty(
    layout_cache: &mut shape::AggregateLayoutCache,
    ctx: &ModuleCtx,
    ty: Type,
) -> usize {
    if ty == Type::Unit {
        return 0;
    }
    layout_cache
        .shape(ctx, ty)
        .map_or(1, |shape| shape.leaves.len())
}

pub(crate) fn whole_root_slice_for_value(
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    value: ValueId,
) -> Option<ObjectSlice> {
    tracked[value]
        .as_ref()
        .copied()
        .and_then(TrackedObject::exact)
        .filter(|slice| {
            slice.root == value && slice.first_leaf == 0 && slice.leaf_count == slice.total_leaves
        })
}

pub(crate) fn object_slice_overlaps_effect(
    slice: ObjectSlice,
    base_slice: ObjectSlice,
    effect_leaves: &rustc_hash::FxHashSet<usize>,
) -> bool {
    if slice.root != base_slice.root {
        return false;
    }
    effect_leaves.iter().copied().any(|leaf| {
        let leaf = base_slice.first_leaf + leaf;
        leaf >= slice.first_leaf && leaf < slice.first_leaf + slice.leaf_count
    })
}

pub(crate) fn slices_overlap(lhs: ObjectSlice, rhs: ObjectSlice) -> bool {
    lhs.root == rhs.root
        && lhs.first_leaf < rhs.first_leaf + rhs.leaf_count
        && rhs.first_leaf < lhs.first_leaf + lhs.leaf_count
}

pub(crate) fn slice_is_covered_by(lhs: ObjectSlice, rhs: ObjectSlice) -> bool {
    lhs.root == rhs.root
        && lhs.first_leaf <= rhs.first_leaf
        && rhs.first_leaf + rhs.leaf_count <= lhs.first_leaf + lhs.leaf_count
}

pub(crate) fn enum_tag_object_slice(ctx: &ModuleCtx, base: ObjectSlice) -> Option<ObjectSlice> {
    let tag_slice = shape::enum_tag_slice(ctx, base.ty)?;
    Some(ObjectSlice {
        root: base.root,
        ty: tag_slice.ty,
        first_leaf: base.first_leaf + tag_slice.first_leaf,
        leaf_count: tag_slice.leaf_count,
        total_leaves: base.total_leaves,
    })
}

pub(crate) fn enum_variant_field_object_slice(
    ctx: &ModuleCtx,
    base: ObjectSlice,
    variant: sonatina_ir::types::EnumVariantRef,
    field: u32,
) -> Option<ObjectSlice> {
    let field_slice = shape::enum_variant_field_slice(ctx, base.ty, variant, field)?;
    Some(ObjectSlice {
        root: base.root,
        ty: field_slice.ty,
        first_leaf: base.first_leaf + field_slice.first_leaf,
        leaf_count: field_slice.leaf_count,
        total_leaves: base.total_leaves,
    })
}

pub(crate) fn objref_element_ty(ctx: &ModuleCtx, ty: Type) -> Option<Type> {
    let sonatina_ir::types::CompoundType::ObjRef(elem) = ty.resolve_compound(ctx)? else {
        return None;
    };
    Some(elem)
}

impl TrackedObject {
    pub(crate) fn exact(self) -> Option<ObjectSlice> {
        match self {
            Self::Exact(slice) => Some(slice),
            Self::RootUnknown { .. } => None,
        }
    }

    pub(crate) fn total_leaves(self) -> usize {
        match self {
            Self::Exact(slice) => slice.total_leaves,
            Self::RootUnknown { total_leaves, .. } => total_leaves,
        }
    }
}
