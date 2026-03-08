use rustc_hash::FxHashMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{DataFlowGraph, Type, U256, ValueId, module::ModuleCtx, types::CompoundType};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AggregateSlice {
    pub ty: Type,
    pub first_leaf: usize,
    pub leaf_count: usize,
}

#[derive(Default)]
pub struct AggregateLayoutCache {
    shape_cache: FxHashMap<Type, AggregateShape>,
    runtime_leaf_cache: FxHashMap<Type, RuntimeLeaves>,
}

impl AggregateLayoutCache {
    pub fn clear(&mut self) {
        self.shape_cache.clear();
        self.runtime_leaf_cache.clear();
    }

    pub fn shape(&mut self, module: &ModuleCtx, ty: Type) -> Option<AggregateShape> {
        if let Some(shape) = self.shape_cache.get(&ty) {
            return Some(shape.clone());
        }

        let shape = aggregate_shape(module, ty)?;
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
        aggregate_slice_for_leaf_range(module, from_ty, to_slice.first_leaf, to_slice.leaf_count)
    }
}

pub fn aggregate_shape(module: &ModuleCtx, ty: Type) -> Option<AggregateShape> {
    if !is_supported_aggregate_ty(module, ty) {
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
    if !is_supported_aggregate_ty(module, root_ty) {
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
    if !is_supported_aggregate_ty(module, root_ty) {
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
            CompoundType::Ptr(_) | CompoundType::Func { .. } => return None,
        }
    }

    aggregate_slice_for_path(module, base_pointee_ty, &path)
}

pub fn aggregate_child_ty(module: &ModuleCtx, agg_ty: Type, idx: u32) -> Option<Type> {
    let idx = usize::try_from(idx).ok()?;
    match agg_ty.resolve_compound(module)? {
        CompoundType::Struct(s) => (!s.packed).then_some(*s.fields.get(idx)?),
        CompoundType::Array { elem, len } => (idx < len).then_some(elem),
        CompoundType::Ptr(_) | CompoundType::Func { .. } => None,
    }
}

pub fn aggregate_child_count(module: &ModuleCtx, agg_ty: Type) -> Option<usize> {
    match agg_ty.resolve_compound(module)? {
        CompoundType::Struct(s) => (!s.packed).then_some(s.fields.len()),
        CompoundType::Array { len, .. } => Some(len),
        CompoundType::Ptr(_) | CompoundType::Func { .. } => None,
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
        let align = u32::try_from(module.align_of_unchecked(ty)).ok()?;
        offset = align_to(offset, align)?;

        let size = u32::try_from(module.size_of_unchecked(ty)).ok()?;
        offset = offset.checked_add(size)?;
    }

    let align = u32::try_from(module.align_of_unchecked(field_ty)).ok()?;
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

pub fn is_supported_aggregate_ty(module: &ModuleCtx, ty: Type) -> bool {
    match ty.resolve_compound(module) {
        Some(CompoundType::Struct(s)) => !s.packed,
        Some(CompoundType::Array { .. }) => true,
        _ => false,
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
        CompoundType::Ptr(_) | CompoundType::Func { .. } => None,
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
        CompoundType::Ptr(_) | CompoundType::Func { .. } => None,
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
        Some(CompoundType::Func { .. }) => None,
        Some(CompoundType::Ptr(_)) | None => Some(1),
    }
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
            let elem_size = u32::try_from(module.size_of_unchecked(elem)).ok()?;
            for idx in 0..len {
                let offset = elem_size.checked_mul(u32::try_from(idx).ok()?)?;
                let total_offset = base_offset.checked_add(offset)?;
                path.push(u32::try_from(idx).ok()?);
                flatten_aggregate(module, elem, total_offset, path, out)?;
                path.pop();
            }
            Some(())
        }
        Some(CompoundType::Ptr(_)) | None => {
            let size = u32::try_from(module.size_of_unchecked(ty)).ok()?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{DataFlowGraph, Type, module::Module};
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
}
