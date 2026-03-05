use smallvec::{SmallVec, smallvec};
use sonatina_ir::{DataFlowGraph, Type, U256, ValueId, module::ModuleCtx, types::CompoundType};

pub type FieldPath = SmallVec<[u32; 4]>;

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
    let shape = aggregate_shape(module, root_ty)?;
    let ty = aggregate_ty_at_path(module, root_ty, path)?;

    let first_leaf = shape
        .leaves
        .iter()
        .position(|leaf| leaf.path.starts_with(path))?;
    let leaf_count = shape.leaves[first_leaf..]
        .iter()
        .take_while(|leaf| leaf.path.starts_with(path))
        .count();
    (leaf_count != 0).then_some(AggregateSlice {
        ty,
        first_leaf,
        leaf_count,
    })
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

fn aggregate_ty_at_path(module: &ModuleCtx, root_ty: Type, path: &[u32]) -> Option<Type> {
    let mut cur = root_ty;
    for &idx in path {
        cur = aggregate_child_ty(module, cur, idx)?;
    }
    Some(cur)
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
        Some(CompoundType::Ptr(_)) | Some(CompoundType::Func { .. }) => None,
        None => {
            let size = u32::try_from(module.size_of_unchecked(ty)).ok()?;
            out.push(AggregateLeaf {
                path: path.clone(),
                ty,
                offset_bytes: base_offset,
                size_bytes: size,
            });
            Some(())
        }
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
}
