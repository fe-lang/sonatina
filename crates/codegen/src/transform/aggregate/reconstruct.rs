use smallvec::SmallVec;
use sonatina_ir::{
    Function, I256, Immediate, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, data, downcast},
    types::{CompoundType, EnumVariantRef},
};

use super::{scalarize::enum_variant_tag_imm, shape};

pub(crate) struct AggregateValueReconstructor<'a> {
    layout_cache: &'a mut shape::AggregateLayoutCache,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValueRebuildKind {
    Aggregate,
    Enum,
    Leaf,
}

impl<'a> AggregateValueReconstructor<'a> {
    pub(crate) fn new(layout_cache: &'a mut shape::AggregateLayoutCache) -> Self {
        Self { layout_cache }
    }

    pub(crate) fn rebuild_slice(
        &mut self,
        func: &mut Function,
        inst: InstId,
        source: ValueId,
        source_ty: Type,
        source_slice: shape::AggregateSlice,
        result_ty: Type,
    ) -> Option<ValueId> {
        if source_slice.leaf_count == 0 {
            return Some(func.dfg.make_undef_value(result_ty));
        }
        if !shape::is_supported_scalar_shape_ty(func.ctx(), source_ty) {
            return self.cast_aggregate_view_value(func, inst, source, source_ty, result_ty);
        }
        if is_explicit_undef(func, source) {
            return Some(func.dfg.make_undef_value(result_ty));
        }

        let (source_first_runtime_leaf, source_runtime_leaf_count) =
            shape::runtime_leaf_range_for_slice(func.ctx(), source_ty, source_slice)?;
        if source_runtime_leaf_count == 0 {
            return Some(func.dfg.make_undef_value(result_ty));
        }

        let source_leaf_count = self
            .layout_cache
            .runtime_leaves(func.ctx(), source_ty)?
            .len();
        if source_first_runtime_leaf == 0 && source_runtime_leaf_count == source_leaf_count {
            return self.cast_aggregate_view_value(func, inst, source, source_ty, result_ty);
        }

        if let Some(child_idx) =
            immediate_child_index_for_slice(func.ctx(), source_ty, source_slice)
        {
            let child_ty = shape::aggregate_child_ty(func.ctx(), source_ty, child_idx)?;
            let child_value =
                self.lookup_immediate_child_value(func, inst, source, source_ty, child_idx)?;
            return self.cast_aggregate_view_value(func, inst, child_value, child_ty, result_ty);
        }

        if !shape::is_supported_scalar_shape_ty(func.ctx(), result_ty) {
            let child_count = shape::aggregate_child_count(func.ctx(), source_ty)?;
            for idx in 0..child_count {
                let idx = u32::try_from(idx).ok()?;
                let child_slice = shape::aggregate_slice_for_index(func.ctx(), source_ty, idx)?;
                let (child_first_runtime_leaf, child_runtime_leaf_count) =
                    shape::runtime_leaf_range_for_slice(func.ctx(), source_ty, child_slice)?;
                if source_first_runtime_leaf < child_first_runtime_leaf
                    || source_first_runtime_leaf + source_runtime_leaf_count
                        > child_first_runtime_leaf + child_runtime_leaf_count
                {
                    continue;
                }

                let child_value =
                    self.lookup_immediate_child_value(func, inst, source, source_ty, idx)?;
                let nested_slice = shape::aggregate_slice_for_runtime_leaf_range(
                    func.ctx(),
                    child_slice.ty,
                    source_first_runtime_leaf - child_first_runtime_leaf,
                    source_runtime_leaf_count,
                )?;
                return self.rebuild_slice(
                    func,
                    inst,
                    child_value,
                    child_slice.ty,
                    nested_slice,
                    result_ty,
                );
            }
            return None;
        }

        if matches!(
            result_ty.resolve_compound(func.ctx()),
            Some(CompoundType::Enum(_))
        ) {
            let module = func.ctx().clone();
            let shape = self.layout_cache.shape(&module, result_ty)?;
            let mut leaves = SmallVec::<[ValueId; 4]>::new();
            let mut next_runtime_leaf = source_first_runtime_leaf;
            for leaf in &shape.leaves {
                if leaf.size_bytes == 0 {
                    leaves.push(func.dfg.make_undef_value(leaf.ty));
                    continue;
                }

                let source_child_slice = shape::aggregate_slice_for_runtime_leaf_range(
                    &module,
                    source_ty,
                    next_runtime_leaf,
                    1,
                )?;
                leaves.push(self.rebuild_slice(
                    func,
                    inst,
                    source,
                    source_ty,
                    source_child_slice,
                    leaf.ty,
                )?);
                next_runtime_leaf = next_runtime_leaf.checked_add(1)?;
            }
            return rebuild_scalar_shape_from_leaf_values(func, inst, &module, result_ty, &leaves);
        }

        let child_count = shape::aggregate_child_count(func.ctx(), result_ty)?;
        let mut rebuilt = func.dfg.make_undef_value(result_ty);
        for idx in 0..child_count {
            let idx = u32::try_from(idx).ok()?;
            let child_slice = shape::aggregate_slice_for_index(func.ctx(), result_ty, idx)?;
            let (child_first_runtime_leaf, child_runtime_leaf_count) =
                shape::runtime_leaf_range_for_slice(func.ctx(), result_ty, child_slice)?;
            let child_value = if child_runtime_leaf_count == 0 {
                func.dfg.make_undef_value(child_slice.ty)
            } else {
                let source_child_slice = shape::aggregate_slice_for_runtime_leaf_range(
                    func.ctx(),
                    source_ty,
                    source_first_runtime_leaf + child_first_runtime_leaf,
                    child_runtime_leaf_count,
                )?;
                self.rebuild_slice(
                    func,
                    inst,
                    source,
                    source_ty,
                    source_child_slice,
                    child_slice.ty,
                )?
            };
            rebuilt = insert_value_before_inst(func, inst, rebuilt, idx, child_value, result_ty);
        }
        Some(rebuilt)
    }

    fn lookup_immediate_child_value(
        &mut self,
        func: &mut Function,
        inst: InstId,
        aggregate: ValueId,
        aggregate_ty: Type,
        target_idx: u32,
    ) -> Option<ValueId> {
        let child_ty = shape::aggregate_child_ty(func.ctx(), aggregate_ty, target_idx)?;
        if is_explicit_undef(func, aggregate) {
            return Some(func.dfg.make_undef_value(child_ty));
        }

        if let Some(slot) =
            enum_child_value_from_source(func, inst, aggregate, aggregate_ty, target_idx, child_ty)
        {
            return slot;
        }

        let Some(def_inst) = func.dfg.value_inst(aggregate) else {
            return Some(extract_value_before_inst(
                func, inst, aggregate, target_idx, child_ty,
            ));
        };

        if let Some(insert) =
            downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(def_inst))
        {
            let insert_idx = shape::const_u32(&func.dfg, *insert.idx())?;
            return if insert_idx == target_idx {
                Some(*insert.value())
            } else {
                self.lookup_immediate_child_value(
                    func,
                    inst,
                    *insert.dest(),
                    aggregate_ty,
                    target_idx,
                )
            };
        }

        if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(def_inst))
        {
            let source = *bitcast.from();
            let source_ty = func.dfg.value_ty(source);
            if shape::is_supported_scalar_shape_ty(func.ctx(), source_ty) {
                let source_slice = self.layout_cache.compatible_bitcast_source_slice(
                    func.ctx(),
                    source_ty,
                    aggregate_ty,
                    shape::aggregate_slice_for_index(func.ctx(), aggregate_ty, target_idx)?,
                )?;
                return self.rebuild_slice(func, inst, source, source_ty, source_slice, child_ty);
            }
        }

        Some(extract_value_before_inst(
            func, inst, aggregate, target_idx, child_ty,
        ))
    }

    fn cast_aggregate_view_value(
        &mut self,
        func: &mut Function,
        inst: InstId,
        value: ValueId,
        from_ty: Type,
        to_ty: Type,
    ) -> Option<ValueId> {
        if from_ty == to_ty {
            return Some(value);
        }

        let from_is_agg = shape::is_supported_scalar_shape_ty(func.ctx(), from_ty);
        let to_is_agg = shape::is_supported_scalar_shape_ty(func.ctx(), to_ty);
        let compatible = if from_is_agg && to_is_agg {
            self.layout_cache
                .compatible_bitcast_runtime_leaves(func.ctx(), from_ty, to_ty)
                .is_some()
        } else if from_is_agg {
            self.layout_cache
                .single_runtime_word_leaf(func.ctx(), from_ty)
                .is_some()
        } else if to_is_agg {
            self.layout_cache
                .single_runtime_word_leaf(func.ctx(), to_ty)
                .is_some()
        } else {
            false
        };

        compatible.then(|| bitcast_before_inst(func, inst, value, from_ty, to_ty))
    }
}

pub(crate) fn rebuild_scalar_shape_from_leaf_values(
    func: &mut Function,
    inst: InstId,
    module: &sonatina_ir::module::ModuleCtx,
    agg_ty: Type,
    scalar_leaves: &[ValueId],
) -> Option<ValueId> {
    if !shape::is_supported_scalar_shape_ty(module, agg_ty) {
        return None;
    }

    let leaf_count = shape::aggregate_shape(module, agg_ty)?.leaves.len();
    if scalar_leaves.len() != leaf_count {
        return None;
    }

    rebuild_value_from_leaf_values_impl(func, inst, module, agg_ty, scalar_leaves)
}

fn value_rebuild_kind(
    module: &sonatina_ir::module::ModuleCtx,
    ty: Type,
) -> Option<ValueRebuildKind> {
    match ty.resolve_compound(module) {
        Some(CompoundType::Enum(_)) if shape::is_supported_scalar_shape_ty(module, ty) => {
            Some(ValueRebuildKind::Enum)
        }
        Some(CompoundType::Enum(_)) => None,
        Some(CompoundType::Struct(_) | CompoundType::Array { .. })
            if shape::is_supported_aggregate_ty(module, ty) =>
        {
            Some(ValueRebuildKind::Aggregate)
        }
        Some(CompoundType::Struct(_) | CompoundType::Array { .. } | CompoundType::Func { .. }) => {
            None
        }
        Some(CompoundType::Ptr(_) | CompoundType::ObjRef(_) | CompoundType::ConstRef(_)) | None => {
            Some(ValueRebuildKind::Leaf)
        }
    }
}

pub(crate) fn bitcast_before_inst(
    func: &mut Function,
    inst: InstId,
    value: ValueId,
    from_ty: Type,
    to_ty: Type,
) -> ValueId {
    if from_ty == to_ty {
        return value;
    }

    let loc = func.layout.prev_inst_of(inst).map_or(
        CursorLocation::BlockTop(func.layout.inst_block(inst)),
        CursorLocation::At,
    );
    let mut cursor = InstInserter::at_location(loc);
    let bitcast_inst = cursor.insert_inst_data(
        func,
        cast::Bitcast::new_unchecked(func.inst_set(), value, to_ty),
    );
    let cast_value = func.dfg.make_value(Value::Inst {
        inst: bitcast_inst,
        result_idx: 0,
        ty: to_ty,
    });
    cursor.attach_result(func, bitcast_inst, cast_value);
    cast_value
}

fn rebuild_value_from_leaf_values_impl(
    func: &mut Function,
    inst: InstId,
    module: &sonatina_ir::module::ModuleCtx,
    agg_ty: Type,
    scalar_leaves: &[ValueId],
) -> Option<ValueId> {
    if scalar_leaves.is_empty() {
        return Some(func.dfg.make_undef_value(agg_ty));
    }

    match value_rebuild_kind(module, agg_ty)? {
        ValueRebuildKind::Leaf => (scalar_leaves.len() == 1).then_some(scalar_leaves[0]),
        ValueRebuildKind::Enum => {
            rebuild_enum_from_leaf_values(func, inst, module, agg_ty, scalar_leaves)
        }
        ValueRebuildKind::Aggregate => {
            let child_count = shape::aggregate_child_count(module, agg_ty)?;
            let mut aggregate = func.dfg.make_undef_value(agg_ty);
            for idx in 0..child_count {
                let idx = u32::try_from(idx).ok()?;
                let child = shape::aggregate_slice_for_index(module, agg_ty, idx)?;
                let child_value = if child.leaf_count == 0 {
                    func.dfg.make_undef_value(child.ty)
                } else {
                    rebuild_value_from_leaf_values_impl(
                        func,
                        inst,
                        module,
                        child.ty,
                        &scalar_leaves[child.first_leaf..child.first_leaf + child.leaf_count],
                    )?
                };
                aggregate =
                    insert_value_before_inst(func, inst, aggregate, idx, child_value, agg_ty);
            }
            Some(aggregate)
        }
    }
}

fn rebuild_enum_from_leaf_values(
    func: &mut Function,
    inst: InstId,
    module: &sonatina_ir::module::ModuleCtx,
    enum_ty: Type,
    scalar_leaves: &[ValueId],
) -> Option<ValueId> {
    let Type::Compound(enum_cmpd) = enum_ty else {
        return None;
    };
    let tag_slice = shape::enum_tag_slice(module, enum_ty)?;
    let tag = *scalar_leaves.get(tag_slice.first_leaf)?;
    let variant = resolve_known_enum_variant(func, enum_cmpd, tag)?;
    let variant_data = module.with_ty_store(|store| store.enum_variant_data(variant).cloned())?;
    let mut values = SmallVec::<[ValueId; 2]>::new();
    for (field_idx, _) in variant_data.fields.iter().enumerate() {
        let field_idx = u32::try_from(field_idx).ok()?;
        let field_slice = shape::enum_variant_field_slice(module, enum_ty, variant, field_idx)?;
        let value = if field_slice.leaf_count == 0 {
            func.dfg.make_undef_value(field_slice.ty)
        } else {
            rebuild_value_from_leaf_values_impl(
                func,
                inst,
                module,
                field_slice.ty,
                &scalar_leaves
                    [field_slice.first_leaf..field_slice.first_leaf + field_slice.leaf_count],
            )?
        };
        values.push(value);
    }
    Some(insert_enum_make_before_inst(
        func, inst, enum_ty, variant, values,
    ))
}

fn resolve_known_enum_variant(
    func: &Function,
    enum_ty: sonatina_ir::types::CompoundTypeRef,
    value: ValueId,
) -> Option<EnumVariantRef> {
    let idx = if let Some(imm) = func.dfg.value_imm(value) {
        imm.to_nonnegative_usize()?
    } else if let Some(inst) = func.dfg.value_inst(value)
        && let Some(enum_tag) = downcast::<&data::EnumTag>(func.inst_set(), func.dfg.inst(inst))
        && let Some(make_inst) = func.dfg.value_inst(*enum_tag.value())
        && let Some(enum_make) =
            downcast::<&data::EnumMake>(func.inst_set(), func.dfg.inst(make_inst))
    {
        usize::try_from(enum_make.variant().index()).ok()?
    } else {
        return None;
    };
    let variant_count = func
        .ctx()
        .with_ty_store(|store| store.enum_data(enum_ty).map(|data| data.variants.len()))?;
    (idx < variant_count).then_some(EnumVariantRef::new(enum_ty, u32::try_from(idx).ok()?))
}

fn is_explicit_undef(func: &Function, value: ValueId) -> bool {
    matches!(func.dfg.value(value), Value::Undef { .. })
}

fn immediate_child_index_for_slice(
    module: &sonatina_ir::module::ModuleCtx,
    agg_ty: Type,
    slice: shape::AggregateSlice,
) -> Option<u32> {
    let child_count = shape::aggregate_child_count(module, agg_ty)?;
    (0..child_count).find_map(|idx| {
        let idx_u32 = u32::try_from(idx).ok()?;
        let child = shape::aggregate_slice_for_index(module, agg_ty, idx_u32)?;
        (child.first_leaf == slice.first_leaf
            && child.leaf_count == slice.leaf_count
            && child.ty == slice.ty)
            .then_some(idx_u32)
    })
}

fn enum_child_value_from_source(
    func: &mut Function,
    inst: InstId,
    aggregate: ValueId,
    aggregate_ty: Type,
    target_idx: u32,
    child_ty: Type,
) -> Option<Option<ValueId>> {
    if !matches!(
        aggregate_ty.resolve_compound(func.ctx()),
        Some(sonatina_ir::types::CompoundType::Enum(_))
    ) {
        return None;
    }

    let source_value = match func.dfg.value_inst(aggregate) {
        Some(def_inst)
            if downcast::<&data::EnumMake>(func.inst_set(), func.dfg.inst(def_inst)).is_some() =>
        {
            let enum_make =
                downcast::<&data::EnumMake>(func.inst_set(), func.dfg.inst(def_inst)).cloned()?;
            if target_idx == 0 {
                return Some(Some(func.dfg.make_imm_value(enum_variant_tag_imm(
                    *enum_make.variant(),
                    child_ty,
                ))));
            }
            let shape::EnumSlotInfo::VariantField { variant, field, .. } =
                shape::enum_slot_info(func.ctx(), aggregate_ty, target_idx)?
            else {
                return Some(None);
            };
            if *enum_make.variant() != variant {
                return Some(Some(func.dfg.make_undef_value(child_ty)));
            }
            return Some(
                enum_make
                    .values()
                    .get(usize::try_from(field).ok()?)
                    .copied()
                    .or_else(|| Some(func.dfg.make_undef_value(child_ty))),
            );
        }
        _ => aggregate,
    };

    if target_idx == 0 {
        return Some(Some(enum_tag_before_inst(
            func,
            inst,
            source_value,
            child_ty,
        )));
    }

    Some(None)
}

fn extract_value_before_inst(
    func: &mut Function,
    inst: InstId,
    aggregate: ValueId,
    idx: u32,
    ty: Type,
) -> ValueId {
    let idx_value = func
        .dfg
        .make_imm_value(Immediate::from_i256(I256::from(idx), Type::I256));
    let loc = func.layout.prev_inst_of(inst).map_or(
        CursorLocation::BlockTop(func.layout.inst_block(inst)),
        CursorLocation::At,
    );
    let mut cursor = InstInserter::at_location(loc);
    let extract_inst = cursor.insert_inst_data(
        func,
        data::ExtractValue::new_unchecked(func.inst_set(), aggregate, idx_value),
    );
    let extract_value = func.dfg.make_value(Value::Inst {
        inst: extract_inst,
        result_idx: 0,
        ty,
    });
    cursor.attach_result(func, extract_inst, extract_value);
    extract_value
}

fn enum_tag_before_inst(func: &mut Function, inst: InstId, value: ValueId, ty: Type) -> ValueId {
    let loc = func.layout.prev_inst_of(inst).map_or(
        CursorLocation::BlockTop(func.layout.inst_block(inst)),
        CursorLocation::At,
    );
    let mut cursor = InstInserter::at_location(loc);
    let enum_tag_inst =
        cursor.insert_inst_data(func, data::EnumTag::new_unchecked(func.inst_set(), value));
    let enum_tag_value = func.dfg.make_value(Value::Inst {
        inst: enum_tag_inst,
        result_idx: 0,
        ty,
    });
    cursor.attach_result(func, enum_tag_inst, enum_tag_value);
    enum_tag_value
}

fn insert_enum_make_before_inst(
    func: &mut Function,
    inst: InstId,
    ty: Type,
    variant: EnumVariantRef,
    values: SmallVec<[ValueId; 2]>,
) -> ValueId {
    let loc = func.layout.prev_inst_of(inst).map_or(
        CursorLocation::BlockTop(func.layout.inst_block(inst)),
        CursorLocation::At,
    );
    let mut cursor = InstInserter::at_location(loc);
    let enum_make_inst = cursor.insert_inst_data(
        func,
        data::EnumMake::new_unchecked(func.inst_set(), ty, variant, values),
    );
    let enum_make_value = func.dfg.make_value(Value::Inst {
        inst: enum_make_inst,
        result_idx: 0,
        ty,
    });
    cursor.attach_result(func, enum_make_inst, enum_make_value);
    enum_make_value
}

fn insert_value_before_inst(
    func: &mut Function,
    inst: InstId,
    dest: ValueId,
    idx: u32,
    value: ValueId,
    ty: Type,
) -> ValueId {
    let idx_value = func
        .dfg
        .make_imm_value(Immediate::from_i256(I256::from(idx), Type::I256));
    let loc = func.layout.prev_inst_of(inst).map_or(
        CursorLocation::BlockTop(func.layout.inst_block(inst)),
        CursorLocation::At,
    );
    let mut cursor = InstInserter::at_location(loc);
    let insert_inst = cursor.insert_inst_data(
        func,
        data::InsertValue::new_unchecked(func.inst_set(), dest, idx_value, value),
    );
    let insert_value = func.dfg.make_value(Value::Inst {
        inst: insert_inst,
        result_idx: 0,
        ty,
    });
    cursor.attach_result(func, insert_inst, insert_value);
    insert_value
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{Module, module::FuncRef};
    use sonatina_parser::parse_module;

    fn parse_test_module(src: &str) -> Module {
        parse_module(src).expect("parse should succeed").module
    }

    fn lookup_func(module: &Module, name: &str) -> FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .expect("function should exist")
    }

    #[test]
    fn rebuilds_compatible_aggregate_bitcast_slices() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i256 };
type @pair = { i256, i256 };
type @nested = { @inner, i256 };

func private %f(v0.@pair) -> i256 {
block0:
    return 0.i256;
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
        let func_ref = lookup_func(&module, "f");

        module.func_store.modify(func_ref, |func| {
            let ret = func
                .layout
                .last_inst_of(func.layout.entry_block().unwrap())
                .unwrap();
            let arg = func.arg_values[0];
            let target_slice = shape::aggregate_slice_for_index(func.ctx(), nested, 0).unwrap();
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let source_slice = layout_cache
                .compatible_bitcast_source_slice(func.ctx(), pair, nested, target_slice)
                .unwrap();
            let rebuilt = AggregateValueReconstructor::new(&mut layout_cache)
                .rebuild_slice(func, ret, arg, pair, source_slice, inner)
                .unwrap();

            assert_eq!(func.dfg.value_ty(rebuilt), inner);
            let rebuilt_inst = func.dfg.value_inst(rebuilt).unwrap();
            let bitcast =
                downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(rebuilt_inst)).unwrap();
            let extract_inst = func.dfg.value_inst(*bitcast.from()).unwrap();
            let extract =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(extract_inst))
                    .unwrap();
            assert_eq!(*extract.dest(), arg);
            assert_eq!(shape::const_u32(&func.dfg, *extract.idx()), Some(0));
        });
    }

    #[test]
    fn rebuilds_full_compatible_bitcast_views_with_zero_sized_fields() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @src = { unit, i256, i256 };
type @dst = { i256, i256 };

func private %f(v0.@src) -> i256 {
block0:
    return 0.i256;
}
"#,
        );
        let src = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("src").unwrap()));
        let dst = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("dst").unwrap()));
        let func_ref = lookup_func(&module, "f");

        module.func_store.modify(func_ref, |func| {
            let ret = func
                .layout
                .last_inst_of(func.layout.entry_block().unwrap())
                .unwrap();
            let arg = func.arg_values[0];
            let target_slice = shape::aggregate_slice_for_path(func.ctx(), dst, &[]).unwrap();
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let source_slice = layout_cache
                .compatible_bitcast_source_slice(func.ctx(), src, dst, target_slice)
                .unwrap();
            let rebuilt = AggregateValueReconstructor::new(&mut layout_cache)
                .rebuild_slice(func, ret, arg, src, source_slice, dst)
                .unwrap();

            assert_eq!(func.dfg.value_ty(rebuilt), dst);
            let rebuilt_inst = func.dfg.value_inst(rebuilt).unwrap();
            let bitcast =
                downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(rebuilt_inst)).unwrap();
            assert_eq!(*bitcast.from(), arg);
        });
    }

    #[test]
    fn rebuilds_single_word_scalar_and_aggregate_views() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i256, v1.@one) -> i256 {
block0:
    return 0.i256;
}
"#,
        );
        let one = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("one").unwrap()));
        let func_ref = lookup_func(&module, "f");

        module.func_store.modify(func_ref, |func| {
            let ret = func
                .layout
                .last_inst_of(func.layout.entry_block().unwrap())
                .unwrap();
            let scalar = func.arg_values[0];
            let aggregate = func.arg_values[1];
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let mut reconstructor = AggregateValueReconstructor::new(&mut layout_cache);

            let scalar_to_agg = reconstructor
                .rebuild_slice(
                    func,
                    ret,
                    scalar,
                    Type::I256,
                    shape::AggregateSlice {
                        ty: Type::I256,
                        first_leaf: 0,
                        leaf_count: 1,
                    },
                    one,
                )
                .unwrap();
            let agg_to_scalar = reconstructor
                .rebuild_slice(
                    func,
                    ret,
                    aggregate,
                    one,
                    shape::aggregate_slice_for_path(func.ctx(), one, &[]).unwrap(),
                    Type::I256,
                )
                .unwrap();

            let scalar_to_agg_inst = func.dfg.value_inst(scalar_to_agg).unwrap();
            let scalar_to_agg_bitcast =
                downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(scalar_to_agg_inst))
                    .unwrap();
            assert_eq!(*scalar_to_agg_bitcast.from(), scalar);

            let agg_to_scalar_inst = func.dfg.value_inst(agg_to_scalar).unwrap();
            let agg_to_scalar_bitcast =
                downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(agg_to_scalar_inst))
                    .unwrap();
            assert_eq!(*agg_to_scalar_bitcast.from(), aggregate);
        });
    }

    #[test]
    fn rebuilds_insert_chain_slices_with_base_extract_fallback() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.@pair, v1.i256) -> i256 {
block0:
    v2.@pair = insert_value v0 0.i8 v1;
    return 0.i256;
}
"#,
        );
        let pair = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("pair").unwrap()));
        let func_ref = lookup_func(&module, "f");

        module.func_store.modify(func_ref, |func| {
            let block = func.layout.entry_block().unwrap();
            let insert_inst = func.layout.first_inst_of(block).unwrap();
            let ret = func.layout.last_inst_of(block).unwrap();
            let source = func.dfg.inst_result(insert_inst).unwrap();
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let rebuilt = AggregateValueReconstructor::new(&mut layout_cache)
                .rebuild_slice(
                    func,
                    ret,
                    source,
                    pair,
                    shape::aggregate_slice_for_index(func.ctx(), pair, 1).unwrap(),
                    Type::I256,
                )
                .unwrap();

            let rebuilt_inst = func.dfg.value_inst(rebuilt).unwrap();
            let extract =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(rebuilt_inst))
                    .unwrap();
            assert_eq!(*extract.dest(), func.arg_values[0]);
            assert_eq!(shape::const_u32(&func.dfg, *extract.idx()), Some(1));
        });
    }

    #[test]
    fn rebuilds_fieldless_enum_children_as_full_enum_values() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @E = enum {
    #A,
    #B,
};

type @Pair = { i256, @E };

func private %f() -> i256 {
block0:
    return 0.i256;
}
"#,
        );
        let pair = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("Pair").unwrap()));
        let enum_ty = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_enum("E").unwrap()));
        let Type::Compound(enum_cmpd) = enum_ty else {
            panic!("expected enum compound type");
        };
        let func_ref = lookup_func(&module, "f");

        module.func_store.modify(func_ref, |func| {
            let ret = func
                .layout
                .last_inst_of(func.layout.entry_block().unwrap())
                .unwrap();
            let module_ctx = func.ctx().clone();
            let leaves = [
                func.dfg
                    .make_imm_value(Immediate::from_i256(I256::zero(), Type::I256)),
                func.dfg.make_imm_value(Immediate::EnumTag {
                    enum_ty: enum_cmpd,
                    value: I256::zero(),
                }),
            ];
            let rebuilt =
                rebuild_scalar_shape_from_leaf_values(func, ret, &module_ctx, pair, &leaves)
                    .unwrap();
            let rebuilt_inst = func.dfg.value_inst(rebuilt).unwrap();
            let final_insert =
                downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(rebuilt_inst))
                    .unwrap();
            assert_eq!(shape::const_u32(&func.dfg, *final_insert.idx()), Some(1));
            let enum_child = *final_insert.value();
            assert_eq!(func.dfg.value_ty(enum_child), enum_ty);

            let enum_make_inst = func.dfg.value_inst(enum_child).unwrap();
            let enum_make =
                downcast::<&data::EnumMake>(func.inst_set(), func.dfg.inst(enum_make_inst))
                    .unwrap();
            assert_eq!(*enum_make.ty(), enum_ty);
            assert_eq!(*enum_make.variant(), EnumVariantRef::new(enum_cmpd, 0));
            assert!(enum_make.values().is_empty());
        });
    }

    #[test]
    fn rebuilds_payload_enum_children_as_full_enum_values() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

type @Pair = { i256, @OptionI256 };

func private %f() -> i256 {
block0:
    return 0.i256;
}
"#,
        );
        let pair = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_struct("Pair").unwrap()));
        let enum_ty = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_enum("OptionI256").unwrap()));
        let Type::Compound(enum_cmpd) = enum_ty else {
            panic!("expected enum compound type");
        };
        let func_ref = lookup_func(&module, "f");

        module.func_store.modify(func_ref, |func| {
            let ret = func
                .layout
                .last_inst_of(func.layout.entry_block().unwrap())
                .unwrap();
            let module_ctx = func.ctx().clone();
            let leaves = [
                func.dfg
                    .make_imm_value(Immediate::from_i256(I256::from(11), Type::I256)),
                func.dfg.make_imm_value(Immediate::EnumTag {
                    enum_ty: enum_cmpd,
                    value: I256::from(1),
                }),
                func.dfg
                    .make_imm_value(Immediate::from_i256(I256::from(7), Type::I256)),
            ];
            let rebuilt =
                rebuild_scalar_shape_from_leaf_values(func, ret, &module_ctx, pair, &leaves)
                    .unwrap();
            let rebuilt_inst = func.dfg.value_inst(rebuilt).unwrap();
            let final_insert =
                downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(rebuilt_inst))
                    .unwrap();
            assert_eq!(shape::const_u32(&func.dfg, *final_insert.idx()), Some(1));
            let enum_child = *final_insert.value();
            assert_eq!(func.dfg.value_ty(enum_child), enum_ty);

            let enum_make_inst = func.dfg.value_inst(enum_child).unwrap();
            let enum_make =
                downcast::<&data::EnumMake>(func.inst_set(), func.dfg.inst(enum_make_inst))
                    .unwrap();
            assert_eq!(*enum_make.ty(), enum_ty);
            assert_eq!(*enum_make.variant(), EnumVariantRef::new(enum_cmpd, 1));
            assert_eq!(enum_make.values().len(), 1);
            let payload = enum_make.values()[0];
            assert_eq!(func.dfg.value_ty(payload), Type::I256);
            assert_eq!(
                func.dfg.value_imm(payload).map(|imm| imm.as_i256()),
                Some(I256::from(7))
            );
        });
    }

    #[test]
    fn refuses_to_rebuild_enum_results_with_dynamic_tags() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.enumtag(@OptionI256), v1.i256) -> i256 {
block0:
    return 0.i256;
}
"#,
        );
        let enum_ty = module
            .ctx
            .with_ty_store(|s| Type::Compound(s.lookup_enum("OptionI256").unwrap()));
        let func_ref = lookup_func(&module, "f");

        module.func_store.modify(func_ref, |func| {
            let ret = func
                .layout
                .last_inst_of(func.layout.entry_block().unwrap())
                .unwrap();
            let module_ctx = func.ctx().clone();
            let leaves = [func.arg_values[0], func.arg_values[1]];
            assert!(
                rebuild_scalar_shape_from_leaf_values(func, ret, &module_ctx, enum_ty, &leaves)
                    .is_none()
            );
        });
    }
}
