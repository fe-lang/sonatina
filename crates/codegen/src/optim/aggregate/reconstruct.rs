use sonatina_ir::{
    Function, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, data, downcast},
};

use super::shape;

pub(crate) struct AggregateValueReconstructor<'a> {
    layout_cache: &'a mut shape::AggregateLayoutCache,
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
        if !shape::is_supported_aggregate_ty(func.ctx(), source_ty) {
            return self.cast_aggregate_view_value(func, inst, source, source_ty, result_ty);
        }
        if is_explicit_undef(func, source) {
            return Some(func.dfg.make_undef_value(result_ty));
        }

        let source_leaf_count = self
            .layout_cache
            .runtime_leaves(func.ctx(), source_ty)?
            .len();
        if source_slice.first_leaf == 0 && source_slice.leaf_count == source_leaf_count {
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

        if !shape::is_supported_aggregate_ty(func.ctx(), result_ty) {
            return None;
        }

        let child_count = shape::aggregate_child_count(func.ctx(), result_ty)?;
        let mut rebuilt = func.dfg.make_undef_value(result_ty);
        for idx in 0..child_count {
            let idx = u32::try_from(idx).ok()?;
            let child_slice = shape::aggregate_slice_for_index(func.ctx(), result_ty, idx)?;
            let child_value = if child_slice.leaf_count == 0 {
                func.dfg.make_undef_value(child_slice.ty)
            } else {
                let source_child_slice = shape::aggregate_slice_for_leaf_range(
                    func.ctx(),
                    source_ty,
                    source_slice.first_leaf + child_slice.first_leaf,
                    child_slice.leaf_count,
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
            if shape::is_supported_aggregate_ty(func.ctx(), source_ty) {
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

        let from_is_agg = shape::is_supported_aggregate_ty(func.ctx(), from_ty);
        let to_is_agg = shape::is_supported_aggregate_ty(func.ctx(), to_ty);
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

fn extract_value_before_inst(
    func: &mut Function,
    inst: InstId,
    aggregate: ValueId,
    idx: u32,
    ty: Type,
) -> ValueId {
    let idx_value = func.dfg.make_imm_value(i64::from(idx));
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

fn insert_value_before_inst(
    func: &mut Function,
    inst: InstId,
    dest: ValueId,
    idx: u32,
    value: ValueId,
    ty: Type,
) -> ValueId {
    let idx_value = func.dfg.make_imm_value(i64::from(idx));
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
}
