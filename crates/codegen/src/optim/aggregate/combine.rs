use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, Function, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, control_flow, data, downcast},
};

use super::shape;

#[derive(Default)]
pub struct AggregateCombine {
    changed: bool,
    layout_cache: shape::AggregateLayoutCache,
}

enum AggregateFieldLookup {
    Found(ValueId),
    BaseNeedsExtract(ValueId),
    Undef(Type),
    Unknown,
}

impl AggregateCombine {
    pub fn run(&mut self, func: &mut Function) -> bool {
        self.changed = false;
        self.layout_cache.clear();
        func.rebuild_users();

        loop {
            let mut iter_changed = false;
            let definitely_non_undef = compute_definitely_non_undef_aggregates(func);
            let blocks: Vec<_> = func.layout.iter_block().collect();
            for block in blocks {
                let insts: Vec<_> = func.layout.iter_inst(block).collect();
                for inst in insts {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    iter_changed |= self.try_rewrite_inst(func, inst, &definitely_non_undef);
                }
            }
            if !iter_changed {
                break;
            }
            self.changed = true;
            func.rebuild_users();
        }

        self.changed
    }

    fn try_rewrite_inst(
        &mut self,
        func: &mut Function,
        inst: InstId,
        definitely_non_undef: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        if downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_extract(func, inst)
        } else if downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_insert(func, inst, definitely_non_undef)
        } else if downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_phi(func, inst, definitely_non_undef)
        } else {
            false
        }
    }

    fn try_rewrite_extract(&mut self, func: &mut Function, inst: InstId) -> bool {
        let Some(extract) = downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst))
        else {
            return false;
        };
        let extract = extract.clone();
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let Some(target_idx) = inst_const_index(func, *extract.idx()) else {
            return false;
        };

        match walk_insert_chain_for_field(func, *extract.dest(), target_idx) {
            AggregateFieldLookup::Found(found) => {
                if func.dfg.value_ty(found) != func.dfg.value_ty(result) {
                    return self.try_rewrite_extract_through_aggregate_bitcast(
                        func, inst, &extract, result, target_idx,
                    );
                }
                func.dfg.change_to_alias(result, found);
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                true
            }
            AggregateFieldLookup::BaseNeedsExtract(base) if base != *extract.dest() => {
                let new_extract =
                    data::ExtractValue::new_unchecked(func.inst_set(), base, *extract.idx());
                func.dfg.replace_inst(inst, Box::new(new_extract));
                true
            }
            AggregateFieldLookup::Undef(field_ty) => {
                if field_ty != func.dfg.value_ty(result) {
                    return false;
                }
                let undef = func.dfg.make_undef_value(field_ty);
                func.dfg.change_to_alias(result, undef);
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                true
            }
            AggregateFieldLookup::BaseNeedsExtract(_) | AggregateFieldLookup::Unknown => self
                .try_rewrite_extract_through_aggregate_bitcast(
                    func, inst, &extract, result, target_idx,
                ),
        }
    }

    fn try_rewrite_extract_through_aggregate_bitcast(
        &mut self,
        func: &mut Function,
        inst: InstId,
        extract: &data::ExtractValue,
        result: ValueId,
        target_idx: u32,
    ) -> bool {
        let dest = *extract.dest();
        let Some(bitcast_inst) = func.dfg.value_inst(dest) else {
            return false;
        };
        let Some(bitcast) =
            downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(bitcast_inst)).cloned()
        else {
            return false;
        };

        let source = *bitcast.from();
        let source_ty = func.dfg.value_ty(source);
        let dest_ty = func.dfg.value_ty(dest);
        if !shape::is_supported_aggregate_ty(func.ctx(), dest_ty) {
            return false;
        }

        let Some(target_slice) = shape::aggregate_slice_for_index(func.ctx(), dest_ty, target_idx)
        else {
            return false;
        };
        let Some(source_slice) = (if shape::is_supported_aggregate_ty(func.ctx(), source_ty) {
            self.layout_cache.compatible_bitcast_source_slice(
                func.ctx(),
                source_ty,
                dest_ty,
                target_slice,
            )
        } else if self
            .layout_cache
            .single_runtime_word_leaf(func.ctx(), dest_ty)
            .is_some()
        {
            Some(shape::AggregateSlice {
                ty: source_ty,
                first_leaf: 0,
                leaf_count: 1,
            })
        } else {
            None
        }) else {
            return false;
        };
        let Some(replacement) = self.build_value_for_aggregate_slice(
            func,
            inst,
            source,
            source_ty,
            source_slice,
            func.dfg.value_ty(result),
        ) else {
            return false;
        };
        if func.dfg.value_ty(replacement) != func.dfg.value_ty(result) {
            return false;
        }
        func.dfg.change_to_alias(result, replacement);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }

    fn try_rewrite_insert(
        &mut self,
        func: &mut Function,
        inst: InstId,
        definitely_non_undef: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        let Some(insert) = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst))
        else {
            return false;
        };
        let insert = insert.clone();
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };

        // AC5: insert identical field back into aggregate.
        if is_identical_field_reinsert(func, &insert, definitely_non_undef) {
            if func.dfg.value_ty(*insert.dest()) != func.dfg.value_ty(result) {
                return false;
            }
            func.dfg.change_to_alias(result, *insert.dest());
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return true;
        }

        // AC3: overwrite collapse.
        if let Some(prev_inst) = func.dfg.value_inst(*insert.dest())
            && let Some(prev) =
                downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(prev_inst))
            && equivalent_indices(func, *insert.idx(), *prev.idx())
        {
            let rewritten = data::InsertValue::new_unchecked(
                func.inst_set(),
                *prev.dest(),
                *insert.idx(),
                *insert.value(),
            );
            func.dfg.replace_inst(inst, Box::new(rewritten));
            return true;
        }

        // AC6: full reconstruction reuse.
        if let Some(source) = try_reconstruct_original_aggregate(func, result) {
            if func.dfg.value_ty(source) != func.dfg.value_ty(result) {
                return false;
            }
            func.dfg.change_to_alias(result, source);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return true;
        }

        false
    }

    fn try_rewrite_phi(
        &mut self,
        func: &mut Function,
        inst: InstId,
        definitely_non_undef: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        self.try_rewrite_phi_of_extracts(func, inst)
            || self.try_rewrite_phi_of_inserts(func, inst, definitely_non_undef)
    }

    fn try_rewrite_phi_of_extracts(&mut self, func: &mut Function, inst: InstId) -> bool {
        let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)) else {
            return false;
        };
        let phi = phi.clone();
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let Some((first_val, first_pred)) = phi.args().first().copied() else {
            return false;
        };
        let Some(first_extract_inst) = func.dfg.value_inst(first_val) else {
            return false;
        };
        let Some(first_extract) =
            downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(first_extract_inst))
        else {
            return false;
        };
        let Some(idx) = inst_const_index(func, *first_extract.idx()) else {
            return false;
        };
        let idx_value = *first_extract.idx();
        let agg_ty = func.dfg.value_ty(*first_extract.dest());
        let res_ty = func.dfg.value_ty(result);

        let mut agg_args = vec![(*first_extract.dest(), first_pred)];
        for &(incoming, pred) in phi.args().iter().skip(1) {
            let Some(extract_inst) = func.dfg.value_inst(incoming) else {
                return false;
            };
            let Some(extract) =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(extract_inst))
            else {
                return false;
            };
            if inst_const_index(func, *extract.idx()) != Some(idx) {
                return false;
            }
            if func.dfg.value_ty(*extract.dest()) != agg_ty {
                return false;
            }
            if func.dfg.value_ty(incoming) != res_ty {
                return false;
            }
            agg_args.push((*extract.dest(), pred));
        }

        let block = func.layout.inst_block(inst);
        let agg_phi_value = append_phi_at_block_top(func, block, agg_ty, agg_args);
        let new_extract = append_non_phi_after_phi_region(
            func,
            block,
            data::ExtractValue::new_unchecked(func.inst_set(), agg_phi_value, idx_value),
            res_ty,
        );

        func.dfg.change_to_alias(result, new_extract);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }

    fn try_rewrite_phi_of_inserts(
        &mut self,
        func: &mut Function,
        inst: InstId,
        definitely_non_undef: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)) else {
            return false;
        };
        let phi = phi.clone();
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let Some((first_val, first_pred)) = phi.args().first().copied() else {
            return false;
        };
        let Some(first_insert_inst) = func.dfg.value_inst(first_val) else {
            return false;
        };
        let Some(first_insert) =
            downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(first_insert_inst))
        else {
            return false;
        };
        if is_identical_field_reinsert(func, first_insert, definitely_non_undef) {
            return false;
        }
        let Some(idx) = inst_const_index(func, *first_insert.idx()) else {
            return false;
        };
        let idx_value = *first_insert.idx();
        let base_ty = func.dfg.value_ty(*first_insert.dest());
        let payload_ty = func.dfg.value_ty(*first_insert.value());
        let result_ty = func.dfg.value_ty(result);

        let mut base_args = vec![(*first_insert.dest(), first_pred)];
        let mut payload_args = vec![(*first_insert.value(), first_pred)];

        for &(incoming, pred) in phi.args().iter().skip(1) {
            let Some(insert_inst) = func.dfg.value_inst(incoming) else {
                return false;
            };
            let Some(insert) =
                downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(insert_inst))
            else {
                return false;
            };
            if is_identical_field_reinsert(func, insert, definitely_non_undef) {
                return false;
            }
            if inst_const_index(func, *insert.idx()) != Some(idx) {
                return false;
            }
            if func.dfg.value_ty(incoming) != result_ty
                || func.dfg.value_ty(*insert.dest()) != base_ty
                || func.dfg.value_ty(*insert.value()) != payload_ty
            {
                return false;
            }
            base_args.push((*insert.dest(), pred));
            payload_args.push((*insert.value(), pred));
        }

        let block = func.layout.inst_block(inst);
        let base_phi = append_phi_at_block_top(func, block, base_ty, base_args);
        let payload_phi = append_phi_at_block_top(func, block, payload_ty, payload_args);
        let new_insert = append_non_phi_after_phi_region(
            func,
            block,
            data::InsertValue::new_unchecked(func.inst_set(), base_phi, idx_value, payload_phi),
            result_ty,
        );

        func.dfg.change_to_alias(result, new_insert);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }

    fn build_value_for_aggregate_slice(
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
                self.build_value_for_aggregate_slice(
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
            let insert_idx = inst_const_index(func, *insert.idx())?;
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
                return self.build_value_for_aggregate_slice(
                    func,
                    inst,
                    source,
                    source_ty,
                    source_slice,
                    child_ty,
                );
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
        compatible.then(|| bitcast_before_inst(func, inst, value, to_ty))
    }
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

fn bitcast_before_inst(func: &mut Function, inst: InstId, value: ValueId, to_ty: Type) -> ValueId {
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
        ty: to_ty,
    });
    cursor.attach_result(func, bitcast_inst, cast_value);
    cast_value
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
        ty,
    });
    cursor.attach_result(func, insert_inst, insert_value);
    insert_value
}

fn append_phi_at_block_top(
    func: &mut Function,
    block: BlockId,
    ty: Type,
    args: Vec<(ValueId, BlockId)>,
) -> ValueId {
    let phi = control_flow::Phi::new_unchecked(func.inst_set(), args);
    let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(block));
    let inst = cursor.prepend_inst_data(func, phi);
    let value = func.dfg.make_value(Value::Inst { inst, ty });
    cursor.attach_result(func, inst, value);
    value
}

fn append_non_phi_after_phi_region<I: sonatina_ir::Inst>(
    func: &mut Function,
    block: BlockId,
    inst_data: I,
    ty: Type,
) -> ValueId {
    let mut last_phi = None;
    for inst in func.layout.iter_inst(block) {
        if func.dfg.is_phi(inst) {
            last_phi = Some(inst);
            continue;
        }
        break;
    }

    let mut cursor = if let Some(last_phi) = last_phi {
        InstInserter::at_location(CursorLocation::At(last_phi))
    } else {
        InstInserter::at_location(CursorLocation::BlockTop(block))
    };
    let inst = cursor.insert_inst_data(func, inst_data);
    let value = func.dfg.make_value(Value::Inst { inst, ty });
    cursor.attach_result(func, inst, value);
    value
}

fn inst_const_index(func: &Function, v: ValueId) -> Option<u32> {
    shape::const_u32(&func.dfg, v)
}

fn equivalent_indices(func: &Function, lhs: ValueId, rhs: ValueId) -> bool {
    lhs == rhs
        || matches!(
            (inst_const_index(func, lhs), inst_const_index(func, rhs)),
            (Some(lhs), Some(rhs)) if lhs == rhs
        )
}

fn is_explicit_undef(func: &Function, v: ValueId) -> bool {
    matches!(func.dfg.value(v), Value::Undef { .. })
}

fn compute_definitely_non_undef_aggregates(func: &Function) -> SecondaryMap<ValueId, bool> {
    let mut definitely_non_undef = SecondaryMap::default();
    for value in func.dfg.values.keys() {
        let ty = func.dfg.value_ty(value);
        if shape::is_supported_aggregate_ty(func.ctx(), ty) {
            definitely_non_undef[value] = !is_explicit_undef(func, value);
        }
    }

    loop {
        let mut changed = false;
        for value in func.dfg.values.keys() {
            let ty = func.dfg.value_ty(value);
            if !shape::is_supported_aggregate_ty(func.ctx(), ty) {
                continue;
            }

            let next = aggregate_is_definitely_non_undef(func, value, &definitely_non_undef);
            if definitely_non_undef[value] != next {
                definitely_non_undef[value] = next;
                changed = true;
            }
        }
        if !changed {
            return definitely_non_undef;
        }
    }
}

fn aggregate_is_definitely_non_undef(
    func: &Function,
    value: ValueId,
    definitely_non_undef: &SecondaryMap<ValueId, bool>,
) -> bool {
    if is_explicit_undef(func, value) {
        return false;
    }

    let ty = func.dfg.value_ty(value);
    let Some(inst) = func.dfg.value_inst(value) else {
        return true;
    };

    if let Some(insert) = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst)) {
        if value_is_definitely_non_undef(func, *insert.dest(), definitely_non_undef) {
            return true;
        }

        let Some(field_count) = shape::aggregate_child_count(func.ctx(), ty) else {
            return false;
        };
        let Some(assignments) = collect_insert_assignments(func, value) else {
            return false;
        };
        return assignments.len() == field_count
            && (0..field_count).all(|idx| {
                let Some(idx_u32) = u32::try_from(idx).ok() else {
                    return false;
                };
                let Some(field) = assignments.get(&idx_u32).copied() else {
                    return false;
                };
                let Some(field_ty) = shape::aggregate_child_ty(func.ctx(), ty, idx_u32) else {
                    return false;
                };
                func.dfg.value_ty(field) == field_ty
                    && value_is_definitely_non_undef(func, field, definitely_non_undef)
            });
    }

    if let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)) {
        return phi.args().iter().any(|&(arg, _)| arg != value)
            && phi.args().iter().all(|&(arg, _)| {
                func.dfg.value_ty(arg) == ty
                    && value_is_definitely_non_undef(func, arg, definitely_non_undef)
            });
    }

    if let Some(extract) = downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst)) {
        return value_is_definitely_non_undef(func, *extract.dest(), definitely_non_undef);
    }

    if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)) {
        return value_is_definitely_non_undef(func, *bitcast.from(), definitely_non_undef);
    }

    false
}

fn value_is_definitely_non_undef(
    func: &Function,
    value: ValueId,
    definitely_non_undef: &SecondaryMap<ValueId, bool>,
) -> bool {
    let ty = func.dfg.value_ty(value);
    if shape::is_supported_aggregate_ty(func.ctx(), ty) {
        definitely_non_undef[value]
    } else {
        !is_explicit_undef(func, value)
    }
}

fn is_identical_field_reinsert(
    func: &Function,
    insert: &data::InsertValue,
    definitely_non_undef: &SecondaryMap<ValueId, bool>,
) -> bool {
    if !definitely_non_undef[*insert.dest()] {
        return false;
    }

    let Some(idx) = inst_const_index(func, *insert.idx()) else {
        return false;
    };

    matches!(
        walk_insert_chain_for_field(func, *insert.dest(), idx),
        AggregateFieldLookup::Found(found) if found == *insert.value()
    ) || func
        .dfg
        .value_inst(*insert.value())
        .is_some_and(|src_inst| {
            downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(src_inst)).is_some_and(
                |extract| {
                    *extract.dest() == *insert.dest()
                        && inst_const_index(func, *extract.idx()) == Some(idx)
                },
            )
        })
}

fn walk_insert_chain_for_field(
    func: &Function,
    aggregate: ValueId,
    target_idx: u32,
) -> AggregateFieldLookup {
    if is_explicit_undef(func, aggregate) {
        let agg_ty = func.dfg.value_ty(aggregate);
        if let Some(field_ty) = shape::aggregate_child_ty(func.ctx(), agg_ty, target_idx) {
            return AggregateFieldLookup::Undef(field_ty);
        }
        return AggregateFieldLookup::Unknown;
    }

    let Some(def_inst) = func.dfg.value_inst(aggregate) else {
        return AggregateFieldLookup::BaseNeedsExtract(aggregate);
    };
    let Some(insert) = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(def_inst))
    else {
        return AggregateFieldLookup::BaseNeedsExtract(aggregate);
    };
    let Some(insert_idx) = inst_const_index(func, *insert.idx()) else {
        return AggregateFieldLookup::Unknown;
    };
    if insert_idx == target_idx {
        return AggregateFieldLookup::Found(*insert.value());
    }
    walk_insert_chain_for_field(func, *insert.dest(), target_idx)
}

fn try_reconstruct_original_aggregate(func: &Function, value: ValueId) -> Option<ValueId> {
    let agg_ty = func.dfg.value_ty(value);
    let field_count = shape::aggregate_child_count(func.ctx(), agg_ty)?;
    if field_count == 0 {
        return None;
    }

    let assignments = collect_insert_assignments(func, value)?;
    if assignments.len() != field_count {
        return None;
    }

    let mut source: Option<ValueId> = None;
    for idx in 0..field_count {
        let idx_u32 = u32::try_from(idx).ok()?;
        let field_val = *assignments.get(&idx_u32)?;
        let mut path = vec![idx_u32];
        let field_source = source_for_path_value(func, field_val, &mut path)?;
        if source.is_none() {
            source = Some(field_source);
        } else if source != Some(field_source) {
            return None;
        }
    }

    let source = source?;
    (!is_explicit_undef(func, source) && func.dfg.value_ty(source) == agg_ty).then_some(source)
}

fn collect_insert_assignments(func: &Function, value: ValueId) -> Option<FxHashMap<u32, ValueId>> {
    let mut assignments: FxHashMap<u32, ValueId> = FxHashMap::default();
    let mut current = value;
    loop {
        let Some(inst) = func.dfg.value_inst(current) else {
            break;
        };
        let Some(insert) = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst))
        else {
            break;
        };
        let idx = inst_const_index(func, *insert.idx())?;
        assignments.entry(idx).or_insert(*insert.value());
        current = *insert.dest();
    }
    Some(assignments)
}

fn source_for_path_value(func: &Function, value: ValueId, path: &mut Vec<u32>) -> Option<ValueId> {
    if let Some(source) = extract_chain_source(func, value, path) {
        return Some(source);
    }

    let value_ty = func.dfg.value_ty(value);
    let child_count = shape::aggregate_child_count(func.ctx(), value_ty)?;
    if child_count == 0 {
        return None;
    }

    let assignments = collect_insert_assignments(func, value)?;
    if assignments.len() != child_count {
        return None;
    }

    let mut source: Option<ValueId> = None;
    for idx in 0..child_count {
        let idx_u32 = u32::try_from(idx).ok()?;
        let field_val = *assignments.get(&idx_u32)?;
        path.push(idx_u32);
        let field_source = source_for_path_value(func, field_val, path)?;
        path.pop();
        if source.is_none() {
            source = Some(field_source);
        } else if source != Some(field_source) {
            return None;
        }
    }

    source
}

fn extract_chain_source(func: &Function, mut value: ValueId, path: &[u32]) -> Option<ValueId> {
    for &idx in path.iter().rev() {
        let inst = func.dfg.value_inst(value)?;
        let extract = downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst))?;
        if inst_const_index(func, *extract.idx()) != Some(idx) {
            return None;
        }
        value = *extract.dest();
    }
    Some(value)
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
    fn combine_rewrites_extracts_through_compatible_aggregate_bitcasts() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i256 };
type @pair = { i256, i256 };
type @nested = { @inner, i256 };

func private %f(v0.@pair) -> i256 {
block0:
    v1.@nested = bitcast v0 @nested;
    v2.@inner = extract_value v1 0.i8;
    v3.i256 = extract_value v2 0.i8;
    return v3;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(AggregateCombine::default().run(func));
        });

        module.func_store.view(func_ref, |func| {
            let mut extract_count = 0;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    let Some(extract) =
                        downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst))
                    else {
                        continue;
                    };
                    extract_count += 1;

                    if let Some(dest_inst) = func.dfg.value_inst(*extract.dest())
                        && let Some(bitcast) =
                            downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(dest_inst))
                    {
                        let from_ty = func.dfg.value_ty(*bitcast.from());
                        let to_ty = func.dfg.value_ty(*extract.dest());
                        assert!(
                            !shape::is_supported_aggregate_ty(func.ctx(), from_ty)
                                || !shape::is_supported_aggregate_ty(func.ctx(), to_ty),
                            "compatible aggregate bitcast should not remain directly under extract"
                        );
                    }
                }
            }
            assert_eq!(
                extract_count, 1,
                "bitcasted nested extract chain should collapse"
            );
        });
    }
}
