use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, Function, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
};

use super::shape;

#[derive(Default)]
pub struct AggregateCombine {
    changed: bool,
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
        func.rebuild_users();

        loop {
            let mut iter_changed = false;
            let blocks: Vec<_> = func.layout.iter_block().collect();
            for block in blocks {
                let insts: Vec<_> = func.layout.iter_inst(block).collect();
                for inst in insts {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    iter_changed |= self.try_rewrite_inst(func, inst);
                }
            }
            if !iter_changed {
                break;
            }
            self.changed = true;
            func.rebuild_users();
        }

        if self.changed {
            func.rebuild_users();
        }
        self.changed
    }

    fn try_rewrite_inst(&mut self, func: &mut Function, inst: InstId) -> bool {
        if downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_extract(func, inst)
        } else if downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_insert(func, inst)
        } else if downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_phi(func, inst)
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
                    return false;
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
            AggregateFieldLookup::BaseNeedsExtract(_) | AggregateFieldLookup::Unknown => false,
        }
    }

    fn try_rewrite_insert(&mut self, func: &mut Function, inst: InstId) -> bool {
        let Some(insert) = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst))
        else {
            return false;
        };
        let insert = insert.clone();
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };

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

        // AC5: insert identical field back into aggregate.
        if !is_explicit_undef(func, *insert.dest())
            && let Some(src_inst) = func.dfg.value_inst(*insert.value())
            && let Some(extract) =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(src_inst))
            && *extract.dest() == *insert.dest()
            && equivalent_indices(func, *extract.idx(), *insert.idx())
        {
            if func.dfg.value_ty(*insert.dest()) != func.dfg.value_ty(result) {
                return false;
            }
            func.dfg.change_to_alias(result, *insert.dest());
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
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

    fn try_rewrite_phi(&mut self, func: &mut Function, inst: InstId) -> bool {
        self.try_rewrite_phi_of_extracts(func, inst) || self.try_rewrite_phi_of_inserts(func, inst)
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

    fn try_rewrite_phi_of_inserts(&mut self, func: &mut Function, inst: InstId) -> bool {
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
