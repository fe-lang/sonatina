use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
};

use super::{promotion::PromotionSsaBuilder, shape};

type LeafValues = SmallVec<[ValueId; 4]>;

#[derive(Debug, Clone, Copy)]
struct Projection {
    alloca_inst: InstId,
    slice: shape::AggregateSlice,
}

#[derive(Clone)]
struct PromotedAlloca {
    inst: InstId,
    shape: shape::AggregateShape,
    leaf_vars: SmallVec<[sonatina_ir::builder::Variable; 4]>,
}

#[derive(Default)]
pub struct AggregateScalarize {
    changed: bool,
}

impl AggregateScalarize {
    pub fn run(&mut self, func: &mut Function) -> bool {
        self.changed = false;
        let module = func.ctx().clone();
        func.rebuild_users();

        let (mut promoted_allocas, mut projection_of) = self.find_promotable_allocas(func, &module);
        let scalarizable = loop {
            let scalarizable = self.compute_scalarizable_aggregates(func, &module, &projection_of);
            let removed = self.filter_promotable_allocas(
                func,
                &module,
                &mut promoted_allocas,
                &mut projection_of,
                &scalarizable,
            );
            if !removed {
                break scalarizable;
            }
        };
        if !promoted_allocas.is_empty() || scalarizable.values().any(|v| *v) {
            self.changed = true;
        } else {
            return false;
        }

        let mut ssa = PromotionSsaBuilder::new();
        self.append_block_preds(func, &mut ssa);
        self.setup_promoted_leaf_vars(func, &mut ssa, &mut promoted_allocas);

        let mut scalarized_agg: SecondaryMap<ValueId, Option<LeafValues>> = SecondaryMap::default();
        let mut scalar_phi_results: SecondaryMap<ValueId, Option<LeafValues>> =
            SecondaryMap::default();

        let agg_phi_insts = self.create_scalar_phi_placeholders(
            func,
            &module,
            &scalarizable,
            &mut scalarized_agg,
            &mut scalar_phi_results,
        );

        let promoted_by_inst: FxHashMap<InstId, PromotedAlloca> = promoted_allocas
            .into_iter()
            .map(|pa| (pa.inst, pa))
            .collect();

        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                self.rewrite_promoted_load_store(
                    func,
                    &module,
                    block,
                    inst,
                    &projection_of,
                    &promoted_by_inst,
                    &scalarizable,
                    &mut scalarized_agg,
                    &mut ssa,
                );
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                self.rewrite_scalarizable_insert_extract(
                    func,
                    &module,
                    block,
                    inst,
                    &scalarizable,
                    &mut scalarized_agg,
                );
            }
        }

        self.fill_scalar_phi_args(
            func,
            &module,
            &agg_phi_insts,
            &scalar_phi_results,
            &mut scalarized_agg,
        );
        ssa.seal_all(func);
        self.cleanup_dead_promoted_allocas(func, &projection_of, &promoted_by_inst);

        if self.changed {
            func.rebuild_users();
        }
        self.changed
    }

    fn append_block_preds(&self, func: &Function, ssa: &mut PromotionSsaBuilder) {
        for block in func.layout.iter_block() {
            let Some(term) = func.layout.last_inst_of(block) else {
                continue;
            };
            let Some(branch) = func.dfg.branch_info(term) else {
                continue;
            };
            for dest in branch.dests() {
                ssa.append_pred(dest, block);
            }
        }
    }

    fn setup_promoted_leaf_vars(
        &self,
        func: &mut Function,
        ssa: &mut PromotionSsaBuilder,
        promoted_allocas: &mut [PromotedAlloca],
    ) {
        let entry = func
            .layout
            .entry_block()
            .expect("function has no entry block");
        for promoted in promoted_allocas {
            for leaf in &promoted.shape.leaves {
                let var = ssa.declare_var(leaf.ty);
                promoted.leaf_vars.push(var);
                let undef = func.dfg.make_undef_value(leaf.ty);
                ssa.def_var(var, undef, entry);
            }
        }
    }

    fn find_promotable_allocas(
        &self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
    ) -> (
        Vec<PromotedAlloca>,
        SecondaryMap<ValueId, Option<Projection>>,
    ) {
        let mut promoted = Vec::new();
        let mut projection_of: SecondaryMap<ValueId, Option<Projection>> = SecondaryMap::default();
        let Some(entry) = func.layout.entry_block() else {
            return (promoted, projection_of);
        };

        let mut entry_allocas: Vec<(InstId, ValueId, Type, shape::AggregateShape)> = Vec::new();
        for inst in func.layout.iter_inst(entry) {
            let Some(alloca) = downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst))
            else {
                continue;
            };
            let Some(ptr_value) = func.dfg.inst_result(inst) else {
                continue;
            };
            let ty = *alloca.ty();
            let Some(shape) = shape::aggregate_shape(module, ty) else {
                continue;
            };
            if shape.leaves.len() > 4 {
                continue;
            }
            entry_allocas.push((inst, ptr_value, ty, shape));
        }

        for (inst, ptr_value, alloca_ty, shape_data) in entry_allocas {
            let whole_slice = shape::AggregateSlice {
                ty: alloca_ty,
                first_leaf: 0,
                leaf_count: shape_data.leaves.len(),
            };
            let mut local_projection: FxHashMap<ValueId, Projection> = FxHashMap::default();
            local_projection.insert(
                ptr_value,
                Projection {
                    alloca_inst: inst,
                    slice: whole_slice,
                },
            );
            let mut queue = vec![ptr_value];
            let mut rejected = false;

            while let Some(ptr) = queue.pop() {
                let projection = local_projection
                    .get(&ptr)
                    .copied()
                    .expect("projection queue value missing");
                let users: Vec<_> = func.dfg.users(ptr).copied().collect();
                for user in users {
                    if !func.layout.is_inst_inserted(user) {
                        continue;
                    }

                    if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(user))
                    {
                        let Some(base) = gep.values().first().copied() else {
                            rejected = true;
                            break;
                        };
                        if base != ptr {
                            rejected = true;
                            break;
                        }
                        let Some(result) = func.dfg.inst_result(user) else {
                            rejected = true;
                            break;
                        };
                        let Some(sub) = shape::aggregate_slice_for_gep_path(
                            module,
                            projection.slice.ty,
                            &gep.values()[1..],
                            &func.dfg,
                        ) else {
                            rejected = true;
                            break;
                        };
                        let composed = Projection {
                            alloca_inst: inst,
                            slice: shape::AggregateSlice {
                                ty: sub.ty,
                                first_leaf: projection.slice.first_leaf + sub.first_leaf,
                                leaf_count: sub.leaf_count,
                            },
                        };
                        if let Some(prev) = local_projection.insert(result, composed)
                            && (prev.slice.first_leaf != composed.slice.first_leaf
                                || prev.slice.leaf_count != composed.slice.leaf_count
                                || prev.slice.ty != composed.slice.ty)
                        {
                            rejected = true;
                            break;
                        }
                        queue.push(result);
                        continue;
                    }

                    if let Some(mload) =
                        downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(user))
                        && *mload.addr() == ptr
                    {
                        let ty = *mload.ty();
                        let ok = if shape::is_supported_aggregate_ty(module, ty) {
                            ty == projection.slice.ty
                        } else {
                            projection.slice.leaf_count == 1 && ty == projection.slice.ty
                        };
                        if !ok {
                            rejected = true;
                            break;
                        }
                        continue;
                    }

                    if let Some(mstore) =
                        downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(user))
                        && *mstore.addr() == ptr
                    {
                        let ty = *mstore.ty();
                        let ok = if shape::is_supported_aggregate_ty(module, ty) {
                            ty == projection.slice.ty
                        } else {
                            projection.slice.leaf_count == 1 && ty == projection.slice.ty
                        };
                        if !ok {
                            rejected = true;
                            break;
                        }
                        continue;
                    }

                    rejected = true;
                    break;
                }
                if rejected {
                    break;
                }
            }

            if rejected {
                continue;
            }

            for (value, projection) in local_projection {
                projection_of[value] = Some(projection);
            }

            promoted.push(PromotedAlloca {
                inst,
                shape: shape_data,
                leaf_vars: SmallVec::new(),
            });
        }

        (promoted, projection_of)
    }

    fn filter_promotable_allocas(
        &self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        promoted_allocas: &mut Vec<PromotedAlloca>,
        projection_of: &mut SecondaryMap<ValueId, Option<Projection>>,
        scalarizable: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        let before = promoted_allocas.len();
        promoted_allocas.retain(|promoted| {
            self.promoted_alloca_can_scalarize(
                func,
                module,
                promoted.inst,
                projection_of,
                scalarizable,
            )
        });

        let kept: FxHashSet<InstId> = promoted_allocas
            .iter()
            .map(|promoted| promoted.inst)
            .collect();
        for value in func.dfg.values.keys() {
            if let Some(projection) = projection_of[value]
                && !kept.contains(&projection.alloca_inst)
            {
                projection_of[value] = None;
            }
        }
        promoted_allocas.len() != before
    }

    fn promoted_alloca_can_scalarize(
        &self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        alloca_inst: InstId,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        scalarizable: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        for ptr in func.dfg.values.keys() {
            let Some(projection) = projection_of[ptr] else {
                continue;
            };
            if projection.alloca_inst != alloca_inst {
                continue;
            }

            for &user in func.dfg.users(ptr) {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }
                if let Some(mload) = downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(user))
                    && *mload.addr() == ptr
                    && shape::is_supported_aggregate_ty(module, *mload.ty())
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if !scalarizable[result] {
                        return false;
                    }
                }
                if let Some(mstore) =
                    downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(user))
                    && *mstore.addr() == ptr
                    && shape::is_supported_aggregate_ty(module, *mstore.ty())
                    && (!scalarizable[*mstore.value()]
                        || func.dfg.value_ty(*mstore.value()) != *mstore.ty())
                {
                    return false;
                }
            }
        }
        true
    }

    fn compute_scalarizable_aggregates(
        &self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
    ) -> SecondaryMap<ValueId, bool> {
        let mut scalarizable: SecondaryMap<ValueId, bool> = SecondaryMap::default();

        for value in func.dfg.values.keys() {
            let ty = func.dfg.value_ty(value);
            if !shape::is_supported_aggregate_ty(module, ty) {
                continue;
            }
            let ok = match func.dfg.value(value) {
                Value::Undef { .. } => true,
                Value::Arg { .. } => false,
                Value::Immediate { .. } | Value::Global { .. } => false,
                Value::Inst { inst, .. } => {
                    if func.dfg.call_info(*inst).is_some() {
                        false
                    } else if downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(*inst))
                        .is_some()
                        || downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(*inst))
                            .is_some()
                        || downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(*inst))
                            .is_some()
                    {
                        true
                    } else if let Some(mload) =
                        downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(*inst))
                    {
                        projection_of[*mload.addr()].is_some()
                    } else {
                        false
                    }
                }
            };
            scalarizable[value] = ok;
        }

        loop {
            let mut changed = false;
            for value in func.dfg.values.keys() {
                if !scalarizable[value] {
                    continue;
                }
                if !self.scalarizable_definition_is_closed(
                    func,
                    module,
                    projection_of,
                    &scalarizable,
                    value,
                ) || !self.scalarizable_uses_are_closed(
                    func,
                    module,
                    projection_of,
                    &scalarizable,
                    value,
                ) {
                    scalarizable[value] = false;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        scalarizable
    }

    fn scalarizable_definition_is_closed(
        &self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        scalarizable: &SecondaryMap<ValueId, bool>,
        value: ValueId,
    ) -> bool {
        match func.dfg.value(value) {
            Value::Undef { .. } => true,
            Value::Arg { .. } | Value::Immediate { .. } | Value::Global { .. } => false,
            Value::Inst { inst, .. } => {
                if let Some(insert) =
                    downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let agg_ty = func.dfg.value_ty(value);
                    let Some(idx) = shape::const_u32(&func.dfg, *insert.idx()) else {
                        return false;
                    };
                    let Some(slice) = shape::aggregate_slice_for_index(module, agg_ty, idx) else {
                        return false;
                    };
                    if func.dfg.value_ty(*insert.dest()) != agg_ty || !scalarizable[*insert.dest()]
                    {
                        return false;
                    }
                    if func.dfg.value_ty(*insert.value()) != slice.ty {
                        return false;
                    }
                    if shape::is_supported_aggregate_ty(module, slice.ty)
                        && !scalarizable[*insert.value()]
                    {
                        return false;
                    }
                    true
                } else if let Some(extract) =
                    downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let src_ty = func.dfg.value_ty(*extract.dest());
                    if !shape::is_supported_aggregate_ty(module, src_ty)
                        || !scalarizable[*extract.dest()]
                    {
                        return false;
                    }
                    let Some(idx) = shape::const_u32(&func.dfg, *extract.idx()) else {
                        return false;
                    };
                    let Some(slice) = shape::aggregate_slice_for_index(module, src_ty, idx) else {
                        return false;
                    };
                    slice.ty == func.dfg.value_ty(value)
                } else if let Some(phi) =
                    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let value_ty = func.dfg.value_ty(value);
                    phi.args()
                        .iter()
                        .all(|&(arg, _)| scalarizable[arg] && func.dfg.value_ty(arg) == value_ty)
                } else if let Some(mload) =
                    downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(*inst))
                {
                    shape::is_supported_aggregate_ty(module, *mload.ty())
                        && projection_of[*mload.addr()].is_some()
                        && *mload.ty() == func.dfg.value_ty(value)
                } else {
                    false
                }
            }
        }
    }

    fn scalarizable_uses_are_closed(
        &self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        scalarizable: &SecondaryMap<ValueId, bool>,
        value: ValueId,
    ) -> bool {
        for &user in func.dfg.users(value) {
            if !func.layout.is_inst_inserted(user) {
                continue;
            }

            if let Some(insert) =
                downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(user))
                && (*insert.dest() == value || *insert.value() == value)
            {
                let Some(res) = func.dfg.inst_result(user) else {
                    return false;
                };
                if !scalarizable[res] {
                    return false;
                }
                continue;
            }

            if let Some(extract) =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(user))
                && *extract.dest() == value
            {
                let Some(res) = func.dfg.inst_result(user) else {
                    return false;
                };
                let res_ty = func.dfg.value_ty(res);
                if shape::is_supported_aggregate_ty(module, res_ty) && !scalarizable[res] {
                    return false;
                }
                continue;
            }

            if let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(user))
                && phi.args().iter().any(|(arg, _)| *arg == value)
            {
                let Some(res) = func.dfg.inst_result(user) else {
                    return false;
                };
                if !scalarizable[res] {
                    return false;
                }
                continue;
            }

            if let Some(mstore) = downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(user))
                && *mstore.value() == value
            {
                if !shape::is_supported_aggregate_ty(module, *mstore.ty()) {
                    return false;
                }
                if projection_of[*mstore.addr()].is_none() {
                    return false;
                }
                continue;
            }

            return false;
        }
        true
    }

    fn create_scalar_phi_placeholders(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        scalarizable: &SecondaryMap<ValueId, bool>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
        scalar_phi_results: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) -> Vec<InstId> {
        let mut phis = Vec::new();
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_none() {
                    continue;
                }
                let Some(result) = func.dfg.inst_result(inst) else {
                    continue;
                };
                if !scalarizable[result] {
                    continue;
                }
                let agg_ty = func.dfg.value_ty(result);
                let shape = shape::aggregate_shape(module, agg_ty)
                    .unwrap_or_else(|| panic!("missing aggregate shape for scalarizable phi"));

                let mut leaf_phis: LeafValues = SmallVec::new();
                for leaf in shape.leaves {
                    let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(block));
                    let phi = control_flow::Phi::new_unchecked(func.inst_set(), Vec::new());
                    let phi_inst = cursor.prepend_inst_data(func, phi);
                    let phi_res = func.dfg.make_value(Value::Inst {
                        inst: phi_inst,
                        ty: leaf.ty,
                    });
                    cursor.attach_result(func, phi_inst, phi_res);
                    leaf_phis.push(phi_res);
                }
                scalar_phi_results[result] = Some(leaf_phis.clone());
                scalarized_agg[result] = Some(leaf_phis);
                phis.push(inst);
            }
        }
        phis
    }

    #[allow(clippy::too_many_arguments)]
    fn rewrite_promoted_load_store(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        block: BlockId,
        inst: InstId,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        promoted_by_inst: &FxHashMap<InstId, PromotedAlloca>,
        scalarizable: &SecondaryMap<ValueId, bool>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
        ssa: &mut PromotionSsaBuilder,
    ) {
        if let Some(mload) = downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let Some(projection) = projection_of[*mload.addr()] else {
                return;
            };
            let Some(promoted) = promoted_by_inst.get(&projection.alloca_inst) else {
                return;
            };

            let ty = *mload.ty();
            let Some(result) = func.dfg.inst_result(inst) else {
                return;
            };
            if shape::is_supported_aggregate_ty(module, ty) {
                if !scalarizable[result] {
                    return;
                }
                let mut leaves: LeafValues = SmallVec::new();
                for idx in projection.slice.first_leaf
                    ..projection.slice.first_leaf + projection.slice.leaf_count
                {
                    let var = promoted.leaf_vars[idx];
                    leaves.push(ssa.use_var(func, var, block));
                }
                scalarized_agg[result] = Some(leaves);
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                return;
            }

            if projection.slice.leaf_count != 1 {
                return;
            }
            let var = promoted.leaf_vars[projection.slice.first_leaf];
            let val = ssa.use_var(func, var, block);
            func.dfg.change_to_alias(result, val);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        let Some(mstore) = downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst)).cloned()
        else {
            return;
        };
        let Some(projection) = projection_of[*mstore.addr()] else {
            return;
        };
        let Some(promoted) = promoted_by_inst.get(&projection.alloca_inst) else {
            return;
        };
        let ty = *mstore.ty();

        if shape::is_supported_aggregate_ty(module, ty) {
            let Some(payload_leaves) =
                self.scalarized_leaves_of_value(func, module, *mstore.value(), ty, scalarized_agg)
            else {
                return;
            };
            if payload_leaves.len() != projection.slice.leaf_count {
                return;
            }
            for (i, val) in payload_leaves.into_iter().enumerate() {
                let var = promoted.leaf_vars[projection.slice.first_leaf + i];
                ssa.def_var(var, val, block);
            }
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        if projection.slice.leaf_count != 1 {
            return;
        }
        let var = promoted.leaf_vars[projection.slice.first_leaf];
        ssa.def_var(var, *mstore.value(), block);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn rewrite_scalarizable_insert_extract(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        _block: BlockId,
        inst: InstId,
        scalarizable: &SecondaryMap<ValueId, bool>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        if let Some(insert) =
            downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let Some(result) = func.dfg.inst_result(inst) else {
                return;
            };
            if !scalarizable[result] {
                return;
            }
            let agg_ty = func.dfg.value_ty(result);
            let Some(idx) = shape::const_u32(&func.dfg, *insert.idx()) else {
                return;
            };
            let Some(slice) = shape::aggregate_slice_for_index(module, agg_ty, idx) else {
                return;
            };

            let Some(mut base_leaves) = self.scalarized_leaves_of_value(
                func,
                module,
                *insert.dest(),
                agg_ty,
                scalarized_agg,
            ) else {
                return;
            };
            let Some(payload_leaves) = self.scalarized_leaves_of_value(
                func,
                module,
                *insert.value(),
                slice.ty,
                scalarized_agg,
            ) else {
                return;
            };
            if payload_leaves.len() != slice.leaf_count {
                return;
            }
            for (i, val) in payload_leaves.into_iter().enumerate() {
                base_leaves[slice.first_leaf + i] = val;
            }
            scalarized_agg[result] = Some(base_leaves);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        let Some(extract) =
            downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst)).cloned()
        else {
            return;
        };
        let Some(result) = func.dfg.inst_result(inst) else {
            return;
        };
        let dest_ty = func.dfg.value_ty(*extract.dest());
        if !shape::is_supported_aggregate_ty(module, dest_ty) {
            return;
        }
        let Some(dest_leaves) =
            self.scalarized_leaves_of_value(func, module, *extract.dest(), dest_ty, scalarized_agg)
        else {
            return;
        };
        let Some(idx) = shape::const_u32(&func.dfg, *extract.idx()) else {
            return;
        };
        let Some(slice) = shape::aggregate_slice_for_index(module, dest_ty, idx) else {
            return;
        };
        let result_ty = func.dfg.value_ty(result);
        if shape::is_supported_aggregate_ty(module, result_ty) {
            if !scalarizable[result] {
                return;
            }
            let mut leaves = LeafValues::new();
            for i in 0..slice.leaf_count {
                leaves.push(dest_leaves[slice.first_leaf + i]);
            }
            scalarized_agg[result] = Some(leaves);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        let replacement = dest_leaves[slice.first_leaf];
        func.dfg.change_to_alias(result, replacement);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn fill_scalar_phi_args(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        agg_phi_insts: &[InstId],
        scalar_phi_results: &SecondaryMap<ValueId, Option<LeafValues>>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        for &inst in agg_phi_insts {
            if !func.layout.is_inst_inserted(inst) {
                continue;
            }
            let Some(result) = func.dfg.inst_result(inst) else {
                continue;
            };
            let agg_ty = func.dfg.value_ty(result);
            let Some(phi) =
                downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).cloned()
            else {
                continue;
            };
            let Some(leaf_phis) = scalar_phi_results[result].clone() else {
                continue;
            };

            for &(incoming, pred) in phi.args() {
                let Some(incoming_leaves) =
                    self.scalarized_leaves_of_value(func, module, incoming, agg_ty, scalarized_agg)
                else {
                    panic!("aggregate phi incoming value is not scalarized");
                };
                if incoming_leaves.len() != leaf_phis.len() {
                    panic!("aggregate phi scalar leaf mismatch");
                }
                for (leaf_phi, leaf_val) in leaf_phis.iter().zip(incoming_leaves.iter()) {
                    let phi_inst = func
                        .dfg
                        .value_inst(*leaf_phi)
                        .unwrap_or_else(|| panic!("scalar phi value has no defining inst"));
                    func.dfg.append_phi_arg(phi_inst, *leaf_val, pred);
                }
            }

            scalarized_agg[result] = Some(leaf_phis);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        }
    }

    fn cleanup_dead_promoted_allocas(
        &mut self,
        func: &mut Function,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        promoted_by_inst: &FxHashMap<InstId, PromotedAlloca>,
    ) {
        if promoted_by_inst.is_empty() {
            return;
        }
        let promoted_insts: FxHashSet<InstId> = promoted_by_inst.keys().copied().collect();

        loop {
            let mut removed_any = false;
            func.rebuild_users();
            for value in func.dfg.values.keys() {
                let Some(projection) = projection_of[value] else {
                    continue;
                };
                if !promoted_insts.contains(&projection.alloca_inst) {
                    continue;
                }
                let Some(inst) = func.dfg.value_inst(value) else {
                    continue;
                };
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                if downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst)).is_none()
                    && downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)).is_none()
                {
                    continue;
                }
                if func
                    .dfg
                    .users(value)
                    .copied()
                    .any(|user| func.layout.is_inst_inserted(user))
                {
                    continue;
                }

                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                removed_any = true;
            }
            if !removed_any {
                break;
            }
            self.changed = true;
        }
    }

    fn scalarized_leaves_of_value(
        &self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        value: ValueId,
        ty: Type,
        scalarized_agg: &SecondaryMap<ValueId, Option<LeafValues>>,
    ) -> Option<LeafValues> {
        if !shape::is_supported_aggregate_ty(module, ty) {
            return (func.dfg.value_ty(value) == ty).then(|| smallvec![value]);
        }

        if is_explicit_undef(func, value) {
            let agg_shape = shape::aggregate_shape(module, ty)?;
            let mut leaves = LeafValues::new();
            for leaf in agg_shape.leaves {
                leaves.push(func.dfg.make_undef_value(leaf.ty));
            }
            return Some(leaves);
        }

        scalarized_agg[value].clone()
    }
}

fn is_explicit_undef(func: &Function, value: ValueId) -> bool {
    matches!(func.dfg.value(value), Value::Undef { .. })
}
