use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, control_flow, data, downcast},
};

use crate::cfg_edit::{CfgEditor, CleanupMode};

use super::{
    cleanup::DeadPureInstCleanup, promotion::SsaBuilder, reconstruct::bitcast_before_inst, shape,
};

type LeafValues = SmallVec<[ValueId; 4]>;

#[derive(Debug, Clone, Copy)]
struct Projection {
    alloca_inst: InstId,
    slice: shape::AggregateSlice,
}

#[derive(Clone)]
struct PromotedAlloca {
    inst: InstId,
    seed_block: BlockId,
    shape: shape::AggregateShape,
    leaf_vars: SmallVec<[sonatina_ir::builder::Variable; 4]>,
}

#[derive(Default)]
pub struct AggregateScalarize {
    changed: bool,
    dead_pure_cleanup: DeadPureInstCleanup,
    layout_cache: shape::AggregateLayoutCache,
}

impl AggregateScalarize {
    pub fn run(&mut self, func: &mut Function) -> bool {
        self.changed = false;
        self.layout_cache.clear();
        let module = func.ctx().clone();
        func.rebuild_users();
        self.assert_cfg_cleaned_up(func);

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

        self.canonicalize_promoted_allocas(func, &mut promoted_allocas);

        let mut ssa = SsaBuilder::new();
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
                self.rewrite_scalarizable_bitcast(
                    func,
                    &module,
                    inst,
                    &scalarizable,
                    &mut scalarized_agg,
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
        self.simplify_scalar_phi_results(func, &mut scalar_phi_results);
        self.changed |= self.cleanup_scalarized_artifacts(func, &projection_of, &promoted_by_inst);

        if self.changed {
            func.rebuild_users();
        }
        self.changed
    }

    fn assert_cfg_cleaned_up(&self, func: &Function) {
        let Some(entry) = func.layout.entry_block() else {
            return;
        };

        let mut reachable = FxHashSet::default();
        let mut worklist = vec![entry];
        while let Some(block) = worklist.pop() {
            if !reachable.insert(block) {
                continue;
            }
            let Some(term) = func.layout.last_inst_of(block) else {
                continue;
            };
            let Some(branch) = func.dfg.branch_info(term) else {
                continue;
            };
            worklist.extend(branch.dests());
        }

        if let Some(block) = func
            .layout
            .iter_block()
            .find(|block| !reachable.contains(block))
        {
            panic!(
                "AggregateScalarize requires CfgCleanup to remove unreachable blocks first (found unreachable block {})",
                block.as_u32()
            );
        }
    }

    fn append_block_preds(&self, func: &Function, ssa: &mut SsaBuilder) {
        for block in func.layout.iter_block() {
            let Some(term) = func.layout.last_inst_of(block) else {
                continue;
            };
            let Some(branch) = func.dfg.branch_info(term) else {
                continue;
            };
            let mut seen = FxHashSet::default();
            for dest in branch.dests() {
                if seen.insert(dest) {
                    ssa.append_pred(dest, block);
                }
            }
        }
    }

    fn setup_promoted_leaf_vars(
        &self,
        func: &mut Function,
        ssa: &mut SsaBuilder,
        promoted_allocas: &mut [PromotedAlloca],
    ) {
        for promoted in promoted_allocas {
            self.assert_promoted_alloca_seed_block(func, promoted);
            for leaf in &promoted.shape.leaves {
                let var = ssa.declare_var(leaf.ty);
                promoted.leaf_vars.push(var);
                let undef = func.dfg.make_undef_value(leaf.ty);
                ssa.def_var(var, undef, promoted.seed_block);
            }
        }
    }

    fn canonicalize_promoted_allocas(
        &self,
        func: &mut Function,
        promoted_allocas: &mut Vec<PromotedAlloca>,
    ) {
        if promoted_allocas.is_empty() {
            return;
        }

        let mut inst_order = FxHashMap::default();
        for (idx, inst) in func
            .layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .enumerate()
        {
            inst_order.insert(inst, idx);
        }
        promoted_allocas.sort_by_key(|promoted| inst_order[&promoted.inst]);

        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        for promoted in promoted_allocas {
            let block = editor.func().layout.inst_block(promoted.inst);
            promoted.seed_block = if first_non_phi_inst(editor.func(), block) == Some(promoted.inst)
            {
                block
            } else {
                editor.split_block_at(promoted.inst).1
            };
        }
    }

    fn assert_promoted_alloca_seed_block(&self, func: &Function, promoted: &PromotedAlloca) {
        assert_eq!(
            func.layout.inst_block(promoted.inst),
            promoted.seed_block,
            "promoted alloca {} should live in its seed block {}",
            promoted.inst.as_u32(),
            promoted.seed_block.as_u32()
        );
        assert_eq!(
            first_non_phi_inst(func, promoted.seed_block),
            Some(promoted.inst),
            "promoted alloca {} should be first non-phi in seed block {}",
            promoted.inst.as_u32(),
            promoted.seed_block.as_u32()
        );
    }

    fn find_promotable_allocas(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
    ) -> (
        Vec<PromotedAlloca>,
        SecondaryMap<ValueId, Option<Projection>>,
    ) {
        let mut promoted = Vec::new();
        let mut projection_of: SecondaryMap<ValueId, Option<Projection>> = SecondaryMap::default();

        let mut allocas: Vec<(InstId, ValueId, Type, shape::AggregateShape)> = Vec::new();
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                let Some((ptr_value, ty)) =
                    downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst))
                        .map(|alloca| (func.dfg.inst_result(inst), *alloca.ty()))
                        .or_else(|| {
                            downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                                .map(|obj_alloc| (func.dfg.inst_result(inst), *obj_alloc.ty()))
                        })
                else {
                    continue;
                };
                let Some(ptr_value) = ptr_value else {
                    continue;
                };
                let Some(shape) = self.aggregate_shape(module, ty) else {
                    continue;
                };
                if shape.leaves.len() > 4 {
                    continue;
                }
                allocas.push((inst, ptr_value, ty, shape));
            }
        }

        for (inst, ptr_value, alloca_ty, shape_data) in allocas {
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
            let mut dead_use_cache: FxHashMap<InstId, bool> = FxHashMap::default();

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

                    if let Some(bitcast) =
                        downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(user))
                        && *bitcast.from() == ptr
                        && let Some(result) = func.dfg.inst_result(user)
                        && let Some(slice) = self.bitcast_projection_slice(
                            module,
                            projection.slice,
                            func.dfg.value_ty(result),
                        )
                    {
                        let composed = Projection {
                            alloca_inst: inst,
                            slice,
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

                    if let Some(obj_proj) =
                        downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(user))
                    {
                        let Some((&base, indices)) = obj_proj.values().split_first() else {
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
                        let Some(sub) = shape::aggregate_slice_for_object_path(
                            module,
                            projection.slice.ty,
                            indices,
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

                    if let Some(obj_index) =
                        downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(user))
                        && *obj_index.object() == ptr
                    {
                        let Some(result) = func.dfg.inst_result(user) else {
                            rejected = true;
                            break;
                        };
                        let Some(sub) = shape::aggregate_slice_for_object_path(
                            module,
                            projection.slice.ty,
                            &[*obj_index.index()],
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
                        if !self.projection_slice_can_view_as(module, projection.slice, ty) {
                            rejected = true;
                            break;
                        }
                        continue;
                    }

                    if let Some(obj_load) =
                        downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(user))
                        && *obj_load.object() == ptr
                    {
                        let Some(result) = func.dfg.inst_result(user) else {
                            rejected = true;
                            break;
                        };
                        let ty = func.dfg.value_ty(result);
                        if !self.projection_slice_can_view_as(module, projection.slice, ty) {
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
                        if !self.projection_slice_can_view_as(module, projection.slice, ty) {
                            rejected = true;
                            break;
                        }
                        continue;
                    }

                    if let Some(obj_store) =
                        downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(user))
                        && *obj_store.object() == ptr
                    {
                        let ty = func.dfg.value_ty(*obj_store.value());
                        if !self.projection_slice_can_view_as(module, projection.slice, ty) {
                            rejected = true;
                            break;
                        }
                        continue;
                    }

                    if is_dead_inst_tree(func, user, &mut dead_use_cache, &mut FxHashSet::default())
                    {
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
                seed_block: func.layout.inst_block(inst),
                shape: shape_data,
                leaf_vars: SmallVec::new(),
            });
        }

        (promoted, projection_of)
    }

    fn filter_promotable_allocas(
        &mut self,
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
        for value in func.dfg.value_ids() {
            if let Some(projection) = projection_of[value]
                && !kept.contains(&projection.alloca_inst)
            {
                projection_of[value] = None;
            }
        }
        promoted_allocas.len() != before
    }

    fn promoted_alloca_can_scalarize(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        alloca_inst: InstId,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        scalarizable: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        for ptr in func.dfg.value_ids() {
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
                if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(user))
                    && *obj_load.object() == ptr
                    && let Some(result) = func.dfg.inst_result(user)
                    && shape::is_supported_aggregate_ty(module, func.dfg.value_ty(result))
                    && !scalarizable[result]
                {
                    return false;
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
                if let Some(obj_store) =
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(user))
                    && *obj_store.object() == ptr
                {
                    let value_ty = func.dfg.value_ty(*obj_store.value());
                    if shape::is_supported_aggregate_ty(module, value_ty)
                        && !scalarizable[*obj_store.value()]
                    {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn compute_scalarizable_aggregates(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
    ) -> SecondaryMap<ValueId, bool> {
        let mut scalarizable: SecondaryMap<ValueId, bool> = SecondaryMap::default();

        for value in func.dfg.value_ids() {
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
                    } else if let Some(bitcast) =
                        downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(*inst))
                    {
                        self.aggregate_bitcast_is_scalarizable(
                            module,
                            func.dfg.value_ty(*bitcast.from()),
                            ty,
                        )
                    } else if let Some(mload) =
                        downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(*inst))
                    {
                        projection_of[*mload.addr()].is_some()
                    } else if let Some(obj_load) =
                        downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(*inst))
                    {
                        projection_of[*obj_load.object()].is_some()
                    } else {
                        false
                    }
                }
            };
            scalarizable[value] = ok;
        }

        loop {
            let mut changed = false;
            for value in func.dfg.value_ids() {
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
        &mut self,
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
                } else if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let value_ty = func.dfg.value_ty(value);
                    shape::is_supported_aggregate_ty(module, value_ty)
                        && projection_of[*obj_load.object()].is_some()
                } else if let Some(bitcast) =
                    downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let from_ty = func.dfg.value_ty(*bitcast.from());
                    if !self.aggregate_bitcast_is_scalarizable(
                        module,
                        from_ty,
                        func.dfg.value_ty(value),
                    ) {
                        return false;
                    }
                    if shape::is_supported_aggregate_ty(module, from_ty) {
                        scalarizable[*bitcast.from()]
                    } else {
                        true
                    }
                } else {
                    false
                }
            }
        }
    }

    fn scalarizable_uses_are_closed(
        &mut self,
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

            if let Some(obj_store) =
                downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(user))
                && *obj_store.value() == value
            {
                if !shape::is_supported_aggregate_ty(module, func.dfg.value_ty(value)) {
                    return false;
                }
                if projection_of[*obj_store.object()].is_none() {
                    return false;
                }
                continue;
            }

            if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(user))
                && *bitcast.from() == value
            {
                let Some(res) = func.dfg.inst_result(user) else {
                    return false;
                };
                let res_ty = func.dfg.value_ty(res);
                if !self.aggregate_bitcast_is_scalarizable(module, func.dfg.value_ty(value), res_ty)
                {
                    return false;
                }
                if shape::is_supported_aggregate_ty(module, res_ty) && !scalarizable[res] {
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
                let shape = self
                    .aggregate_shape(module, agg_ty)
                    .unwrap_or_else(|| panic!("missing aggregate shape for scalarizable phi"));

                let mut leaf_phis: LeafValues = SmallVec::new();
                for leaf in shape.leaves {
                    let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(block));
                    let phi = control_flow::Phi::new_unchecked(func.inst_set(), Vec::new());
                    let phi_inst = cursor.prepend_inst_data(func, phi);
                    let phi_res = func.dfg.make_value(Value::Inst {
                        inst: phi_inst,
                        result_idx: 0,
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
        ssa: &mut SsaBuilder,
    ) {
        if let Some((projection_value, ty, result)) =
            downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
                .map(|mload| (*mload.addr(), *mload.ty(), func.dfg.inst_result(inst)))
                .or_else(|| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)).map(
                        |obj_load| {
                            let result = func.dfg.inst_result(inst);
                            let ty = result
                                .map(|result| func.dfg.value_ty(result))
                                .unwrap_or(Type::Unit);
                            (*obj_load.object(), ty, result)
                        },
                    )
                })
        {
            let Some(projection) = projection_of[projection_value] else {
                return;
            };
            let Some(promoted) = promoted_by_inst.get(&projection.alloca_inst) else {
                return;
            };
            let Some(result) = result else {
                return;
            };
            let leaf_range = projection.slice.first_leaf
                ..projection.slice.first_leaf + projection.slice.leaf_count;
            let underlying_leaves = &promoted.shape.leaves[leaf_range.clone()];
            if shape::is_supported_aggregate_ty(module, ty) {
                if !scalarizable[result] {
                    return;
                }
                let Some(view_leaf_tys) = self.projection_view_leaf_tys(module, ty) else {
                    return;
                };
                if view_leaf_tys.len() != underlying_leaves.len() {
                    return;
                }
                let mut leaves: LeafValues = SmallVec::new();
                for (i, (underlying_leaf, view_ty)) in
                    underlying_leaves.iter().zip(view_leaf_tys).enumerate()
                {
                    let var = promoted.leaf_vars[projection.slice.first_leaf + i];
                    let value = ssa.use_var(func, var, block);
                    leaves.push(bitcast_before_inst(
                        func,
                        inst,
                        value,
                        underlying_leaf.ty,
                        view_ty,
                    ));
                }
                scalarized_agg[result] = Some(leaves);
                return;
            }

            if projection.slice.leaf_count != 1 {
                return;
            }
            let underlying_leaf = &underlying_leaves[0];
            let var = promoted.leaf_vars[projection.slice.first_leaf];
            let val = ssa.use_var(func, var, block);
            let val = bitcast_before_inst(func, inst, val, underlying_leaf.ty, ty);
            func.dfg.change_to_alias(result, val);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        let Some((projection_value, value, ty)) =
            downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
                .map(|mstore| (*mstore.addr(), *mstore.value(), *mstore.ty()))
                .or_else(|| {
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)).map(
                        |obj_store| {
                            let value = *obj_store.value();
                            (*obj_store.object(), value, func.dfg.value_ty(value))
                        },
                    )
                })
        else {
            return;
        };
        let Some(projection) = projection_of[projection_value] else {
            return;
        };
        let Some(promoted) = promoted_by_inst.get(&projection.alloca_inst) else {
            return;
        };
        let leaf_range =
            projection.slice.first_leaf..projection.slice.first_leaf + projection.slice.leaf_count;
        let underlying_leaves = &promoted.shape.leaves[leaf_range.clone()];

        if shape::is_supported_aggregate_ty(module, ty) {
            let Some(payload_leaves) =
                self.scalarized_leaves_of_value(func, module, value, ty, scalarized_agg)
            else {
                return;
            };
            let Some(view_leaf_tys) = self.projection_view_leaf_tys(module, ty) else {
                return;
            };
            if payload_leaves.len() != projection.slice.leaf_count
                || view_leaf_tys.len() != underlying_leaves.len()
            {
                return;
            }
            for (i, ((val, view_ty), underlying_leaf)) in payload_leaves
                .into_iter()
                .zip(view_leaf_tys)
                .zip(underlying_leaves.iter())
                .enumerate()
            {
                let var = promoted.leaf_vars[projection.slice.first_leaf + i];
                let stored = bitcast_before_inst(func, inst, val, view_ty, underlying_leaf.ty);
                ssa.def_var(var, stored, block);
            }
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        if projection.slice.leaf_count != 1 {
            return;
        }
        let underlying_leaf = &underlying_leaves[0];
        let var = promoted.leaf_vars[projection.slice.first_leaf];
        let stored = bitcast_before_inst(func, inst, value, ty, underlying_leaf.ty);
        ssa.def_var(var, stored, block);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn rewrite_scalarizable_bitcast(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        inst: InstId,
        scalarizable: &SecondaryMap<ValueId, bool>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        let Some(bitcast) =
            downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)).cloned()
        else {
            return;
        };
        let Some(result) = func.dfg.inst_result(inst) else {
            return;
        };
        let from = *bitcast.from();
        let from_ty = func.dfg.value_ty(from);
        let result_ty = func.dfg.value_ty(result);
        let from_is_agg = shape::is_supported_aggregate_ty(module, from_ty);
        let result_is_agg = shape::is_supported_aggregate_ty(module, result_ty);
        if !from_is_agg && !result_is_agg {
            return;
        }

        if from_is_agg && result_is_agg {
            if !scalarizable[result] {
                return;
            }
            let Some((src_leaves, dst_leaves)) =
                self.compatible_aggregate_bitcast_runtime_leaves(module, from_ty, result_ty)
            else {
                return;
            };
            let Some(source_leaves) =
                self.scalarized_leaves_of_value(func, module, from, from_ty, scalarized_agg)
            else {
                return;
            };
            if source_leaves.len() != src_leaves.len() {
                return;
            }

            let mut mapped = LeafValues::new();
            for ((source, src_leaf), dst_leaf) in
                source_leaves.into_iter().zip(src_leaves).zip(dst_leaves)
            {
                let value = bitcast_before_inst(func, inst, source, src_leaf.ty, dst_leaf.ty);
                mapped.push(value);
            }
            scalarized_agg[result] = Some(mapped);
            return;
        }

        if result_is_agg {
            if !scalarizable[result] {
                return;
            }
            let Some(dst_leaf) = self.aggregate_single_runtime_word_leaf(module, result_ty) else {
                return;
            };
            let mut leaves = LeafValues::new();
            let value = bitcast_before_inst(func, inst, from, from_ty, dst_leaf.ty);
            leaves.push(value);
            scalarized_agg[result] = Some(leaves);
            return;
        }

        let Some(src_leaf) = self.aggregate_single_runtime_word_leaf(module, from_ty) else {
            return;
        };
        let Some(source_leaves) =
            self.scalarized_leaves_of_value(func, module, from, from_ty, scalarized_agg)
        else {
            return;
        };
        let [source] = source_leaves.as_slice() else {
            return;
        };
        let replacement = bitcast_before_inst(func, inst, *source, src_leaf.ty, result_ty);
        func.dfg.change_to_alias(result, replacement);
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
        }
    }

    fn simplify_scalar_phi_results(
        &mut self,
        func: &mut Function,
        scalar_phi_results: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        let values: Vec<_> = func.dfg.value_ids().collect();
        for value in values {
            let Some(mut leaf_phis) = scalar_phi_results[value].take() else {
                continue;
            };
            self.simplify_scalar_leaf_phis(func, &mut leaf_phis, scalar_phi_results);
            scalar_phi_results[value] = Some(leaf_phis);
        }
    }

    fn simplify_scalar_leaf_phis(
        &mut self,
        func: &mut Function,
        leaf_phis: &mut LeafValues,
        scalar_phi_results: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        let mut worklist: Vec<_> = leaf_phis.iter().copied().collect();
        let mut queued = FxHashSet::default();
        while let Some(leaf_phi) = worklist.pop() {
            let Some(phi_inst) = func.dfg.value_inst(leaf_phi) else {
                continue;
            };
            if !func.layout.is_inst_inserted(phi_inst) {
                continue;
            }
            let Some(replacement) = trivial_phi_replacement(func, phi_inst) else {
                continue;
            };
            let phi_users: Vec<_> = func
                .dfg
                .users(leaf_phi)
                .copied()
                .filter(|user| func.layout.is_inst_inserted(*user) && func.dfg.is_phi(*user))
                .collect();
            func.dfg.change_to_alias(leaf_phi, replacement);
            for current in leaf_phis.iter_mut() {
                if *current == leaf_phi {
                    *current = replacement;
                }
            }
            replace_scalar_phi_value(scalar_phi_results, leaf_phi, replacement);
            InstInserter::at_location(CursorLocation::At(phi_inst)).remove_inst(func);
            for user in phi_users {
                let Some(user_value) = func.dfg.inst_result(user) else {
                    continue;
                };
                if queued.insert(user_value) {
                    worklist.push(user_value);
                }
            }
            self.changed = true;
        }
    }

    fn cleanup_scalarized_artifacts(
        &mut self,
        func: &mut Function,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        promoted_by_inst: &FxHashMap<InstId, PromotedAlloca>,
    ) -> bool {
        let mut changed = false;
        loop {
            func.rebuild_users();
            let removed_mloads = self.cleanup_dead_aggregate_mloads_with_current_users(func);
            let removed_promoted_paths = self.cleanup_dead_promoted_paths_with_current_users(
                func,
                projection_of,
                promoted_by_inst,
            );
            let removed_pure = self.dead_pure_cleanup.run_with_current_users(func);
            if !removed_mloads && !removed_promoted_paths && !removed_pure {
                return changed;
            }
            changed = true;
        }
    }

    fn cleanup_dead_aggregate_mloads_with_current_users(&self, func: &mut Function) -> bool {
        let mut changed = false;
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                let Some((result, load_ty)) =
                    downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|mload| {
                            func.dfg
                                .inst_result(inst)
                                .map(|result| (result, *mload.ty()))
                        })
                        .or_else(|| {
                            downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                                .and_then(|_| {
                                    func.dfg
                                        .inst_result(inst)
                                        .map(|result| (result, func.dfg.value_ty(result)))
                                })
                        })
                else {
                    continue;
                };
                if !shape::is_supported_aggregate_ty(func.ctx(), load_ty) {
                    continue;
                }
                if func
                    .dfg
                    .users(result)
                    .copied()
                    .any(|user| func.layout.is_inst_inserted(user))
                {
                    continue;
                }

                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                changed = true;
            }
        }
        changed
    }

    fn cleanup_dead_promoted_paths_with_current_users(
        &self,
        func: &mut Function,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        promoted_by_inst: &FxHashMap<InstId, PromotedAlloca>,
    ) -> bool {
        if promoted_by_inst.is_empty() {
            return false;
        }
        let mut changed = false;

        loop {
            let mut removed_any = false;
            for value in func.dfg.value_ids().collect::<Vec<_>>() {
                let Some(projection) = projection_of[value] else {
                    continue;
                };
                if !promoted_by_inst.contains_key(&projection.alloca_inst) {
                    continue;
                }
                let Some(inst) = func.dfg.value_inst(value) else {
                    continue;
                };
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                let inst_data = func.dfg.inst(inst);
                if downcast::<&data::Alloca>(func.inst_set(), inst_data).is_none()
                    && downcast::<&data::Gep>(func.inst_set(), inst_data).is_none()
                    && downcast::<&data::ObjAlloc>(func.inst_set(), inst_data).is_none()
                    && downcast::<&data::ObjProj>(func.inst_set(), inst_data).is_none()
                    && downcast::<&data::ObjIndex>(func.inst_set(), inst_data).is_none()
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
                return changed;
            }
            changed = true;
            func.rebuild_users();
        }
    }

    fn aggregate_shape(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        ty: Type,
    ) -> Option<shape::AggregateShape> {
        self.layout_cache.shape(module, ty)
    }

    fn aggregate_single_runtime_word_leaf(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        ty: Type,
    ) -> Option<shape::AggregateLeaf> {
        self.layout_cache.single_runtime_word_leaf(module, ty)
    }

    fn compatible_aggregate_bitcast_runtime_leaves(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        from_ty: Type,
        to_ty: Type,
    ) -> Option<(shape::RuntimeLeaves, shape::RuntimeLeaves)> {
        self.layout_cache
            .compatible_bitcast_runtime_leaves(module, from_ty, to_ty)
    }

    fn projection_view_leaf_tys(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        ty: Type,
    ) -> Option<SmallVec<[Type; 4]>> {
        if shape::is_supported_aggregate_ty(module, ty) {
            return Some(
                self.aggregate_shape(module, ty)?
                    .leaves
                    .into_iter()
                    .map(|leaf| leaf.ty)
                    .collect(),
            );
        }
        Some(smallvec![ty])
    }

    fn bitcast_projection_slice(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        slice: shape::AggregateSlice,
        ptr_ty: Type,
    ) -> Option<shape::AggregateSlice> {
        let pointee_ty = module.with_ty_store(|s| s.deref(ptr_ty))?;
        self.projection_slice_can_view_as(module, slice, pointee_ty)
            .then_some(shape::AggregateSlice {
                ty: pointee_ty,
                ..slice
            })
    }

    fn projection_slice_can_view_as(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        slice: shape::AggregateSlice,
        view_ty: Type,
    ) -> bool {
        let Some(from_leaf_tys) = self.projection_view_leaf_tys(module, slice.ty) else {
            return false;
        };
        let Some(to_leaf_tys) = self.projection_view_leaf_tys(module, view_ty) else {
            return false;
        };

        from_leaf_tys.len() == slice.leaf_count
            && from_leaf_tys.len() == to_leaf_tys.len()
            && (view_ty == slice.ty
                || from_leaf_tys.len() == 1
                    && module.size_of_unchecked(from_leaf_tys[0])
                        == module.size_of_unchecked(to_leaf_tys[0])
                || shape::is_supported_aggregate_ty(module, slice.ty)
                    && shape::is_supported_aggregate_ty(module, view_ty)
                    && self
                        .compatible_aggregate_bitcast_runtime_leaves(module, slice.ty, view_ty)
                        .is_some())
    }

    fn aggregate_bitcast_is_scalarizable(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        from_ty: Type,
        to_ty: Type,
    ) -> bool {
        if module.size_of_unchecked(from_ty) != module.size_of_unchecked(to_ty) {
            return false;
        }
        let from_is_agg = shape::is_supported_aggregate_ty(module, from_ty);
        let to_is_agg = shape::is_supported_aggregate_ty(module, to_ty);
        if from_is_agg && to_is_agg {
            return self
                .compatible_aggregate_bitcast_runtime_leaves(module, from_ty, to_ty)
                .is_some();
        }
        if to_is_agg {
            return self
                .aggregate_single_runtime_word_leaf(module, to_ty)
                .is_some();
        }
        if from_is_agg {
            return self
                .aggregate_single_runtime_word_leaf(module, from_ty)
                .is_some();
        }
        false
    }

    fn scalarized_leaves_of_value(
        &mut self,
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
            let agg_shape = self.aggregate_shape(module, ty)?;
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

fn trivial_phi_replacement(func: &mut Function, phi_inst: InstId) -> Option<ValueId> {
    let phi_value = func.dfg.inst_result(phi_inst)?;
    let ty = func.dfg.value_ty(phi_value);
    let phi = func.dfg.cast_phi(phi_inst)?;

    let replacement = match phi.args().first() {
        None => func.dfg.make_undef_value(ty),
        Some(&(first, _)) if phi.args().iter().all(|(value, _)| *value == first) => {
            if first == phi_value {
                func.dfg.make_undef_value(ty)
            } else {
                first
            }
        }
        Some(_) => {
            let mut non_self = None;
            for &(value, _) in phi.args() {
                if value == phi_value {
                    continue;
                }

                match non_self {
                    Some(existing) if existing != value => return None,
                    Some(_) => {}
                    None => non_self = Some(value),
                }
            }

            non_self.unwrap_or_else(|| func.dfg.make_undef_value(ty))
        }
    };

    Some(replacement)
}

fn replace_scalar_phi_value(
    scalar_phi_results: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    from: ValueId,
    to: ValueId,
) {
    for value in scalar_phi_results.keys() {
        let Some(leaf_phis) = scalar_phi_results[value].as_mut() else {
            continue;
        };
        for leaf_phi in leaf_phis {
            if *leaf_phi == from {
                *leaf_phi = to;
            }
        }
    }
}

fn is_dead_inst_tree(
    func: &Function,
    inst: InstId,
    memo: &mut FxHashMap<InstId, bool>,
    visiting: &mut FxHashSet<InstId>,
) -> bool {
    if let Some(&cached) = memo.get(&inst) {
        return cached;
    }
    if !visiting.insert(inst)
        || func.dfg.side_effect(inst).has_effect()
        || func.dfg.is_terminator(inst)
    {
        memo.insert(inst, false);
        return false;
    }

    let dead = func.dfg.inst_result(inst).is_some_and(|result| {
        func.dfg
            .users(result)
            .copied()
            .filter(|user| func.layout.is_inst_inserted(*user))
            .all(|user| is_dead_inst_tree(func, user, memo, visiting))
    });
    visiting.remove(&inst);
    memo.insert(inst, dead);
    dead
}

fn first_non_phi_inst(func: &Function, block: BlockId) -> Option<InstId> {
    func.layout
        .iter_inst(block)
        .find(|inst| !func.dfg.is_phi(*inst))
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{InstDowncast, Module, inst::cast, module::FuncRef};
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

    fn assert_no_promoted_aggregate_artifacts(
        func: &Function,
        ctx: &sonatina_ir::module::ModuleCtx,
    ) {
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                assert!(
                    downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                    "promoted alloca should be removed"
                );
                assert!(
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                    "promoted object root should be removed"
                );
                assert!(
                    downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                    "promoted object projection should be removed"
                );
                assert!(
                    downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                    "promoted object index should be removed"
                );
                if let Some(mload) =
                    <&data::Mload as InstDowncast>::downcast(func.inst_set(), func.dfg.inst(inst))
                {
                    assert!(
                        !shape::is_supported_aggregate_ty(ctx, *mload.ty()),
                        "aggregate mload should be gone after scalarization"
                    );
                }
                if let Some(_obj_load) =
                    <&data::ObjLoad as InstDowncast>::downcast(func.inst_set(), func.dfg.inst(inst))
                    && let Some(result) = func.dfg.inst_result(inst)
                {
                    assert!(
                        !shape::is_supported_aggregate_ty(ctx, func.dfg.value_ty(result)),
                        "aggregate obj.load should be gone after scalarization"
                    );
                }
                if let Some(mstore) =
                    <&data::Mstore as InstDowncast>::downcast(func.inst_set(), func.dfg.inst(inst))
                {
                    assert!(
                        !shape::is_supported_aggregate_ty(ctx, *mstore.ty()),
                        "aggregate mstore should be gone after scalarization"
                    );
                }
                if let Some(obj_store) = <&data::ObjStore as InstDowncast>::downcast(
                    func.inst_set(),
                    func.dfg.inst(inst),
                ) {
                    assert!(
                        !shape::is_supported_aggregate_ty(
                            ctx,
                            func.dfg.value_ty(*obj_store.value())
                        ),
                        "aggregate obj.store should be gone after scalarization"
                    );
                }
            }
        }
    }

    #[test]
    fn scalarize_does_not_leave_removed_leaf_phi_uses() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i1, v1.i1, v2.i256) -> i256 {
    block0:
        v3.*@slice = alloca @slice;
        br v0 block1 block2;

    block1:
        v4.@slice = insert_value undef.@slice 0.i8 v2;
        v5.@slice = insert_value v4 1.i8 11.i256;
        jump block3;

    block2:
        v6.@slice = insert_value undef.@slice 0.i8 v2;
        v7.@slice = insert_value v6 1.i8 22.i256;
        jump block3;

    block3:
        v8.@slice = phi (v5 block1) (v7 block2);
        mstore v3 v8 @slice;
        br v1 block4 block5;

    block4:
        v9.@slice = insert_value undef.@slice 0.i8 99.i256;
        v10.@slice = insert_value v9 1.i8 33.i256;
        mstore v3 v10 @slice;
        jump block5;

    block5:
        v11.@slice = mload v3 @slice;
        v12.i256 = extract_value v11 0.i8;
        return v12;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    func.dfg.inst(inst).for_each_value(&mut |value| {
                        if let Some(def_inst) = func.dfg.value_inst(value) {
                            assert!(
                                func.layout.is_inst_inserted(def_inst),
                                "inst {} uses value v{} from removed inst {}",
                                inst.as_u32(),
                                value.as_u32(),
                                def_inst.as_u32()
                            );
                        }
                    });
                }
            }
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    #[should_panic(
        expected = "AggregateScalarize requires CfgCleanup to remove unreachable blocks first"
    )]
    fn scalarize_requires_cfg_cleanup_for_unreachable_blocks() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f() -> i256 {
    block0:
        v0.*@slice = alloca @slice;
        return 0.i256;

    block1:
        v1.@slice = mload v0 @slice;
        v2.i256 = extract_value v1 0.i8;
        return v2;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });
    }

    #[test]
    fn scalarize_cleans_up_dead_promoted_pointer_trees() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f() -> i256 {
    block0:
        v0.*@slice = alloca @slice;
        v1.*i256 = gep v0 0.i8 0.i8;
        v2.*i256 = bitcast v1 *i256;
        return 0.i256;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    assert!(
                        downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                        "dead promoted alloca should be removed"
                    );
                    assert!(
                        downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                        "dead promoted gep should be removed"
                    );
                    assert!(
                        downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                        "dead promoted bitcast should be removed"
                    );
                }
            }
        });
    }

    #[test]
    fn scalarize_promotes_non_entry_alloca() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i1, v1.i256, v2.i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        v3.*@slice = alloca @slice;
        v4.*i256 = gep v3 0.i8 0.i8;
        v5.*i256 = gep v3 0.i8 1.i8;
        mstore v4 v1 i256;
        mstore v5 v2 i256;
        v6.i256 = mload v4 i256;
        v7.i256 = mload v5 i256;
        v8.i256 = add v6 v7;
        return v8;

    block2:
        return 0.i256;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_promotes_obj_alloc_root() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        v2.objref<@slice> = obj.alloc @slice;
        v3.@slice = insert_value undef.@slice 0.i8 v0;
        v4.@slice = insert_value v3 1.i8 v1;
        obj.store v2 v4;
        v5.@slice = obj.load v2;
        v6.i256 = extract_value v5 1.i8;
        return v6;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_promotes_obj_proj_and_index_paths() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, [i256; 2] };

func private %f(v0.i256, v1.i256, v2.i256) -> i256 {
    block0:
        v3.objref<@pair> = obj.alloc @pair;
        v4.objref<i256> = obj.proj v3 0.i8;
        v5.objref<[i256; 2]> = obj.proj v3 1.i8;
        v6.objref<i256> = obj.index v5 0.i8;
        v7.objref<i256> = obj.index v5 1.i8;
        obj.store v4 v0;
        obj.store v6 v1;
        obj.store v7 v2;
        v8.i256 = obj.load v4;
        v9.i256 = obj.load v6;
        v10.i256 = obj.load v7;
        v11.i256 = add v8 v9;
        v12.i256 = add v11 v10;
        return v12;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_splits_block_to_seed_non_entry_alloca_at_its_location() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i1, v1.i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        v2.i256 = add v1 1.i256;
        v3.*@one = alloca @one;
        mstore v3 v2 i256;
        v4.i256 = mload v3 i256;
        return v4;

    block2:
        return 0.i256;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_eq!(
                func.layout.iter_block().count(),
                4,
                "non-entry alloca with leading instructions should split its block"
            );
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_splits_each_promoted_alloca_to_its_own_seed_point() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = add v0 1.i256;
        v3.*@one = alloca @one;
        mstore v3 v2 i256;
        v4.i256 = mload v3 i256;
        v5.*@one = alloca @one;
        mstore v5 v1 i256;
        v6.i256 = mload v5 i256;
        v7.i256 = add v4 v6;
        return v7;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_eq!(
                func.layout.iter_block().count(),
                3,
                "each promoted alloca in the original block should get its own seed point"
            );
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_non_entry_alloca_merges_store_and_undef_paths() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i1) -> i256 {
    block0:
        jump block1;

    block1:
        v1.*@one = alloca @one;
        v2.*i256 = gep v1 0.i8 0.i8;
        br v0 block2 block3;

    block2:
        mstore v2 7.i256 i256;
        jump block4;

    block3:
        jump block4;

    block4:
        v3.i256 = mload v2 i256;
        return v3;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);

            let mut found = false;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    let Some(phi) = <&control_flow::Phi as InstDowncast>::downcast(
                        func.inst_set(),
                        func.dfg.inst(inst),
                    ) else {
                        continue;
                    };
                    if func
                        .dfg
                        .inst_result(inst)
                        .is_none_or(|result| func.dfg.value_ty(result) != Type::I256)
                    {
                        continue;
                    }

                    let has_undef = phi
                        .args()
                        .iter()
                        .any(|(value, _)| matches!(func.dfg.value(*value), Value::Undef { .. }));
                    let has_non_undef = phi
                        .args()
                        .iter()
                        .any(|(value, _)| !matches!(func.dfg.value(*value), Value::Undef { .. }));
                    if has_undef && has_non_undef {
                        found = true;
                    }
                }
            }

            assert!(found, "expected scalar phi merging stored and undef paths");
        });
    }

    #[test]
    fn scalarize_loop_local_alloca_reseeds_at_its_location() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f() -> i256 {
    block0:
        jump block1;

    block1:
        v0.i1 = phi (1.i1 block0) (0.i1 block4);
        v1.i256 = add 5.i256 6.i256;
        v2.*@one = alloca @one;
        v3.*i256 = gep v2 0.i8 0.i8;
        br v0 block2 block3;

    block2:
        mstore v3 9.i256 i256;
        jump block3;

    block3:
        v4.i256 = mload v3 i256;
        br v0 block4 block5;

    block4:
        jump block1;

    block5:
        return v4;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_eq!(
                func.layout.iter_block().count(),
                7,
                "loop-local alloca with leading instructions should split its seed point"
            );
            assert_no_promoted_aggregate_artifacts(func, &ctx);

            let mut found = false;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    let Some(phi) = <&control_flow::Phi as InstDowncast>::downcast(
                        func.inst_set(),
                        func.dfg.inst(inst),
                    ) else {
                        continue;
                    };
                    if func
                        .dfg
                        .inst_result(inst)
                        .is_none_or(|result| func.dfg.value_ty(result) != Type::I256)
                    {
                        continue;
                    }

                    let has_undef = phi
                        .args()
                        .iter()
                        .any(|(value, _)| matches!(func.dfg.value(*value), Value::Undef { .. }));
                    let has_non_undef = phi
                        .args()
                        .iter()
                        .any(|(value, _)| !matches!(func.dfg.value(*value), Value::Undef { .. }));
                    if has_undef && has_non_undef {
                        found = true;
                    }
                }
            }

            assert!(
                found,
                "loop-local promoted alloca should re-seed to undef at its alloca point"
            );
        });
    }

    #[test]
    fn scalarize_simplifies_transitive_scalar_phi_users_without_stale_entries() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i1, v1.i1, v2.i256, v3.i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v4.@slice = insert_value undef.@slice 0.i8 v2;
        v5.@slice = insert_value v4 1.i8 v3;
        v6.@slice = phi (v5 block1) (v5 block2);
        br v1 block4 block5;

    block4:
        jump block6;

    block5:
        jump block6;

    block6:
        v7.@slice = phi (v6 block4) (v6 block5);
        v8.i256 = extract_value v7 0.i8;
        return v8;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    func.dfg.inst(inst).for_each_value(&mut |value| {
                        if let Some(def_inst) = func.dfg.value_inst(value) {
                            assert!(
                                func.layout.is_inst_inserted(def_inst),
                                "inst {} uses value v{} from removed inst {}",
                                inst.as_u32(),
                                value.as_u32(),
                                def_inst.as_u32()
                            );
                        }
                    });
                }
            }
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_deduplicates_duplicate_successor_edges() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i1) -> i256 {
    block0:
        v1.*@slice = alloca @slice;
        br v0 block1 block1;

    block1:
        v2.@slice = mload v1 @slice;
        v3.i256 = extract_value v2 0.i8;
        return v3;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(phi) = <&control_flow::Phi as InstDowncast>::downcast(
                        func.inst_set(),
                        func.dfg.inst(inst),
                    ) {
                        let mut preds = FxHashSet::default();
                        for &(_, pred) in phi.args() {
                            assert!(preds.insert(pred), "phi should not retain duplicate preds");
                        }
                    }
                }
            }
        });
    }
}
