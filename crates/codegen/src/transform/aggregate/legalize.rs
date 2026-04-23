use std::mem;

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, Inst, InstId, Type, Value, ValueId,
    cfg::ControlFlowGraph,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, control_flow, data, downcast},
    module::ModuleCtx,
    types::CompoundType,
};

use crate::{
    cfg_edit::CleanupMode,
    critical_edge::CriticalEdgeSplitter,
    optim::{adce::AdceSolver, cfg_cleanup::CfgCleanup},
};

use super::{cleanup::DeadPureInstCleanup, shape};

#[derive(Clone, Copy)]
struct AggregateProjectionView {
    root_value: ValueId,
    root_ty: Type,
    agg_ty: Type,
    first_root_runtime_leaf: usize,
    runtime_leaf_count: usize,
}

#[derive(Clone, Copy)]
struct ScalarUse {
    inst: InstId,
    result: ValueId,
    root_runtime_leaf: usize,
    result_ty: Type,
}

#[derive(Default)]
struct MloadProjectionPlan {
    scalar_uses: SmallVec<[ScalarUse; 4]>,
    transparent_insts: SmallVec<[InstId; 8]>,
    demanded_root_runtime_leaves: SmallVec<[bool; 8]>,
}

impl MloadProjectionPlan {
    fn new(root_runtime_leaf_count: usize) -> Self {
        Self {
            demanded_root_runtime_leaves: smallvec![false; root_runtime_leaf_count],
            ..Self::default()
        }
    }

    fn add_scalar_use(
        &mut self,
        inst: InstId,
        result: ValueId,
        root_runtime_leaf: usize,
        result_ty: Type,
    ) {
        self.scalar_uses.push(ScalarUse {
            inst,
            result,
            root_runtime_leaf,
            result_ty,
        });
        self.mark_root_runtime_leaf(root_runtime_leaf);
    }

    fn mark_root_runtime_leaf(&mut self, root_runtime_leaf: usize) {
        let Some(demanded) = self.demanded_root_runtime_leaves.get_mut(root_runtime_leaf) else {
            panic!("aggregate projection root runtime leaf out of bounds");
        };
        *demanded = true;
    }

    fn mark_view_runtime_leaves(&mut self, view: &AggregateProjectionView) {
        let end = view
            .first_root_runtime_leaf
            .checked_add(view.runtime_leaf_count)
            .unwrap_or_else(|| panic!("aggregate projection runtime leaf range overflow"));
        let Some(demanded) = self
            .demanded_root_runtime_leaves
            .get_mut(view.first_root_runtime_leaf..end)
        else {
            panic!("aggregate projection runtime leaf range out of bounds");
        };
        for leaf in demanded {
            *leaf = true;
        }
    }
}

struct SnapshotRoot {
    root_value: ValueId,
    src_ptr: ValueId,
    slot_ptr: Option<ValueId>,
    runtime_leaves: shape::RuntimeLeaves,
    raw_leaf_cache: Vec<Option<ValueId>>,
    cast_leaf_cache: FxHashMap<(usize, Type), ValueId>,
}

impl SnapshotRoot {
    fn new(root_value: ValueId, src_ptr: ValueId, runtime_leaves: shape::RuntimeLeaves) -> Self {
        let raw_leaf_cache = vec![None; runtime_leaves.len()];
        Self {
            root_value,
            src_ptr,
            slot_ptr: None,
            runtime_leaves,
            raw_leaf_cache,
            cast_leaf_cache: FxHashMap::default(),
        }
    }

    fn leaf_as(
        &mut self,
        legalize: &mut AggregateLowerToMemoryLegalize,
        func: &mut Function,
        builder: &mut BeforeCursor,
        root_runtime_leaf: usize,
        result_ty: Type,
    ) -> ValueId {
        let Some(leaf) = self.runtime_leaves.get(root_runtime_leaf) else {
            panic!("aggregate projection root runtime leaf out of bounds");
        };

        let raw = match self.raw_leaf_cache[root_runtime_leaf] {
            Some(value) => value,
            None => {
                let value = legalize.emit_load_scalar_from_path(
                    func,
                    builder,
                    self.src_ptr,
                    &leaf.path,
                    leaf.ty,
                );
                self.raw_leaf_cache[root_runtime_leaf] = Some(value);
                legalize
                    .snapshot_leaf_values
                    .insert((self.root_value, root_runtime_leaf), value);
                value
            }
        };
        if func.dfg.value_ty(raw) == result_ty {
            return raw;
        }
        if let Some(&value) = self.cast_leaf_cache.get(&(root_runtime_leaf, result_ty)) {
            return value;
        }

        let casted = builder.insert_with_result(
            func,
            cast::Bitcast::new_unchecked(func.inst_set(), raw, result_ty),
            result_ty,
        );
        self.cast_leaf_cache
            .insert((root_runtime_leaf, result_ty), casted);
        casted
    }

    fn ensure_slot(
        &mut self,
        legalize: &mut AggregateLowerToMemoryLegalize,
        func: &mut Function,
        builder: &mut BeforeCursor,
        dst_ptr: ValueId,
        demanded_root_runtime_leaves: &[bool],
    ) {
        if self.slot_ptr.is_some() {
            return;
        }
        if demanded_root_runtime_leaves.len() != self.runtime_leaves.len() {
            panic!("aggregate projection demanded leaf mask length mismatch");
        }

        for (idx, leaf) in self.runtime_leaves.iter().enumerate() {
            if !demanded_root_runtime_leaves[idx] {
                continue;
            }

            let raw = match self.raw_leaf_cache[idx] {
                Some(value) => value,
                None => {
                    let value = legalize.emit_load_scalar_from_path(
                        func,
                        builder,
                        self.src_ptr,
                        &leaf.path,
                        leaf.ty,
                    );
                    self.raw_leaf_cache[idx] = Some(value);
                    legalize
                        .snapshot_leaf_values
                        .insert((self.root_value, idx), value);
                    value
                }
            };
            legalize.emit_store_scalar_to_path(func, builder, dst_ptr, &leaf.path, raw, leaf.ty);
        }

        self.slot_ptr = Some(dst_ptr);
    }
}

#[derive(Default)]
pub struct AggregateLowerToMemoryLegalize {
    changed: bool,
    materialized_addr: SecondaryMap<ValueId, Option<ValueId>>,
    materialized_slots: Vec<ValueId>,
    projection_views: SecondaryMap<ValueId, Option<AggregateProjectionView>>,
    snapshot_leaf_values: FxHashMap<(ValueId, usize), ValueId>,
    layout_cache: shape::AggregateLayoutCache,
    slot_tree_insts: Vec<InstId>,
    slot_tree_queue: Vec<ValueId>,
    slot_tree_seen_insts: FxHashSet<InstId>,
    slot_tree_seen_values: FxHashSet<ValueId>,
    dead_pure_cleanup: DeadPureInstCleanup,
}

#[derive(Default)]
struct AggregateLegalizeScan {
    has_work: bool,
    has_agg_phi: bool,
    candidates: SecondaryMap<BlockId, SmallVec<[InstId; 8]>>,
}

impl AggregateLowerToMemoryLegalize {
    pub fn run(&mut self, func: &mut Function, module: &ModuleCtx) -> bool {
        self.changed = false;
        self.materialized_addr.clear();
        self.materialized_slots.clear();
        self.projection_views.clear();
        self.snapshot_leaf_values.clear();
        self.layout_cache.clear();
        self.slot_tree_insts.clear();
        self.slot_tree_queue.clear();
        self.slot_tree_seen_insts.clear();
        self.slot_tree_seen_values.clear();
        if func.layout.entry_block().is_none() {
            return false;
        }

        let scan = scan_aggregate_legalize_needs(func, module);
        if !scan.has_work {
            return false;
        }

        // Legalization uses `dfg.change_to_alias`, which requires up-to-date user sets.
        func.rebuild_users();

        let (blocks, split_edges) = self.prepare_legalize_block_order(func, scan.has_agg_phi);
        for block in blocks {
            for &inst in &scan.candidates[block] {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                self.changed |= self.rewrite_inst(func, module, inst);
            }
        }

        if self.changed {
            self.changed |= self.cleanup_legalized_artifacts(func, split_edges);
        }
        assert_aggregate_legalized(func, module);
        self.changed
    }

    fn prepare_legalize_block_order(
        &mut self,
        func: &mut Function,
        has_agg_phi: bool,
    ) -> (SmallVec<[BlockId; 16]>, bool) {
        let entry = func
            .layout
            .entry_block()
            .expect("function must have entry block");
        if func.layout.next_block_of(entry).is_none() {
            return (smallvec![entry], false);
        }

        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        if !has_agg_phi {
            return (aggregate_legalize_block_order(func, &cfg), false);
        }

        let block_count = func.layout.iter_block().count();
        CriticalEdgeSplitter::new().run(func, &mut cfg);
        let changed = func.layout.iter_block().count() != block_count;
        self.changed |= changed;
        (aggregate_legalize_block_order(func, &cfg), changed)
    }

    fn cleanup_legalized_artifacts(&mut self, func: &mut Function, split_edges: bool) -> bool {
        // User sets stay current through legalization and CFG cleanup, so the cleanup
        // phases can share the single rebuild done before rewriting starts.
        let mut changed = false;
        let mut pending_cfg_cleanup = split_edges;

        loop {
            let removed_mloads = self.remove_dead_aggregate_mloads(func);
            let removed_slots = self.remove_dead_materialized_slots(func);
            let removed_pure = self.dead_pure_cleanup.run_with_current_users(func);
            let removed_dead = AdceSolver::new().run(func);
            let cleaned_cfg = pending_cfg_cleanup && CfgCleanup::new(CleanupMode::Strict).run(func);
            pending_cfg_cleanup = false;

            let progress =
                removed_mloads || removed_slots || removed_pure || removed_dead || cleaned_cfg;
            changed |= progress;
            if !progress {
                return changed;
            }
        }
    }

    fn remove_dead_aggregate_mloads(&self, func: &mut Function) -> bool {
        let mut changed = false;
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                let Some(mload) = downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
                else {
                    continue;
                };
                if !shape::is_supported_aggregate_ty(func.ctx(), *mload.ty()) {
                    continue;
                }
                let Some(result) = func.dfg.inst_result(inst) else {
                    continue;
                };
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

    fn create_temp_alloca(&mut self, func: &mut Function, ty: Type) -> ValueId {
        let entry = func
            .layout
            .entry_block()
            .expect("function must have entry block");
        let ptr_ty = ty.to_ptr(func.ctx());
        let alloca = data::Alloca::new_unchecked(func.inst_set(), ty);
        let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(entry));
        let inst = cursor.prepend_inst_data(func, alloca);
        let ptr = func.dfg.make_value(Value::Inst {
            inst,
            result_idx: 0,
            ty: ptr_ty,
        });
        cursor.attach_result(func, inst, ptr);
        ptr
    }

    fn alias_and_remove(
        &self,
        func: &mut Function,
        inst: InstId,
        result: ValueId,
        replacement: ValueId,
    ) {
        func.dfg.change_to_alias(result, replacement);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn remove_if_results_dead(&self, func: &mut Function, inst: InstId) -> bool {
        if func.dfg.inst_results(inst).iter().copied().any(|result| {
            func.dfg
                .users(result)
                .copied()
                .any(|user| func.layout.is_inst_inserted(user))
        }) {
            return false;
        }

        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }

    fn single_word_leaf(
        &mut self,
        module: &ModuleCtx,
        agg_ty: Type,
        ctx: &str,
    ) -> shape::AggregateLeaf {
        let runtime_leaves = self.runtime_leaves_or_panic(module, agg_ty);
        let [leaf] = runtime_leaves.as_slice() else {
            panic!(
                "{ctx} bitcast requires single-leaf aggregate (got {})",
                runtime_leaves.len()
            );
        };
        if leaf.size_bytes != 32 {
            panic!(
                "{ctx} bitcast requires 32-byte leaf (got {})",
                leaf.size_bytes
            );
        }
        leaf.clone()
    }

    fn rewrite_inst(&mut self, func: &mut Function, module: &ModuleCtx, inst: InstId) -> bool {
        if downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            return self.rewrite_bitcast(func, module, inst);
        }
        if downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.rewrite_insert_value(func, module, inst);
            return true;
        }
        if downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.rewrite_extract_value(func, module, inst);
            return true;
        }
        if downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_some()
            && func
                .dfg
                .inst_result(inst)
                .is_some_and(|v| shape::is_supported_aggregate_ty(module, func.dfg.value_ty(v)))
        {
            self.rewrite_aggregate_phi(func, module, inst);
            return true;
        }
        if let Some(mload) = downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
            && shape::is_supported_aggregate_ty(module, *mload.ty())
        {
            self.rewrite_aggregate_mload(func, module, inst);
            return true;
        }
        if let Some(mstore) = downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
            && shape::is_supported_aggregate_ty(module, *mstore.ty())
        {
            self.rewrite_aggregate_mstore(func, module, inst);
            return true;
        }
        false
    }

    fn rewrite_bitcast(&mut self, func: &mut Function, module: &ModuleCtx, inst: InstId) -> bool {
        let bitcast = *downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst))
            .expect("expected bitcast");
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let from = *bitcast.from();
        let from_ty = func.dfg.value_ty(from);
        let to_ty = func.dfg.value_ty(result);
        let from_is_agg = shape::is_supported_aggregate_ty(module, from_ty);
        let to_is_agg = shape::is_supported_aggregate_ty(module, to_ty);
        if !from_is_agg && !to_is_agg {
            return false;
        }

        let Some(from_size) = shape::runtime_size_bytes(module, from_ty) else {
            return false;
        };
        let Some(to_size) = shape::runtime_size_bytes(module, to_ty) else {
            return false;
        };
        if from_size != to_size {
            panic!(
                "bitcast size mismatch in legalizer: {from_ty:?} ({from_size}) -> {to_ty:?} ({to_size})"
            );
        }

        // Aggregate -> aggregate: copy between layout-compatible leaf views.
        if from_is_agg && to_is_agg {
            if is_explicit_undef(func, from) {
                let undef = func.dfg.make_undef_value(to_ty);
                self.alias_and_remove(func, inst, result, undef);
                return true;
            }

            if let Some(view) = self.projection_views[from]
                && let Some(bitcast_view) =
                    self.aggregate_projection_view_for_bitcast(module, &view, to_ty)
            {
                self.projection_views[result] = Some(bitcast_view);
                if self.materialized_addr[result].is_some()
                    || self.value_requires_materialized_slot(func, result)
                {
                    let dst_ptr = self.materialized_ptr(func, result, module);
                    let mut builder = BeforeCursor::new_before_inst(func, inst);
                    self.emit_projection_view_to_ptr_from_snapshot(
                        func,
                        &mut builder,
                        module,
                        &bitcast_view,
                        dst_ptr,
                        to_ty,
                    );
                }
                self.remove_if_results_dead(func, inst);
                return true;
            }

            let mut builder = BeforeCursor::new_before_inst(func, inst);
            let src_ptr = self.materialized_ptr(func, from, module);
            let dst_ptr = self.materialized_ptr(func, result, module);
            let (src_leaves, dst_leaves) =
                self.aggregate_bitcast_leaf_layout(module, from_ty, to_ty);
            self.emit_copy_leaf_slices_ptr_to_ptr(
                func,
                &mut builder,
                src_ptr,
                &src_leaves,
                dst_ptr,
                &dst_leaves,
            );
            self.remove_if_results_dead(func, inst);
            return true;
        }

        // Scalar -> aggregate: only legal for single-word aggregates on EVM.
        if to_is_agg {
            let leaf = self.single_word_leaf(module, to_ty, "scalar-to-aggregate");

            let dst_ptr = self.materialized_ptr(func, result, module);

            let mut builder = BeforeCursor::new_before_inst(func, inst);
            let payload = if leaf.ty == from_ty {
                from
            } else {
                builder.insert_with_result(
                    func,
                    cast::Bitcast::new_unchecked(func.inst_set(), from, leaf.ty),
                    leaf.ty,
                )
            };
            self.emit_store_scalar_to_path(
                func,
                &mut builder,
                dst_ptr,
                &leaf.path,
                payload,
                leaf.ty,
            );
            self.remove_if_results_dead(func, inst);
            return true;
        }

        // Aggregate -> scalar: only legal for single-word aggregates on EVM.
        let leaf = self.single_word_leaf(module, from_ty, "aggregate-to-scalar");
        if is_explicit_undef(func, from) {
            let undef = func.dfg.make_undef_value(to_ty);
            self.alias_and_remove(func, inst, result, undef);
            return true;
        }

        let replacement = if let Some(view) = self.projection_views[from] {
            if view.runtime_leaf_count != 1 {
                panic!("aggregate-to-scalar bitcast requires single runtime leaf");
            }
            let raw =
                self.snapshot_leaf_value_or_panic(view.root_value, view.first_root_runtime_leaf);
            if func.dfg.value_ty(raw) == to_ty {
                raw
            } else {
                let mut builder = BeforeCursor::new_before_inst(func, inst);
                builder.insert_with_result(
                    func,
                    cast::Bitcast::new_unchecked(func.inst_set(), raw, to_ty),
                    to_ty,
                )
            }
        } else {
            let mut builder = BeforeCursor::new_before_inst(func, inst);
            let src_ptr = self.materialized_ptr(func, from, module);
            let loaded =
                self.emit_load_scalar_from_path(func, &mut builder, src_ptr, &leaf.path, leaf.ty);
            if leaf.ty == to_ty {
                loaded
            } else {
                builder.insert_with_result(
                    func,
                    cast::Bitcast::new_unchecked(func.inst_set(), loaded, to_ty),
                    to_ty,
                )
            }
        };
        self.alias_and_remove(func, inst, result, replacement);
        true
    }

    fn rewrite_insert_value(&mut self, func: &mut Function, module: &ModuleCtx, inst: InstId) {
        let insert = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst))
            .expect("expected insert_value")
            .clone();
        let result = func
            .dfg
            .inst_result(inst)
            .expect("insert_value must have result");
        let result_ty = func.dfg.value_ty(result);
        if !shape::is_supported_aggregate_ty(module, result_ty) {
            return;
        }
        let dst_ptr = self.materialized_ptr(func, result, module);

        let mut builder = BeforeCursor::new_before_inst(func, inst);
        self.emit_copy_aggregate_value_to_ptr(
            func,
            module,
            &mut builder,
            *insert.dest(),
            dst_ptr,
            result_ty,
        );

        let idx_value = *insert.idx();
        let idx_const = shape::const_u32(&func.dfg, idx_value);
        if idx_const.is_none() {
            self.rewrite_insert_value_dynamic_array_index(
                func,
                module,
                inst,
                &mut builder,
                dst_ptr,
                &insert,
            );
            return;
        }

        let idx = idx_const.expect("checked above");
        let slice = shape::aggregate_slice_for_index(module, result_ty, idx)
            .unwrap_or_else(|| panic!("insert_value index out of bounds"));
        if shape::is_supported_aggregate_ty(module, slice.ty) {
            self.emit_copy_subaggregate_value_to_slice(
                func,
                module,
                &mut builder,
                *insert.value(),
                SubaggregateSliceDst {
                    ptr: dst_ptr,
                    root_ty: result_ty,
                    slice,
                },
            );
        } else {
            let result_shape = self.shape_or_panic(module, result_ty);
            let leaf = &result_shape.leaves[slice.first_leaf];
            self.emit_store_scalar_to_path(
                func,
                &mut builder,
                dst_ptr,
                &leaf.path,
                *insert.value(),
                leaf.ty,
            );
        }

        self.remove_if_results_dead(func, inst);
    }

    fn rewrite_insert_value_dynamic_array_index(
        &mut self,
        func: &mut Function,
        module: &ModuleCtx,
        inst: InstId,
        builder: &mut BeforeCursor,
        dst_ptr: ValueId,
        insert: &data::InsertValue,
    ) {
        let dst_ty = func
            .dfg
            .inst_result(inst)
            .map(|v| func.dfg.value_ty(v))
            .expect("insert_value must have result");
        let elem = self.array_elem_ty_or_panic(module, dst_ty, "insert_value");
        let elem_ptr = self.emit_gep_array_element_ptr(func, builder, dst_ptr, *insert.idx(), elem);
        if shape::is_supported_aggregate_ty(module, elem) {
            self.emit_copy_aggregate_value_to_ptr(
                func,
                module,
                builder,
                *insert.value(),
                elem_ptr,
                elem,
            );
        } else {
            self.emit_store_scalar_to_path(func, builder, elem_ptr, &[], *insert.value(), elem);
        }
        self.remove_if_results_dead(func, inst);
    }

    fn rewrite_extract_value(&mut self, func: &mut Function, module: &ModuleCtx, inst: InstId) {
        let extract = downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst))
            .expect("expected extract_value")
            .clone();
        let result = func
            .dfg
            .inst_result(inst)
            .expect("extract_value must have result");
        let result_ty = func.dfg.value_ty(result);
        let agg_ty = func.dfg.value_ty(*extract.dest());
        let idx_value = *extract.idx();
        let idx_const = shape::const_u32(&func.dfg, idx_value);
        if idx_const.is_none() {
            self.rewrite_extract_value_dynamic_array_index(func, module, inst, result, &extract);
            return;
        }

        let idx = idx_const.expect("checked above");
        let slice = shape::aggregate_slice_for_index(module, agg_ty, idx)
            .unwrap_or_else(|| panic!("extract_value index out of bounds"));
        if let Some(view) = self.projection_views[*extract.dest()]
            && let Some(child_view) =
                self.aggregate_projection_view_for_extract(func, module, &view, &extract, result_ty)
        {
            if shape::is_supported_aggregate_ty(module, result_ty) {
                self.projection_views[result] = Some(child_view);
                if self.materialized_addr[result].is_some()
                    || self.value_requires_materialized_slot(func, result)
                {
                    let dst_ptr = self.materialized_ptr(func, result, module);
                    let mut builder = BeforeCursor::new_before_inst(func, inst);
                    self.emit_projection_view_to_ptr_from_snapshot(
                        func,
                        &mut builder,
                        module,
                        &child_view,
                        dst_ptr,
                        result_ty,
                    );
                }
                self.remove_if_results_dead(func, inst);
                return;
            }

            if child_view.runtime_leaf_count != 1 {
                panic!("scalar extract_value must resolve to one runtime leaf");
            }

            let raw = self.snapshot_leaf_value_or_panic(
                child_view.root_value,
                child_view.first_root_runtime_leaf,
            );
            let replacement = if func.dfg.value_ty(raw) == result_ty {
                raw
            } else {
                let mut builder = BeforeCursor::new_before_inst(func, inst);
                builder.insert_with_result(
                    func,
                    cast::Bitcast::new_unchecked(func.inst_set(), raw, result_ty),
                    result_ty,
                )
            };
            self.alias_and_remove(func, inst, result, replacement);
            return;
        }

        if shape::is_supported_aggregate_ty(module, result_ty) {
            let dst_ptr = self.materialized_ptr(func, result, module);
            let mut builder = BeforeCursor::new_before_inst(func, inst);
            self.emit_copy_from_aggregate_slice(
                func,
                module,
                &mut builder,
                AggregateSliceCopySrc {
                    value: *extract.dest(),
                    root_ty: agg_ty,
                    slice,
                },
                AggregateSliceCopyDst {
                    ptr: dst_ptr,
                    ty: result_ty,
                },
            );
            self.remove_if_results_dead(func, inst);
            return;
        }

        if is_explicit_undef(func, *extract.dest()) {
            let undef = func.dfg.make_undef_value(result_ty);
            self.alias_and_remove(func, inst, result, undef);
            return;
        }

        let src_shape = self.shape_or_panic(module, agg_ty);
        let src_leaf = &src_shape.leaves[slice.first_leaf];
        let mut builder = BeforeCursor::new_before_inst(func, inst);
        let src_ptr = self.materialized_ptr(func, *extract.dest(), module);
        let load = self.emit_load_scalar_from_path(
            func,
            &mut builder,
            src_ptr,
            &src_leaf.path,
            src_leaf.ty,
        );
        if func.dfg.value_ty(load) != result_ty {
            panic!("extract_value type mismatch after legalization");
        }
        self.alias_and_remove(func, inst, result, load);
    }

    fn rewrite_extract_value_dynamic_array_index(
        &mut self,
        func: &mut Function,
        module: &ModuleCtx,
        inst: InstId,
        result: ValueId,
        extract: &data::ExtractValue,
    ) {
        let result_ty = func.dfg.value_ty(result);
        let src_value = *extract.dest();
        let src_agg_ty = func.dfg.value_ty(src_value);
        let idx_value = *extract.idx();
        let elem = self.array_elem_ty_or_panic(module, src_agg_ty, "extract_value");
        if elem != result_ty {
            panic!("extract_value result type mismatch for dynamic array index");
        }
        if shape::is_supported_aggregate_ty(module, result_ty) {
            let dst_ptr = self.materialized_ptr(func, result, module);
            let mut builder = BeforeCursor::new_before_inst(func, inst);
            if is_explicit_undef(func, src_value) {
                let undef = func.dfg.make_undef_value(result_ty);
                self.emit_copy_aggregate_value_to_ptr(
                    func,
                    module,
                    &mut builder,
                    undef,
                    dst_ptr,
                    result_ty,
                );
            } else {
                let src_ptr = self.materialized_ptr(func, src_value, module);
                let elem_ptr =
                    self.emit_gep_array_element_ptr(func, &mut builder, src_ptr, idx_value, elem);
                self.emit_copy_aggregate_ptr_to_ptr(
                    func,
                    module,
                    &mut builder,
                    elem_ptr,
                    dst_ptr,
                    result_ty,
                );
            }
            self.remove_if_results_dead(func, inst);
            return;
        }

        if is_explicit_undef(func, src_value) {
            let undef = func.dfg.make_undef_value(result_ty);
            self.alias_and_remove(func, inst, result, undef);
            return;
        }

        let mut builder = BeforeCursor::new_before_inst(func, inst);
        let src_ptr = self.materialized_ptr(func, src_value, module);
        let elem_ptr =
            self.emit_gep_array_element_ptr(func, &mut builder, src_ptr, idx_value, elem);
        let loaded = self.emit_load_scalar_from_path(func, &mut builder, elem_ptr, &[], result_ty);
        self.alias_and_remove(func, inst, result, loaded);
    }

    fn rewrite_aggregate_phi(&mut self, func: &mut Function, module: &ModuleCtx, inst: InstId) {
        let phi = downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst))
            .expect("expected phi")
            .clone();
        let result = func.dfg.inst_result(inst).expect("phi must have result");
        let agg_ty = func.dfg.value_ty(result);
        let dst_ptr = self.materialized_ptr(func, result, module);

        for &(incoming, pred) in phi.args() {
            let term = func
                .layout
                .last_inst_of(pred)
                .unwrap_or_else(|| panic!("phi predecessor {pred:?} has no terminator"));
            let mut builder = BeforeCursor::new_before_inst(func, term);
            self.emit_copy_aggregate_value_to_ptr(
                func,
                module,
                &mut builder,
                incoming,
                dst_ptr,
                agg_ty,
            );
        }

        self.remove_if_results_dead(func, inst);
    }

    fn rewrite_aggregate_mload(&mut self, func: &mut Function, module: &ModuleCtx, inst: InstId) {
        let mload = *downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
            .expect("expected mload");
        let result = func
            .dfg
            .inst_result(inst)
            .expect("aggregate mload must have result");
        if !func
            .dfg
            .users(result)
            .copied()
            .any(|user| func.layout.is_inst_inserted(user))
        {
            self.remove_if_results_dead(func, inst);
            return;
        }

        let agg_ty = *mload.ty();
        let plan = self.plan_mload_projection_uses(func, module, result, agg_ty);
        let mut builder = BeforeCursor::new_before_inst(func, inst);
        let src_ptr = self.aggregate_addr_as_typed_ptr(func, &mut builder, *mload.addr(), agg_ty);
        let runtime_leaves = self.runtime_leaves_or_panic(module, agg_ty);
        let mut snapshot = SnapshotRoot::new(result, src_ptr, runtime_leaves);

        for (root_runtime_leaf, demanded) in plan.demanded_root_runtime_leaves.iter().enumerate() {
            if !demanded {
                continue;
            }
            let leaf_ty = snapshot.runtime_leaves[root_runtime_leaf].ty;
            let _ = snapshot.leaf_as(self, func, &mut builder, root_runtime_leaf, leaf_ty);
        }

        for scalar_use in &plan.scalar_uses {
            if !func.layout.is_inst_inserted(scalar_use.inst) {
                continue;
            }
            let replacement = snapshot.leaf_as(
                self,
                func,
                &mut builder,
                scalar_use.root_runtime_leaf,
                scalar_use.result_ty,
            );
            self.alias_and_remove(func, scalar_use.inst, scalar_use.result, replacement);
        }

        self.remove_dead_transparents(func, &plan.transparent_insts);

        let slot_was_requested = self.materialized_addr[result].is_some();
        if slot_was_requested || self.value_requires_materialized_slot(func, result) {
            let dst_ptr = self.materialized_ptr(func, result, module);
            if slot_was_requested {
                let demanded_root_runtime_leaves = vec![true; snapshot.runtime_leaves.len()];
                snapshot.ensure_slot(
                    self,
                    func,
                    &mut builder,
                    dst_ptr,
                    demanded_root_runtime_leaves.as_slice(),
                );
            } else {
                snapshot.ensure_slot(
                    self,
                    func,
                    &mut builder,
                    dst_ptr,
                    plan.demanded_root_runtime_leaves.as_slice(),
                );
            }
        }

        self.remove_if_results_dead(func, inst);
    }

    fn plan_mload_projection_uses(
        &mut self,
        func: &Function,
        module: &ModuleCtx,
        root_value: ValueId,
        root_ty: Type,
    ) -> MloadProjectionPlan {
        let root_runtime_leaf_count = self.runtime_leaves_or_panic(module, root_ty).len();
        let mut plan = MloadProjectionPlan::new(root_runtime_leaf_count);
        let mut views: SecondaryMap<ValueId, Option<AggregateProjectionView>> =
            SecondaryMap::default();
        let mut worklist = vec![root_value];
        let root_view = AggregateProjectionView {
            root_value,
            root_ty,
            agg_ty: root_ty,
            first_root_runtime_leaf: 0,
            runtime_leaf_count: root_runtime_leaf_count,
        };
        views[root_value] = Some(root_view);
        self.projection_views[root_value] = Some(root_view);

        while let Some(value) = worklist.pop() {
            let Some(view) = views[value] else {
                continue;
            };
            let users: Vec<_> = func.dfg.users(value).copied().collect();
            for &user in &users {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }
                let Some(extract) =
                    downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(user)).cloned()
                else {
                    continue;
                };
                if *extract.dest() != value {
                    continue;
                }
                let Some(extract_result) = func.dfg.inst_result(user) else {
                    plan.mark_view_runtime_leaves(&view);
                    continue;
                };
                let result_ty = func.dfg.value_ty(extract_result);
                let Some(child_view) = self.aggregate_projection_view_for_extract(
                    func, module, &view, &extract, result_ty,
                ) else {
                    plan.mark_view_runtime_leaves(&view);
                    continue;
                };
                if shape::is_supported_aggregate_ty(module, result_ty) {
                    views[extract_result] = Some(child_view);
                    self.projection_views[extract_result] = Some(child_view);
                    plan.transparent_insts.push(user);
                    worklist.push(extract_result);
                    continue;
                }
                if child_view.runtime_leaf_count == 1 {
                    plan.add_scalar_use(
                        user,
                        extract_result,
                        child_view.first_root_runtime_leaf,
                        result_ty,
                    );
                    continue;
                }
                plan.mark_view_runtime_leaves(&view);
            }

            for &user in &users {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }
                let Some(bitcast) =
                    downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(user)).cloned()
                else {
                    continue;
                };
                if *bitcast.from() != value {
                    continue;
                }
                let Some(bitcast_result) = func.dfg.inst_result(user) else {
                    plan.mark_view_runtime_leaves(&view);
                    continue;
                };
                let bitcast_ty = func.dfg.value_ty(bitcast_result);
                let Some(bitcast_view) =
                    self.aggregate_projection_view_for_bitcast(module, &view, bitcast_ty)
                else {
                    plan.mark_view_runtime_leaves(&view);
                    continue;
                };
                views[bitcast_result] = Some(bitcast_view);
                self.projection_views[bitcast_result] = Some(bitcast_view);
                plan.transparent_insts.push(user);
                worklist.push(bitcast_result);
            }
            for &user in &users {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }
                if downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(user))
                    .is_some_and(|extract| *extract.dest() == value)
                    || downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(user))
                        .is_some_and(|bitcast| *bitcast.from() == value)
                {
                    continue;
                }
                plan.mark_view_runtime_leaves(&view);
            }
        }

        plan
    }

    fn aggregate_projection_view_for_extract(
        &mut self,
        func: &Function,
        module: &ModuleCtx,
        view: &AggregateProjectionView,
        extract: &data::ExtractValue,
        result_ty: Type,
    ) -> Option<AggregateProjectionView> {
        let idx = shape::const_u32(&func.dfg, *extract.idx())?;
        let slice = shape::aggregate_slice_for_index(module, view.agg_ty, idx)?;
        if slice.ty != result_ty {
            return None;
        }
        let (first_runtime_leaf, runtime_leaf_count) =
            shape::runtime_leaf_range_for_slice(module, view.agg_ty, slice)?;
        let first_root_runtime_leaf = view
            .first_root_runtime_leaf
            .checked_add(first_runtime_leaf)
            .unwrap_or_else(|| panic!("aggregate projection runtime leaf range overflow"));
        let end = first_root_runtime_leaf
            .checked_add(runtime_leaf_count)
            .unwrap_or_else(|| panic!("aggregate projection runtime leaf range overflow"));
        if end > self.runtime_leaves_or_panic(module, view.root_ty).len() {
            panic!("aggregate projection runtime leaf range out of bounds");
        }
        Some(AggregateProjectionView {
            root_value: view.root_value,
            root_ty: view.root_ty,
            agg_ty: result_ty,
            first_root_runtime_leaf,
            runtime_leaf_count,
        })
    }

    fn aggregate_projection_view_for_bitcast(
        &mut self,
        module: &ModuleCtx,
        view: &AggregateProjectionView,
        bitcast_ty: Type,
    ) -> Option<AggregateProjectionView> {
        if !shape::is_supported_aggregate_ty(module, bitcast_ty)
            || self
                .layout_cache
                .compatible_bitcast_runtime_leaves(module, view.agg_ty, bitcast_ty)
                .is_none()
        {
            return None;
        }
        if self.runtime_leaves_or_panic(module, bitcast_ty).len() != view.runtime_leaf_count {
            return None;
        }
        Some(AggregateProjectionView {
            root_value: view.root_value,
            root_ty: view.root_ty,
            agg_ty: bitcast_ty,
            first_root_runtime_leaf: view.first_root_runtime_leaf,
            runtime_leaf_count: view.runtime_leaf_count,
        })
    }

    fn remove_dead_transparents(&self, func: &mut Function, transparent_insts: &[InstId]) {
        for &inst in transparent_insts.iter().rev() {
            if func.layout.is_inst_inserted(inst) {
                self.remove_if_results_dead(func, inst);
            }
        }
    }

    fn rewrite_aggregate_mstore(&mut self, func: &mut Function, module: &ModuleCtx, inst: InstId) {
        let mstore = *downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
            .expect("expected mstore");
        let agg_ty = *mstore.ty();
        let mut builder = BeforeCursor::new_before_inst(func, inst);
        let dst_ptr = self.aggregate_addr_as_typed_ptr(func, &mut builder, *mstore.addr(), agg_ty);
        self.emit_copy_aggregate_value_to_ptr(
            func,
            module,
            &mut builder,
            *mstore.value(),
            dst_ptr,
            agg_ty,
        );
        self.remove_if_results_dead(func, inst);
    }

    fn shape_or_panic(&mut self, module: &ModuleCtx, ty: Type) -> shape::AggregateShape {
        self.layout_cache
            .shape(module, ty)
            .unwrap_or_else(|| panic!("unsupported aggregate type in legalizer: {ty:?}"))
    }

    fn runtime_leaves_or_panic(&mut self, module: &ModuleCtx, ty: Type) -> shape::RuntimeLeaves {
        self.layout_cache
            .runtime_leaves(module, ty)
            .unwrap_or_else(|| panic!("unsupported aggregate type in legalizer: {ty:?}"))
    }

    fn array_elem_ty_or_panic(&self, module: &ModuleCtx, ty: Type, ctx: &str) -> Type {
        let Some(CompoundType::Array { elem, .. }) = ty.resolve_compound(module) else {
            panic!("{ctx} dynamic index is only supported for arrays");
        };
        elem
    }

    fn aggregate_bitcast_leaf_layout(
        &mut self,
        module: &ModuleCtx,
        from_ty: Type,
        to_ty: Type,
    ) -> (shape::RuntimeLeaves, shape::RuntimeLeaves) {
        let src_leaves = self.runtime_leaves_or_panic(module, from_ty);
        let dst_leaves = self.runtime_leaves_or_panic(module, to_ty);

        if src_leaves.len() != dst_leaves.len() {
            panic!(
                "aggregate bitcast leaf count mismatch: {from_ty:?} ({}) -> {to_ty:?} ({})",
                src_leaves.len(),
                dst_leaves.len()
            );
        }

        for (src_leaf, dst_leaf) in src_leaves.iter().zip(&dst_leaves) {
            if src_leaf.offset_bytes != dst_leaf.offset_bytes
                || src_leaf.size_bytes != dst_leaf.size_bytes
            {
                panic!(
                    "aggregate bitcast leaf layout mismatch: {from_ty:?} ({src_leaf:?}) -> {to_ty:?} ({dst_leaf:?})"
                );
            }
        }

        (src_leaves, dst_leaves)
    }

    fn materialized_ptr(
        &mut self,
        func: &mut Function,
        value: ValueId,
        module: &ModuleCtx,
    ) -> ValueId {
        if is_explicit_undef(func, value) {
            panic!("explicit undef aggregate has no materialized pointer");
        }
        let ty = func.dfg.value_ty(value);
        if !shape::is_supported_aggregate_ty(module, ty) {
            panic!("expected aggregate value, got {ty:?}");
        }
        if let Some(ptr) = self.materialized_addr[value] {
            return ptr;
        }
        let ptr = self.create_temp_alloca(func, ty);
        self.materialized_addr[value] = Some(ptr);
        self.materialized_slots.push(ptr);
        ptr
    }

    fn snapshot_leaf_value_or_panic(
        &self,
        root_value: ValueId,
        root_runtime_leaf: usize,
    ) -> ValueId {
        self.snapshot_leaf_values
            .get(&(root_value, root_runtime_leaf))
            .copied()
            .unwrap_or_else(|| panic!("missing cached snapshot leaf for aggregate projection"))
    }

    fn emit_projection_view_to_ptr_from_snapshot(
        &mut self,
        func: &mut Function,
        builder: &mut BeforeCursor,
        module: &ModuleCtx,
        view: &AggregateProjectionView,
        dst_ptr: ValueId,
        dst_ty: Type,
    ) {
        let dst_leaves = self.runtime_leaves_or_panic(module, dst_ty);
        if dst_leaves.len() != view.runtime_leaf_count {
            panic!("aggregate projection runtime leaf count mismatch");
        }

        for (leaf_idx, dst_leaf) in dst_leaves.iter().enumerate() {
            let root_runtime_leaf = view
                .first_root_runtime_leaf
                .checked_add(leaf_idx)
                .unwrap_or_else(|| panic!("aggregate projection runtime leaf range overflow"));
            let raw = self.snapshot_leaf_value_or_panic(view.root_value, root_runtime_leaf);
            let stored = if func.dfg.value_ty(raw) == dst_leaf.ty {
                raw
            } else {
                builder.insert_with_result(
                    func,
                    cast::Bitcast::new_unchecked(func.inst_set(), raw, dst_leaf.ty),
                    dst_leaf.ty,
                )
            };
            self.emit_store_scalar_to_path(
                func,
                builder,
                dst_ptr,
                &dst_leaf.path,
                stored,
                dst_leaf.ty,
            );
        }
    }

    fn value_requires_materialized_slot(&self, func: &Function, value: ValueId) -> bool {
        for &user in func.dfg.users(value) {
            if !func.layout.is_inst_inserted(user) {
                continue;
            }
            if downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(user)).is_some_and(
                |extract| {
                    *extract.dest() == value
                        && shape::const_u32(&func.dfg, *extract.idx()).is_some()
                },
            ) || downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(user))
                .is_some_and(|bitcast| *bitcast.from() == value)
                || downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(user))
                    .is_some_and(|mstore| *mstore.value() == value)
                || downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(user))
                    .is_some_and(|insert| *insert.dest() == value)
                || downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(user))
                    .is_some_and(|phi| phi.args().iter().any(|&(incoming, _)| incoming == value))
            {
                continue;
            }
            return true;
        }
        false
    }

    fn emit_store_undef_to_leaves(
        &self,
        func: &mut Function,
        builder: &mut BeforeCursor,
        dst_ptr: ValueId,
        leaves: &[shape::AggregateLeaf],
    ) {
        for leaf in leaves {
            if leaf.size_bytes == 0 {
                continue;
            }
            let undef = func.dfg.make_undef_value(leaf.ty);
            self.emit_store_scalar_to_path(func, builder, dst_ptr, &leaf.path, undef, leaf.ty);
        }
    }

    fn emit_copy_aggregate_value_to_ptr(
        &mut self,
        func: &mut Function,
        module: &ModuleCtx,
        builder: &mut BeforeCursor,
        value: ValueId,
        dst_ptr: ValueId,
        agg_ty: Type,
    ) {
        let shape = self.shape_or_panic(module, agg_ty);
        if is_explicit_undef(func, value) {
            self.emit_store_undef_to_leaves(func, builder, dst_ptr, &shape.leaves);
            return;
        }

        if let Some(view) = self.projection_views[value] {
            self.emit_projection_view_to_ptr_from_snapshot(
                func, builder, module, &view, dst_ptr, agg_ty,
            );
            return;
        }

        let src_ptr = self.materialized_ptr(func, value, module);
        self.emit_copy_aggregate_ptr_to_ptr(func, module, builder, src_ptr, dst_ptr, agg_ty);
    }

    fn emit_copy_aggregate_ptr_to_ptr(
        &mut self,
        func: &mut Function,
        module: &ModuleCtx,
        builder: &mut BeforeCursor,
        src_ptr: ValueId,
        dst_ptr: ValueId,
        agg_ty: Type,
    ) {
        let shape = self.shape_or_panic(module, agg_ty);
        self.emit_copy_leaf_slices_ptr_to_ptr(
            func,
            builder,
            src_ptr,
            &shape.leaves,
            dst_ptr,
            &shape.leaves,
        );
    }

    fn emit_copy_leaf_slices_ptr_to_ptr(
        &self,
        func: &mut Function,
        builder: &mut BeforeCursor,
        src_ptr: ValueId,
        src_leaves: &[shape::AggregateLeaf],
        dst_ptr: ValueId,
        dst_leaves: &[shape::AggregateLeaf],
    ) {
        assert_eq!(
            src_leaves.len(),
            dst_leaves.len(),
            "copy leaf slice length mismatch during legalization"
        );
        for (src_leaf, dst_leaf) in src_leaves.iter().zip(dst_leaves) {
            assert_eq!(
                src_leaf.size_bytes, dst_leaf.size_bytes,
                "copy leaf size mismatch during legalization"
            );
            if dst_leaf.size_bytes == 0 {
                continue;
            }
            let loaded = self.emit_load_scalar_from_path(
                func,
                builder,
                src_ptr,
                &src_leaf.path,
                src_leaf.ty,
            );
            let stored = if src_leaf.ty == dst_leaf.ty {
                loaded
            } else {
                builder.insert_with_result(
                    func,
                    cast::Bitcast::new_unchecked(func.inst_set(), loaded, dst_leaf.ty),
                    dst_leaf.ty,
                )
            };
            self.emit_store_scalar_to_path(
                func,
                builder,
                dst_ptr,
                &dst_leaf.path,
                stored,
                dst_leaf.ty,
            );
        }
    }

    fn emit_copy_subaggregate_value_to_slice(
        &mut self,
        func: &mut Function,
        module: &ModuleCtx,
        builder: &mut BeforeCursor,
        value: ValueId,
        dst: SubaggregateSliceDst,
    ) {
        let dst_shape = self.shape_or_panic(module, dst.root_ty);
        let payload_ty = dst.slice.ty;
        let payload_shape = self.shape_or_panic(module, payload_ty);
        if payload_shape.leaves.len() != dst.slice.leaf_count {
            panic!("insert_value slice leaf mismatch during legalization");
        }

        if is_explicit_undef(func, value) {
            let dst_leaves = &dst_shape.leaves
                [dst.slice.first_leaf..dst.slice.first_leaf + dst.slice.leaf_count];
            self.emit_store_undef_to_leaves(func, builder, dst.ptr, dst_leaves);
            return;
        }

        let src_ptr = self.materialized_ptr(func, value, module);
        let src_leaves = &payload_shape.leaves[..dst.slice.leaf_count];
        let dst_leaves =
            &dst_shape.leaves[dst.slice.first_leaf..dst.slice.first_leaf + dst.slice.leaf_count];
        self.emit_copy_leaf_slices_ptr_to_ptr(
            func, builder, src_ptr, src_leaves, dst.ptr, dst_leaves,
        );
    }

    fn emit_copy_from_aggregate_slice(
        &mut self,
        func: &mut Function,
        module: &ModuleCtx,
        builder: &mut BeforeCursor,
        src: AggregateSliceCopySrc,
        dst: AggregateSliceCopyDst,
    ) {
        let dst_shape = self.shape_or_panic(module, dst.ty);
        if dst_shape.leaves.len() != src.slice.leaf_count {
            panic!("extract_value slice leaf mismatch during legalization");
        }

        if is_explicit_undef(func, src.value) {
            let undef = func.dfg.make_undef_value(dst.ty);
            self.emit_copy_aggregate_value_to_ptr(func, module, builder, undef, dst.ptr, dst.ty);
            return;
        }

        let src_ptr = self.materialized_ptr(func, src.value, module);
        let src_shape = self.shape_or_panic(module, src.root_ty);
        let src_leaves =
            &src_shape.leaves[src.slice.first_leaf..src.slice.first_leaf + src.slice.leaf_count];
        self.emit_copy_leaf_slices_ptr_to_ptr(
            func,
            builder,
            src_ptr,
            src_leaves,
            dst.ptr,
            &dst_shape.leaves,
        );
    }

    fn emit_load_scalar_from_path(
        &self,
        func: &mut Function,
        builder: &mut BeforeCursor,
        base_ptr: ValueId,
        path: &[u32],
        ty: Type,
    ) -> ValueId {
        let ptr = self.emit_gep_to_path(func, builder, base_ptr, path, ty);
        builder.insert_with_result(
            func,
            data::Mload::new_unchecked(func.inst_set(), ptr, ty),
            ty,
        )
    }

    fn emit_store_scalar_to_path(
        &self,
        func: &mut Function,
        builder: &mut BeforeCursor,
        base_ptr: ValueId,
        path: &[u32],
        value: ValueId,
        ty: Type,
    ) {
        let ptr = self.emit_gep_to_path(func, builder, base_ptr, path, ty);
        builder.insert_no_result(
            func,
            data::Mstore::new_unchecked(func.inst_set(), ptr, value, ty),
        );
    }

    fn aggregate_addr_as_typed_ptr(
        &self,
        func: &mut Function,
        builder: &mut BeforeCursor,
        addr: ValueId,
        agg_ty: Type,
    ) -> ValueId {
        let ptr_ty = agg_ty.to_ptr(func.ctx());
        let addr_ty = func.dfg.value_ty(addr);
        if addr_ty == ptr_ty {
            return addr;
        }
        if addr_ty.is_pointer(func.ctx()) {
            return builder.insert_with_result(
                func,
                cast::Bitcast::new_unchecked(func.inst_set(), addr, ptr_ty),
                ptr_ty,
            );
        }
        if addr_ty.is_integral() {
            return builder.insert_with_result(
                func,
                cast::IntToPtr::new_unchecked(func.inst_set(), addr, ptr_ty),
                ptr_ty,
            );
        }
        panic!("aggregate memory address must be integral or pointer (got {addr_ty:?})");
    }

    fn emit_gep_to_path(
        &self,
        func: &mut Function,
        builder: &mut BeforeCursor,
        base_ptr: ValueId,
        path: &[u32],
        leaf_ty: Type,
    ) -> ValueId {
        if path.is_empty() {
            return base_ptr;
        }
        let mut values: SmallVec<[ValueId; 8]> = smallvec![base_ptr, func.dfg.make_imm_value(0i64)];
        for &idx in path {
            values.push(func.dfg.make_imm_value(i64::from(idx)));
        }
        let ptr_ty = leaf_ty.to_ptr(func.ctx());
        builder.insert_with_result(
            func,
            data::Gep::new_unchecked(func.inst_set(), values),
            ptr_ty,
        )
    }

    fn emit_gep_array_element_ptr(
        &self,
        func: &mut Function,
        builder: &mut BeforeCursor,
        base_ptr: ValueId,
        idx_value: ValueId,
        elem_ty: Type,
    ) -> ValueId {
        let values: SmallVec<[ValueId; 8]> =
            smallvec![base_ptr, func.dfg.make_imm_value(0i64), idx_value];
        let ptr_ty = elem_ty.to_ptr(func.ctx());
        builder.insert_with_result(
            func,
            data::Gep::new_unchecked(func.inst_set(), values),
            ptr_ty,
        )
    }

    fn remove_dead_materialized_slots(&mut self, func: &mut Function) -> bool {
        let slot_ptrs = mem::take(&mut self.materialized_slots);
        let mut changed = false;

        loop {
            let mut removed_any = false;

            for &slot_ptr in &slot_ptrs {
                if !func.dfg.has_value(slot_ptr) {
                    continue;
                }
                if !func
                    .dfg
                    .value_inst(slot_ptr)
                    .is_some_and(|inst| func.layout.is_inst_inserted(inst))
                {
                    continue;
                }
                if !self.collect_dead_materialized_slot_insts(func, slot_ptr) {
                    continue;
                }

                self.slot_tree_seen_insts.clear();
                for &inst in self.slot_tree_insts.iter().rev() {
                    if !self.slot_tree_seen_insts.insert(inst)
                        || !func.layout.is_inst_inserted(inst)
                    {
                        continue;
                    }
                    InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                    removed_any = true;
                    changed = true;
                }
            }

            if !removed_any {
                self.materialized_slots = slot_ptrs;
                return changed;
            }
        }
    }

    fn collect_dead_aggregate_alloca_slots(&mut self, func: &Function, module: &ModuleCtx) {
        self.materialized_slots.clear();
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                let Some(alloca) = downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst))
                else {
                    continue;
                };
                if !shape::is_supported_aggregate_ty(module, *alloca.ty()) {
                    continue;
                }
                if let Some(slot_ptr) = func.dfg.inst_result(inst) {
                    self.materialized_slots.push(slot_ptr);
                }
            }
        }
    }

    fn collect_dead_materialized_slot_insts(&mut self, func: &Function, slot_ptr: ValueId) -> bool {
        self.slot_tree_insts.clear();
        self.slot_tree_queue.clear();
        self.slot_tree_seen_values.clear();

        let Some(alloca_inst) = func.dfg.value_inst(slot_ptr) else {
            return false;
        };
        self.slot_tree_insts.push(alloca_inst);
        self.slot_tree_queue.push(slot_ptr);

        while let Some(value) = self.slot_tree_queue.pop() {
            if !self.slot_tree_seen_values.insert(value) {
                continue;
            }

            for &user in func.dfg.users(value) {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }

                if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(user))
                    && gep.values().first().copied() == Some(value)
                {
                    self.slot_tree_insts.push(user);
                    if let Some(result) = func.dfg.inst_result(user) {
                        self.slot_tree_queue.push(result);
                    }
                    continue;
                }

                if let Some(bitcast) =
                    downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(user))
                    && *bitcast.from() == value
                {
                    self.slot_tree_insts.push(user);
                    if let Some(result) = func.dfg.inst_result(user) {
                        self.slot_tree_queue.push(result);
                    }
                    continue;
                }

                if let Some(mstore) =
                    downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(user))
                    && *mstore.addr() == value
                {
                    self.slot_tree_insts.push(user);
                    continue;
                }

                if let Some(mload) = downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(user))
                    && *mload.addr() == value
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if func
                        .dfg
                        .users(result)
                        .copied()
                        .any(|load_user| func.layout.is_inst_inserted(load_user))
                    {
                        return false;
                    }
                    self.slot_tree_insts.push(user);
                    continue;
                }

                return false;
            }
        }

        true
    }
}

#[derive(Clone, Copy)]
struct SubaggregateSliceDst {
    ptr: ValueId,
    root_ty: Type,
    slice: shape::AggregateSlice,
}

#[derive(Clone, Copy)]
struct AggregateSliceCopySrc {
    value: ValueId,
    root_ty: Type,
    slice: shape::AggregateSlice,
}

#[derive(Clone, Copy)]
struct AggregateSliceCopyDst {
    ptr: ValueId,
    ty: Type,
}

struct BeforeCursor {
    cursor: InstInserter,
}

impl BeforeCursor {
    fn new_before_inst(func: &Function, inst: InstId) -> Self {
        let block = func.layout.inst_block(inst);
        let loc = if let Some(prev) = func.layout.prev_inst_of(inst) {
            CursorLocation::At(prev)
        } else {
            CursorLocation::BlockTop(block)
        };
        Self {
            cursor: InstInserter::at_location(loc),
        }
    }

    fn insert_no_result<I: Inst>(&mut self, func: &mut Function, inst_data: I) -> InstId {
        let inst = self.cursor.insert_inst_data(func, inst_data);
        self.cursor.set_location(CursorLocation::At(inst));
        inst
    }

    fn insert_with_result<I: Inst>(
        &mut self,
        func: &mut Function,
        inst_data: I,
        ty: Type,
    ) -> ValueId {
        let inst = self.insert_no_result(func, inst_data);
        let value = func.dfg.make_value(Value::Inst {
            inst,
            result_idx: 0,
            ty,
        });
        self.cursor.attach_result(func, inst, value);
        value
    }
}

fn scan_aggregate_legalize_needs(func: &Function, module: &ModuleCtx) -> AggregateLegalizeScan {
    let mut scan = AggregateLegalizeScan::default();

    for &arg in &func.arg_values {
        let ty = func.dfg.value_ty(arg);
        if shape::is_supported_aggregate_ty(module, ty) {
            panic!("aggregate function arguments are unsupported by aggregate legalization");
        }
    }

    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if let Some(call) =
                downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
            {
                if call
                    .args()
                    .iter()
                    .any(|&arg| shape::is_supported_aggregate_ty(module, func.dfg.value_ty(arg)))
                {
                    panic!("aggregate call arguments are unsupported by aggregate legalization");
                }
                if func.dfg.inst_results(inst).iter().copied().any(|result| {
                    shape::is_supported_aggregate_ty(module, func.dfg.value_ty(result))
                }) {
                    panic!("aggregate call results are unsupported by aggregate legalization");
                }
            }

            if let Some(ret) =
                downcast::<&control_flow::Return>(func.inst_set(), func.dfg.inst(inst))
                && ret
                    .args()
                    .iter()
                    .copied()
                    .any(|arg| shape::is_supported_aggregate_ty(module, func.dfg.value_ty(arg)))
            {
                panic!("aggregate return values are unsupported by aggregate legalization");
            }

            if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst))
            {
                let from_ty = func.dfg.value_ty(*bitcast.from());
                let to_ty = func
                    .dfg
                    .inst_result(inst)
                    .map(|value| func.dfg.value_ty(value))
                    .unwrap_or(Type::Unit);
                if shape::is_supported_aggregate_ty(module, from_ty)
                    || shape::is_supported_aggregate_ty(module, to_ty)
                {
                    scan.has_work = true;
                    scan.candidates[block].push(inst);
                }
                continue;
            }

            if downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst)).is_some() {
                if func.dfg.inst_result(inst).is_some_and(|value| {
                    shape::is_supported_aggregate_ty(module, func.dfg.value_ty(value))
                }) {
                    scan.has_work = true;
                    scan.candidates[block].push(inst);
                }
                continue;
            }

            if let Some(extract) =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst))
            {
                if shape::is_supported_aggregate_ty(module, func.dfg.value_ty(*extract.dest())) {
                    scan.has_work = true;
                    scan.candidates[block].push(inst);
                }
                continue;
            }

            if downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_some() {
                let has_agg_phi = func.dfg.inst_result(inst).is_some_and(|value| {
                    shape::is_supported_aggregate_ty(module, func.dfg.value_ty(value))
                });
                if has_agg_phi {
                    scan.has_work = true;
                    scan.has_agg_phi = true;
                    scan.candidates[block].push(inst);
                }
                continue;
            }

            if let Some(mload) = downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst)) {
                if shape::is_supported_aggregate_ty(module, *mload.ty()) {
                    scan.has_work = true;
                    scan.candidates[block].push(inst);
                }
                continue;
            }

            if let Some(mstore) = downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
                && shape::is_supported_aggregate_ty(module, *mstore.ty())
            {
                scan.has_work = true;
                scan.candidates[block].push(inst);
            }
        }
    }

    scan
}

fn aggregate_legalize_block_order(
    func: &Function,
    cfg: &ControlFlowGraph,
) -> SmallVec<[BlockId; 16]> {
    let mut blocks = SmallVec::new();
    let mut seen = FxHashSet::default();
    if let Some(entry) = func.layout.entry_block() {
        append_component_rpo(cfg, entry, &mut seen, &mut blocks);
    }
    for block in func.layout.iter_block() {
        if !seen.contains(&block) {
            append_component_rpo(cfg, block, &mut seen, &mut blocks);
        }
    }

    blocks
}

fn append_component_rpo(
    cfg: &ControlFlowGraph,
    start: BlockId,
    seen: &mut FxHashSet<BlockId>,
    blocks: &mut SmallVec<[BlockId; 16]>,
) {
    let mut post_order = SmallVec::<[BlockId; 16]>::new();
    let mut stack = SmallVec::<[(BlockId, bool); 16]>::new();
    stack.push((start, false));

    while let Some((block, expanded)) = stack.pop() {
        if expanded {
            post_order.push(block);
            continue;
        }
        if !seen.insert(block) {
            continue;
        }

        stack.push((block, true));
        let mut succs: Vec<_> = cfg.succs_of(block).copied().collect();
        succs.reverse();
        for succ in succs {
            if !seen.contains(&succ) {
                stack.push((succ, false));
            }
        }
    }

    post_order.reverse();
    blocks.extend(post_order);
}

fn is_explicit_undef(func: &Function, value: ValueId) -> bool {
    matches!(func.dfg.value(value), Value::Undef { .. })
}

pub fn assert_aggregate_legalized(function: &Function, module: &ModuleCtx) {
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if let Some(bitcast) =
                downcast::<&cast::Bitcast>(function.inst_set(), function.dfg.inst(inst))
            {
                let from_ty = function.dfg.value_ty(*bitcast.from());
                let to_ty = function
                    .dfg
                    .inst_result(inst)
                    .map(|v| function.dfg.value_ty(v))
                    .unwrap_or(Type::Unit);
                if shape::is_supported_aggregate_ty(module, from_ty)
                    || shape::is_supported_aggregate_ty(module, to_ty)
                {
                    panic!(
                        "aggregate legalization invariant violated: aggregate bitcast remains (inst {})",
                        inst.as_u32()
                    );
                }
            }
            if downcast::<&data::InsertValue>(function.inst_set(), function.dfg.inst(inst))
                .is_some()
            {
                panic!(
                    "aggregate legalization invariant violated: insert_value remains (inst {})",
                    inst.as_u32()
                );
            }
            if downcast::<&data::ExtractValue>(function.inst_set(), function.dfg.inst(inst))
                .is_some()
            {
                panic!(
                    "aggregate legalization invariant violated: extract_value remains (inst {})",
                    inst.as_u32()
                );
            }
            if downcast::<&control_flow::Phi>(function.inst_set(), function.dfg.inst(inst))
                .is_some()
                && function.dfg.inst_result(inst).is_some_and(|v| {
                    shape::is_supported_aggregate_ty(module, function.dfg.value_ty(v))
                })
            {
                panic!(
                    "aggregate legalization invariant violated: aggregate phi remains (inst {})",
                    inst.as_u32()
                );
            }
            if let Some(mload) =
                downcast::<&data::Mload>(function.inst_set(), function.dfg.inst(inst))
                && shape::is_supported_aggregate_ty(module, *mload.ty())
            {
                panic!(
                    "aggregate legalization invariant violated: aggregate mload remains (inst {})",
                    inst.as_u32()
                );
            }
            if let Some(mstore) =
                downcast::<&data::Mstore>(function.inst_set(), function.dfg.inst(inst))
                && shape::is_supported_aggregate_ty(module, *mstore.ty())
            {
                panic!(
                    "aggregate legalization invariant violated: aggregate mstore remains (inst {})",
                    inst.as_u32()
                );
            }
        }
    }
}

pub fn cleanup_dead_aggregate_alloca_trees(function: &mut Function, module: &ModuleCtx) -> bool {
    let mut cleanup = AggregateLowerToMemoryLegalize::default();
    cleanup.collect_dead_aggregate_alloca_slots(function, module);

    let mut changed = false;
    loop {
        let removed_slots = cleanup.remove_dead_materialized_slots(function);
        let removed_pure = cleanup.dead_pure_cleanup.run_with_current_users(function);
        let progress = removed_slots || removed_pure;
        changed |= progress;
        if !progress {
            return changed;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::{EvmBackend, PushWidthPolicy},
        object::{CompileOptions, compile_all_objects},
    };
    use revm::{
        Context, EvmContext, Handler,
        primitives::{
            AccountInfo, Address, Bytecode, Bytes, Env, ExecutionResult, OsakaSpec, Output,
            TransactTo, U256,
        },
    };
    use sonatina_ir::{Module, isa::evm::Evm, module::FuncRef};
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
    use sonatina_verifier::{VerificationLevel, VerifierConfig};

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

    fn test_backend() -> EvmBackend {
        let triple = TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        );
        EvmBackend::new(Evm::new(triple))
    }

    fn test_compile_opts() -> CompileOptions {
        CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        }
    }

    fn run_contract(module: &Module) -> U256 {
        let artifacts = compile_all_objects(module, &test_backend(), &test_compile_opts())
            .expect("compile should succeed");
        let artifact = artifacts
            .iter()
            .find(|artifact| artifact.object.0.as_str() == "Contract")
            .expect("missing Contract object");
        let runtime = artifact
            .sections
            .iter()
            .find(|(name, _)| name.0.as_str() == "runtime")
            .map(|(_, section)| section.bytes.as_slice())
            .expect("missing runtime section");

        let mut db = revm::InMemoryDB::default();
        let bytecode = Bytecode::new_raw(Bytes::copy_from_slice(runtime));
        let contract = Address::repeat_byte(0x12);
        db.insert_account_info(
            contract,
            AccountInfo {
                balance: U256::ZERO,
                nonce: 0,
                code_hash: bytecode.hash_slow(),
                code: Some(bytecode),
            },
        );

        let mut env = Env::default();
        env.tx.clear();
        env.tx.transact_to = TransactTo::Call(contract);
        env.tx.data = Bytes::default();

        struct NoopInspector;
        impl<DB: revm::Database> revm::Inspector<DB> for NoopInspector {}

        let context = Context::new(EvmContext::new_with_env(db, Box::new(env)), NoopInspector);
        let mut evm = revm::Evm::new(context, Handler::mainnet::<OsakaSpec>());
        let res = evm.transact_commit().expect("evm execution should succeed");

        match res {
            ExecutionResult::Success {
                output: Output::Call(bytes),
                ..
            } => U256::from_be_slice(bytes.as_ref()),
            _ => panic!("unexpected execution result: {res:?}"),
        }
    }

    #[test]
    fn aggregate_bitcast_across_compatible_shapes_compiles() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i256 };
type @pair = { i256, i256 };
type @nested = { @inner, i256 };

func public %entry() {
    block0:
        v0.i256 = evm_calldata_load 0.i32;
        v1.i256 = evm_calldata_load 32.i32;
        v2.@pair = insert_value undef.@pair 0.i8 v0;
        v3.@pair = insert_value v2 1.i8 v1;
        v4.@nested = bitcast v3 @nested;
        v5.@inner = extract_value v4 0.i8;
        v6.i256 = extract_value v5 0.i8;
        mstore 0.i32 v6 i256;
        evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );

        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        };
        compile_all_objects(&module, &test_backend(), &opts).expect("compile should succeed");
    }

    #[test]
    fn late_legalizer_removes_aggregate_ops_and_scalarizes_memory_types() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i256 };
type @pair = { i256, i256 };
type @nested = { @inner, i256 };

func private %f(v0.i1, v1.i256, v2.i256) -> i256 {
    block0:
        v3.@pair = insert_value undef.@pair 0.i8 v1;
        v4.@pair = insert_value v3 1.i8 v2;
        v5.*@pair = alloca @pair;
        mstore v5 v4 @pair;
        br v0 block1 block2;

    block1:
        v6.@nested = bitcast v4 @nested;
        jump block3;

    block2:
        v7.@pair = mload v5 @pair;
        v8.@nested = bitcast v7 @nested;
        jump block3;

    block3:
        v9.@nested = phi (v6 block1) (v8 block2);
        v10.@inner = extract_value v9 0.i8;
        v11.i256 = extract_value v10 0.i8;
        return v11;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });

        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(mload) =
                        downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
                    {
                        assert!(
                            !shape::is_supported_aggregate_ty(&ctx, *mload.ty()),
                            "aggregate mload should be gone"
                        );
                    }
                    if let Some(mstore) =
                        downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
                    {
                        assert!(
                            !shape::is_supported_aggregate_ty(&ctx, *mstore.ty()),
                            "aggregate mstore should be gone"
                        );
                    }
                }
            }
        });
    }

    #[test]
    fn late_legalizer_drops_dead_materialization_slots() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.i256) -> i256 {
    block0:
        v1.@pair = insert_value undef.@pair 0.i8 v0;
        v2.@pair = insert_value v1 1.i8 9.i256;
        return 0.i256;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });

        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    assert!(
                        downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                        "dead materialization alloca should be removed"
                    );
                }
            }
        });
    }

    #[test]
    fn late_legalizer_handles_pointer_valued_aggregates() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { *i8, i256 };

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        v2.*i8 = int_to_ptr v0 *i8;
        v3.*i8 = int_to_ptr v1 *i8;
        v4.@pair = insert_value undef.@pair 0.i8 v2;
        v5.@pair = insert_value v4 1.i8 9.i256;
        v6.*@pair = alloca @pair;
        mstore v6 v5 @pair;
        v7.@pair = mload v6 @pair;
        v8.*i8 = extract_value v7 0.i8;
        v9.i256 = ptr_to_int v8 i256;
        v10.[*i8; 2] = insert_value undef.[*i8; 2] 0.i8 v2;
        v11.[*i8; 2] = insert_value v10 1.i8 v3;
        v12.*[*i8; 2] = alloca [*i8; 2];
        mstore v12 v11 [*i8; 2];
        v13.[*i8; 2] = mload v12 [*i8; 2];
        v14.*i8 = extract_value v13 1.i8;
        v15.i256 = ptr_to_int v14 i256;
        v16.i256 = add v9 v15;
        return v16;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });

        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(mload) =
                        downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
                    {
                        assert!(
                            !shape::is_supported_aggregate_ty(&ctx, *mload.ty()),
                            "aggregate mload should be gone"
                        );
                    }
                    if let Some(mstore) =
                        downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
                    {
                        assert!(
                            !shape::is_supported_aggregate_ty(&ctx, *mstore.ty()),
                            "aggregate mstore should be gone"
                        );
                    }
                }
            }
        });
    }

    #[test]
    fn late_legalizer_handles_zero_sized_subaggregates() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @empty = {};
type @outer = { @empty, i256 };

func private %f(v0.i256) -> i256 {
    block0:
        v1.@outer = insert_value undef.@outer 0.i8 undef.@empty;
        v2.@outer = insert_value v1 1.i8 v0;
        v3.@empty = extract_value v2 0.i8;
        v4.i256 = extract_value v2 1.i8;
        return v4;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });

        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(mload) =
                        downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
                    {
                        assert!(
                            !shape::is_supported_aggregate_ty(&ctx, *mload.ty()),
                            "aggregate mload should be gone"
                        );
                    }
                    if let Some(mstore) =
                        downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
                    {
                        assert!(
                            !shape::is_supported_aggregate_ty(&ctx, *mstore.ty()),
                            "aggregate mstore should be gone"
                        );
                    }
                }
            }
        });
    }

    #[test]
    fn late_legalizer_handles_dominating_defs_after_uses_in_layout_order() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i256) -> i256 {
    block0:
        jump block1;

    block2:
        v2.i256 = extract_value v1 0.i8;
        return v2;

    block1:
        v1.@one = insert_value undef.@one 0.i8 v0;
        jump block2;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });

        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(mload) =
                        downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
                    {
                        assert!(
                            !shape::is_supported_aggregate_ty(&ctx, *mload.ty()),
                            "aggregate mload should be gone"
                        );
                    }
                    if let Some(mstore) =
                        downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
                    {
                        assert!(
                            !shape::is_supported_aggregate_ty(&ctx, *mstore.ty()),
                            "aggregate mstore should be gone"
                        );
                    }
                }
            }
        });
    }

    #[test]
    fn late_dead_aggregate_alloca_cleanup_drops_dead_slot_trees() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f() -> i256 {
    block0:
        v0.*@pair = alloca @pair;
        v1.*i256 = gep v0 0.i64 0.i8;
        mstore v1 1.i256 i256;
        v2.*i256 = gep v0 0.i64 1.i8;
        mstore v2 2.i256 i256;
        v3.*i256 = gep v0 0.i64 0.i8;
        v4.i256 = mload v3 i256;
        return 0.i256;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(cleanup_dead_aggregate_alloca_trees(func, &ctx));
        });

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    assert!(
                        downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                        "dead aggregate alloca tree should be removed"
                    );
                }
            }
        });
    }

    #[test]
    fn late_legalizer_materializes_surviving_extract_views_without_root_slots() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i256, i256 };
type @outer = { @inner, i256 };

func private %f() -> i256 {
    block0:
        v0.*@outer = alloca @outer;
        v1.*i256 = gep v0 0.i64 0.i8 0.i8;
        mstore v1 1.i256 i256;
        v2.*i256 = gep v0 0.i64 0.i8 1.i8;
        mstore v2 2.i256 i256;
        v3.*i256 = gep v0 0.i64 1.i8;
        mstore v3 3.i256 i256;
        v4.@outer = mload v0 @outer;
        v5.@inner = extract_value v4 0.i8;
        v6.*@inner = alloca @inner;
        mstore v6 v5 @inner;
        return 0.i256;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });

        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
            let mut outer_allocas = 0;
            let mut inner_allocas = 0;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(alloca) =
                        downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst))
                    {
                        match alloca.ty().resolve_compound(&ctx) {
                            Some(CompoundType::Struct(data)) if data.name == "outer" => {
                                outer_allocas += 1;
                            }
                            Some(CompoundType::Struct(data)) if data.name == "inner" => {
                                inner_allocas += 1;
                            }
                            _ => {}
                        }
                    }
                }
            }
            assert_eq!(
                outer_allocas, 1,
                "root snapshot slot should not be materialized"
            );
            assert_eq!(
                inner_allocas, 1,
                "surviving child view should not need its own slot"
            );
        });
    }

    #[test]
    fn late_legalizer_materializes_surviving_bitcast_views_without_root_slots() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };
type @inner = { i256 };
type @nested = { @inner, i256 };

func private %f() -> i256 {
    block0:
        v0.*@pair = alloca @pair;
        v1.*i256 = gep v0 0.i64 0.i8;
        mstore v1 11.i256 i256;
        v2.*i256 = gep v0 0.i64 1.i8;
        mstore v2 22.i256 i256;
        v3.@pair = mload v0 @pair;
        v4.@nested = bitcast v3 @nested;
        v5.*@nested = alloca @nested;
        mstore v5 v4 @nested;
        return 0.i256;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });

        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
            let mut pair_allocas = 0;
            let mut nested_allocas = 0;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(alloca) =
                        downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst))
                    {
                        match alloca.ty().resolve_compound(&ctx) {
                            Some(CompoundType::Struct(data)) if data.name == "pair" => {
                                pair_allocas += 1;
                            }
                            Some(CompoundType::Struct(data)) if data.name == "nested" => {
                                nested_allocas += 1;
                            }
                            _ => {}
                        }
                    }
                }
            }
            assert_eq!(
                pair_allocas, 1,
                "root snapshot slot should not be materialized"
            );
            assert_eq!(
                nested_allocas, 1,
                "surviving bitcast view should not need its own slot"
            );
        });
    }

    #[test]
    fn late_legalizer_initializes_backedge_phi_source_slots_at_def_sites() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func public %entry() {
    block0:
        v0.*@pair = alloca @pair;
        v1.*i256 = gep v0 0.i64 0.i8;
        mstore v1 1.i256 i256;
        v2.*i256 = gep v0 0.i64 1.i8;
        mstore v2 2.i256 i256;
        v3.@pair = mload v0 @pair;
        jump block1;

    block1:
        v4.@pair = phi (v3 block0) (v10 block2);
        v5.i256 = phi (0.i256 block0) (1.i256 block2);
        v6.i1 = eq v5 0.i256;
        br v6 block2 block3;

    block2:
        v7.*@pair = alloca @pair;
        v8.*i256 = gep v7 0.i64 0.i8;
        mstore v8 10.i256 i256;
        v9.*i256 = gep v7 0.i64 1.i8;
        mstore v9 20.i256 i256;
        v10.@pair = mload v7 @pair;
        jump block1;

    block3:
        v11.i256 = extract_value v4 0.i8;
        mstore 0.i32 v11 i256;
        evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "entry");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });
        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
        });
        assert_eq!(run_contract(&module), U256::from(10));
    }

    #[test]
    fn late_legalizer_preserves_snapshot_semantics_for_raw_aggregate_extracts() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func public %entry() {
    block0:
        mstore 64.i32 12.i256 i256;
        mstore 96.i32 34.i256 i256;
        v0.@slice = mload 64.i32 @slice;
        mstore 64.i32 99.i256 i256;
        v1.i256 = extract_value v0 0.i8;
        mstore 0.i32 v1 i256;
        evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "entry");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });
        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
        });
        assert_eq!(run_contract(&module), U256::from(12));
    }

    #[test]
    fn late_legalizer_preserves_snapshot_semantics_for_nested_raw_aggregate_extracts() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i256, i256 };
type @outer = { @inner, i256 };

func public %entry() {
    block0:
        mstore 64.i32 10.i256 i256;
        mstore 96.i32 20.i256 i256;
        mstore 128.i32 30.i256 i256;
        v0.@outer = mload 64.i32 @outer;
        mstore 96.i32 99.i256 i256;
        v1.@inner = extract_value v0 0.i8;
        v2.i256 = extract_value v1 1.i8;
        mstore 0.i32 v2 i256;
        evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "entry");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });
        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
        });
        assert_eq!(run_contract(&module), U256::from(20));
    }

    #[test]
    fn late_legalizer_preserves_snapshot_semantics_through_bitcasted_raw_aggregate_extracts() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i256 };
type @pair = { i256, i256 };
type @nested = { @inner, i256 };

func public %entry() {
    block0:
        mstore 64.i32 11.i256 i256;
        mstore 96.i32 22.i256 i256;
        v0.@pair = mload 64.i32 @pair;
        v1.@nested = bitcast v0 @nested;
        mstore 64.i32 99.i256 i256;
        v2.@inner = extract_value v1 0.i8;
        v3.i256 = extract_value v2 0.i8;
        mstore 0.i32 v3 i256;
        evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "entry");
        module.func_store.modify(func_ref, |func| {
            AggregateLowerToMemoryLegalize::default().run(func, &ctx);
        });
        module.func_store.view(func_ref, |func| {
            assert_aggregate_legalized(func, &ctx);
        });
        assert_eq!(run_contract(&module), U256::from(11));
    }
}
