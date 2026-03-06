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
    cfg_edit::CleanupMode, critical_edge::CriticalEdgeSplitter, optim::cfg_cleanup::CfgCleanup,
};

use super::{cleanup::remove_dead_pure_insts_with_current_users, shape};

#[derive(Default)]
pub struct AggregateLowerToMemoryLegalize {
    changed: bool,
    materialized_addr: SecondaryMap<ValueId, Option<ValueId>>,
    materialized_slots: Vec<ValueId>,
    shape_cache: FxHashMap<Type, shape::AggregateShape>,
    runtime_leaf_cache: FxHashMap<Type, shape::RuntimeLeaves>,
    slot_tree_insts: Vec<InstId>,
    slot_tree_queue: Vec<ValueId>,
    slot_tree_seen_insts: FxHashSet<InstId>,
    slot_tree_seen_values: FxHashSet<ValueId>,
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
        self.shape_cache.clear();
        self.runtime_leaf_cache.clear();
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
        let removed_slots = self.remove_dead_materialized_slots(func);
        let removed_pure = remove_dead_pure_insts_with_current_users(func);
        let mut changed = removed_slots || removed_pure;

        if split_edges {
            let cleaned_cfg = CfgCleanup::new(CleanupMode::Strict).run(func);
            changed |= cleaned_cfg;
            if cleaned_cfg {
                changed |= self.remove_dead_materialized_slots(func);
                changed |= remove_dead_pure_insts_with_current_users(func);
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
        let ptr = func.dfg.make_value(Value::Inst { inst, ty: ptr_ty });
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

        let from_size = module.size_of_unchecked(from_ty);
        let to_size = module.size_of_unchecked(to_ty);
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

            let src_ptr = self.materialized_ptr(func, from, module);
            let dst_ptr = self.materialized_ptr(func, result, module);
            let (src_leaves, dst_leaves) =
                self.aggregate_bitcast_leaf_layout(module, from_ty, to_ty);
            let mut builder = BeforeCursor::new_before_inst(func, inst);
            self.emit_copy_leaf_slices_ptr_to_ptr(
                func,
                &mut builder,
                src_ptr,
                &src_leaves,
                dst_ptr,
                &dst_leaves,
            );
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
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
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return true;
        }

        // Aggregate -> scalar: only legal for single-word aggregates on EVM.
        let leaf = self.single_word_leaf(module, from_ty, "aggregate-to-scalar");
        if is_explicit_undef(func, from) {
            let undef = func.dfg.make_undef_value(to_ty);
            self.alias_and_remove(func, inst, result, undef);
            return true;
        }

        let src_ptr = self.materialized_ptr(func, from, module);
        let mut builder = BeforeCursor::new_before_inst(func, inst);
        let loaded =
            self.emit_load_scalar_from_path(func, &mut builder, src_ptr, &leaf.path, leaf.ty);
        let replacement = if leaf.ty == to_ty {
            loaded
        } else {
            builder.insert_with_result(
                func,
                cast::Bitcast::new_unchecked(func.inst_set(), loaded, to_ty),
                to_ty,
            )
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

        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
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
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
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
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        if is_explicit_undef(func, *extract.dest()) {
            let undef = func.dfg.make_undef_value(result_ty);
            self.alias_and_remove(func, inst, result, undef);
            return;
        }

        let src_ptr = self.materialized_ptr(func, *extract.dest(), module);
        let src_shape = self.shape_or_panic(module, agg_ty);
        let src_leaf = &src_shape.leaves[slice.first_leaf];
        let mut builder = BeforeCursor::new_before_inst(func, inst);
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
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        if is_explicit_undef(func, src_value) {
            let undef = func.dfg.make_undef_value(result_ty);
            self.alias_and_remove(func, inst, result, undef);
            return;
        }

        let src_ptr = self.materialized_ptr(func, src_value, module);
        let mut builder = BeforeCursor::new_before_inst(func, inst);
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

        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn rewrite_aggregate_mload(&mut self, func: &mut Function, module: &ModuleCtx, inst: InstId) {
        let mload = *downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
            .expect("expected mload");
        let result = func
            .dfg
            .inst_result(inst)
            .expect("aggregate mload must have result");
        let agg_ty = *mload.ty();
        let users: Vec<_> = func.dfg.users(result).copied().collect();
        for user in users {
            if !func.layout.is_inst_inserted(user) {
                continue;
            }
            let Some(extract) =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(user))
            else {
                continue;
            };
            let extract = extract.clone();
            if *extract.dest() != result {
                continue;
            }
            let Some(extract_result) = func.dfg.inst_result(user) else {
                continue;
            };
            if shape::is_supported_aggregate_ty(module, func.dfg.value_ty(extract_result)) {
                continue;
            }
            self.rewrite_scalar_extract_from_aggregate_addr(
                func,
                module,
                user,
                &extract,
                *mload.addr(),
                agg_ty,
            );
        }

        if !func
            .dfg
            .users(result)
            .copied()
            .any(|user| func.layout.is_inst_inserted(user))
        {
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        let mut builder = BeforeCursor::new_before_inst(func, inst);
        let src_ptr = self.aggregate_addr_as_typed_ptr(func, &mut builder, *mload.addr(), agg_ty);
        let dst_ptr = self.materialized_ptr(func, result, module);
        self.emit_copy_aggregate_ptr_to_ptr(func, module, &mut builder, src_ptr, dst_ptr, agg_ty);

        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
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
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn shape_or_panic(&mut self, module: &ModuleCtx, ty: Type) -> shape::AggregateShape {
        if let Some(shape) = self.shape_cache.get(&ty) {
            return shape.clone();
        }

        let shape = shape::aggregate_shape(module, ty)
            .unwrap_or_else(|| panic!("unsupported aggregate type in legalizer: {ty:?}"));
        self.shape_cache.insert(ty, shape.clone());
        shape
    }

    fn runtime_leaves_or_panic(&mut self, module: &ModuleCtx, ty: Type) -> shape::RuntimeLeaves {
        if let Some(leaves) = self.runtime_leaf_cache.get(&ty) {
            return leaves.clone();
        }

        let leaves: shape::RuntimeLeaves = self
            .shape_or_panic(module, ty)
            .leaves
            .into_iter()
            .filter(|leaf| leaf.size_bytes != 0)
            .collect();
        self.runtime_leaf_cache.insert(ty, leaves.clone());
        leaves
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

    fn rewrite_scalar_extract_from_aggregate_addr(
        &mut self,
        func: &mut Function,
        module: &ModuleCtx,
        inst: InstId,
        extract: &data::ExtractValue,
        src_addr: ValueId,
        src_agg_ty: Type,
    ) {
        let result = func
            .dfg
            .inst_result(inst)
            .expect("extract_value must have result");
        let result_ty = func.dfg.value_ty(result);
        let mut builder = BeforeCursor::new_before_inst(func, inst);
        let src_ptr = self.aggregate_addr_as_typed_ptr(func, &mut builder, src_addr, src_agg_ty);

        let replacement = if let Some(idx) = shape::const_u32(&func.dfg, *extract.idx()) {
            let slice = shape::aggregate_slice_for_index(module, src_agg_ty, idx)
                .unwrap_or_else(|| panic!("extract_value index out of bounds"));
            let src_shape = self.shape_or_panic(module, src_agg_ty);
            let src_leaf = &src_shape.leaves[slice.first_leaf];
            self.emit_load_scalar_from_path(
                func,
                &mut builder,
                src_ptr,
                &src_leaf.path,
                src_leaf.ty,
            )
        } else {
            let elem = self.array_elem_ty_or_panic(module, src_agg_ty, "extract_value");
            if elem != result_ty {
                panic!("extract_value result type mismatch for dynamic array index");
            }
            let elem_ptr =
                self.emit_gep_array_element_ptr(func, &mut builder, src_ptr, *extract.idx(), elem);
            self.emit_load_scalar_from_path(func, &mut builder, elem_ptr, &[], result_ty)
        };
        if func.dfg.value_ty(replacement) != result_ty {
            panic!("extract_value type mismatch after aggregate load legalization");
        }
        self.alias_and_remove(func, inst, result, replacement);
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
        let value = func.dfg.make_value(Value::Inst { inst, ty });
        self.cursor.attach_result(func, inst, value);
        value
    }
}

fn scan_aggregate_legalize_needs(func: &Function, module: &ModuleCtx) -> AggregateLegalizeScan {
    let mut scan = AggregateLegalizeScan::default();

    for &arg in &func.arg_values {
        let ty = func.dfg.value_ty(arg);
        if shape::is_supported_aggregate_ty(module, ty) {
            panic!("aggregate function arguments are unsupported before phase 3");
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
                    panic!("aggregate call arguments are unsupported before phase 3");
                }
                if let Some(result) = func.dfg.inst_result(inst)
                    && shape::is_supported_aggregate_ty(module, func.dfg.value_ty(result))
                {
                    panic!("aggregate call results are unsupported before phase 3");
                }
            }

            if let Some(ret) =
                downcast::<&control_flow::Return>(func.inst_set(), func.dfg.inst(inst))
                && let Some(arg) = ret.arg()
                && shape::is_supported_aggregate_ty(module, func.dfg.value_ty(*arg))
            {
                panic!("aggregate return values are unsupported before phase 3");
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::{EvmBackend, PushWidthPolicy},
        object::{CompileOptions, compile_all_objects},
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
    fn late_legalizer_handles_raw_aggregate_addresses_and_scalar_extracts_without_temps() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func public %entry(v0.i256, v1.*i8) -> i256 {
    block0:
        v2.@slice = mload v0 @slice;
        v3.i256 = extract_value v2 1.i8;
        v4.@slice = mload v1 @slice;
        v5.i256 = extract_value v4 0.i8;
        v6.i256 = add v3 v5;
        return v6;
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
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    assert!(
                        downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                        "direct scalar extracts from aggregate loads should not materialize temps"
                    );
                }
            }
        });

        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        };
        compile_all_objects(&module, &test_backend(), &opts).expect("compile should succeed");
    }
}
