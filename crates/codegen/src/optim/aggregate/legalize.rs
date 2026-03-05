use cranelift_entity::SecondaryMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, Inst, InstId, Type, Value, ValueId,
    cfg::ControlFlowGraph,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, control_flow, data, downcast},
    module::ModuleCtx,
    types::CompoundType,
};

use crate::critical_edge::CriticalEdgeSplitter;

use super::shape;

#[derive(Default)]
pub struct AggregateLowerToMemoryLegalize {
    changed: bool,
    materialized_addr: SecondaryMap<ValueId, Option<ValueId>>,
}

impl AggregateLowerToMemoryLegalize {
    pub fn run(&mut self, func: &mut Function, module: &ModuleCtx) -> bool {
        self.changed = false;
        self.materialized_addr.clear();
        if func.layout.entry_block().is_none() {
            return false;
        }

        // Legalization uses `dfg.change_to_alias`, which requires up-to-date user sets.
        func.rebuild_users();

        self.validate_unsupported_boundaries(func, module);
        self.split_critical_edges_for_aggregate_phi(func, module);
        self.preallocate_materialized_slots(func, module);

        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                self.changed |= self.rewrite_inst(func, module, inst);
            }
        }

        if self.changed {
            func.rebuild_users();
        }
        assert_aggregate_legalized(func, module);
        self.changed
    }

    fn validate_unsupported_boundaries(&self, func: &Function, module: &ModuleCtx) {
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
                    if call.args().iter().any(|&arg| {
                        shape::is_supported_aggregate_ty(module, func.dfg.value_ty(arg))
                    }) {
                        panic!("aggregate call arguments are unsupported before phase 3");
                    }
                    if let Some(res) = func.dfg.inst_result(inst)
                        && shape::is_supported_aggregate_ty(module, func.dfg.value_ty(res))
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
            }
        }
    }

    fn split_critical_edges_for_aggregate_phi(&mut self, func: &mut Function, module: &ModuleCtx) {
        let has_agg_phi = func.layout.iter_block().any(|block| {
            func.layout.iter_inst(block).any(|inst| {
                downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_some()
                    && func.dfg.inst_result(inst).is_some_and(|v| {
                        shape::is_supported_aggregate_ty(module, func.dfg.value_ty(v))
                    })
            })
        });
        if !has_agg_phi {
            return;
        }

        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        CriticalEdgeSplitter::new().run(func, &mut cfg);
        self.changed = true;
    }

    fn preallocate_materialized_slots(&mut self, func: &mut Function, module: &ModuleCtx) {
        let mut aggregate_results: Vec<(ValueId, Type)> = Vec::new();
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                let Some(result) = func.dfg.inst_result(inst) else {
                    continue;
                };
                let ty = func.dfg.value_ty(result);
                if !shape::is_supported_aggregate_ty(module, ty) {
                    continue;
                }
                aggregate_results.push((result, ty));
            }
        }

        for (result, ty) in aggregate_results {
            if self.materialized_addr[result].is_some() {
                continue;
            }
            let addr = self.create_temp_alloca(func, ty);
            self.materialized_addr[result] = Some(addr);
        }
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
        &self,
        module: &ModuleCtx,
        agg_ty: Type,
        ctx: &str,
    ) -> shape::AggregateLeaf {
        let shape = self.shape_or_panic(module, agg_ty);
        let [leaf] = shape.leaves.as_slice() else {
            panic!(
                "{ctx} bitcast requires single-leaf aggregate (got {})",
                shape.leaves.len()
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

        // Aggregate -> aggregate: same bits, so share backing storage.
        if from_is_agg && to_is_agg {
            if is_explicit_undef(func, from) {
                let undef = func.dfg.make_undef_value(to_ty);
                self.alias_and_remove(func, inst, result, undef);
                return true;
            }

            let src_ptr = self.materialized_ptr(func, from, module);
            self.materialized_addr[result] = Some(src_ptr);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return true;
        }

        // Scalar -> aggregate: only legal for single-word aggregates on EVM.
        if to_is_agg {
            let leaf = self.single_word_leaf(module, to_ty, "scalar-to-aggregate");

            let dst_ptr = self.materialized_addr[result]
                .unwrap_or_else(|| self.create_temp_alloca(func, to_ty));
            self.materialized_addr[result] = Some(dst_ptr);

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
            let Some(CompoundType::Array { elem, .. }) = result_ty.resolve_compound(module) else {
                panic!("insert_value dynamic index is only supported for arrays");
            };
            let elem_ptr =
                self.emit_gep_array_element_ptr(func, &mut builder, dst_ptr, idx_value, elem);
            if shape::is_supported_aggregate_ty(module, elem) {
                self.emit_copy_aggregate_value_to_ptr(
                    func,
                    module,
                    &mut builder,
                    *insert.value(),
                    elem_ptr,
                    elem,
                );
            } else {
                self.emit_store_scalar_to_path(
                    func,
                    &mut builder,
                    elem_ptr,
                    &[],
                    *insert.value(),
                    elem,
                );
            }
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
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
            let Some(CompoundType::Array { elem, .. }) = agg_ty.resolve_compound(module) else {
                panic!("extract_value dynamic index is only supported for arrays");
            };

            if shape::is_supported_aggregate_ty(module, result_ty) {
                let dst_ptr = self.materialized_ptr(func, result, module);
                let mut builder = BeforeCursor::new_before_inst(func, inst);
                if is_explicit_undef(func, *extract.dest()) {
                    let undef = func.dfg.make_undef_value(elem);
                    self.emit_copy_aggregate_value_to_ptr(
                        func,
                        module,
                        &mut builder,
                        undef,
                        dst_ptr,
                        elem,
                    );
                } else {
                    let src_ptr = self.materialized_ptr(func, *extract.dest(), module);
                    let elem_ptr = self.emit_gep_array_element_ptr(
                        func,
                        &mut builder,
                        src_ptr,
                        idx_value,
                        elem,
                    );
                    self.emit_copy_aggregate_ptr_to_ptr(
                        func,
                        module,
                        &mut builder,
                        elem_ptr,
                        dst_ptr,
                        elem,
                    );
                }
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                return;
            }

            if is_explicit_undef(func, *extract.dest()) {
                let undef = func.dfg.make_undef_value(result_ty);
                self.alias_and_remove(func, inst, result, undef);
                return;
            }

            let src_ptr = self.materialized_ptr(func, *extract.dest(), module);
            let mut builder = BeforeCursor::new_before_inst(func, inst);
            let elem_ptr =
                self.emit_gep_array_element_ptr(func, &mut builder, src_ptr, idx_value, elem);
            let loaded =
                self.emit_load_scalar_from_path(func, &mut builder, elem_ptr, &[], result_ty);
            self.alias_and_remove(func, inst, result, loaded);
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
        let dst_ptr = self.materialized_ptr(func, result, module);

        let mut builder = BeforeCursor::new_before_inst(func, inst);
        self.emit_copy_aggregate_ptr_to_ptr(
            func,
            module,
            &mut builder,
            *mload.addr(),
            dst_ptr,
            agg_ty,
        );

        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn rewrite_aggregate_mstore(&mut self, func: &mut Function, module: &ModuleCtx, inst: InstId) {
        let mstore = *downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
            .expect("expected mstore");
        let agg_ty = *mstore.ty();
        let mut builder = BeforeCursor::new_before_inst(func, inst);
        self.emit_copy_aggregate_value_to_ptr(
            func,
            module,
            &mut builder,
            *mstore.value(),
            *mstore.addr(),
            agg_ty,
        );
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn shape_or_panic(&self, module: &ModuleCtx, ty: Type) -> shape::AggregateShape {
        shape::aggregate_shape(module, ty)
            .unwrap_or_else(|| panic!("unsupported aggregate type in legalizer: {ty:?}"))
    }

    fn materialized_ptr(&self, func: &Function, value: ValueId, module: &ModuleCtx) -> ValueId {
        if is_explicit_undef(func, value) {
            panic!("explicit undef aggregate has no materialized pointer");
        }
        let ty = func.dfg.value_ty(value);
        if !shape::is_supported_aggregate_ty(module, ty) {
            panic!("expected aggregate value, got {ty:?}");
        }
        self.materialized_addr[value].unwrap_or_else(|| {
            panic!(
                "aggregate value missing materialized slot v{}",
                value.as_u32()
            )
        })
    }

    fn emit_copy_aggregate_value_to_ptr(
        &self,
        func: &mut Function,
        module: &ModuleCtx,
        builder: &mut BeforeCursor,
        value: ValueId,
        dst_ptr: ValueId,
        agg_ty: Type,
    ) {
        let shape = self.shape_or_panic(module, agg_ty);
        if is_explicit_undef(func, value) {
            for leaf in &shape.leaves {
                if leaf.size_bytes == 0 {
                    continue;
                }
                let undef = func.dfg.make_undef_value(leaf.ty);
                self.emit_store_scalar_to_path(func, builder, dst_ptr, &leaf.path, undef, leaf.ty);
            }
            return;
        }

        let src_ptr = self.materialized_ptr(func, value, module);
        self.emit_copy_aggregate_ptr_to_ptr(func, module, builder, src_ptr, dst_ptr, agg_ty);
    }

    fn emit_copy_aggregate_ptr_to_ptr(
        &self,
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
        debug_assert_eq!(src_leaves.len(), dst_leaves.len());
        for (src_leaf, dst_leaf) in src_leaves.iter().zip(dst_leaves) {
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
            self.emit_store_scalar_to_path(
                func,
                builder,
                dst_ptr,
                &dst_leaf.path,
                loaded,
                dst_leaf.ty,
            );
        }
    }

    fn emit_copy_subaggregate_value_to_slice(
        &self,
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
            for i in 0..dst.slice.leaf_count {
                let dst_leaf = &dst_shape.leaves[dst.slice.first_leaf + i];
                if dst_leaf.size_bytes == 0 {
                    continue;
                }
                let undef = func.dfg.make_undef_value(dst_leaf.ty);
                self.emit_store_scalar_to_path(
                    func,
                    builder,
                    dst.ptr,
                    &dst_leaf.path,
                    undef,
                    dst_leaf.ty,
                );
            }
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
        &self,
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
