use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, I256, Immediate, InstId, Type, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, control_flow, data, downcast},
    module::FuncRef,
};

use super::{
    LocalObjectArgInfo, LocalObjectArgMap, ObjectEffectSummaryMap, SliceSet,
    cleanup::DeadPureInstCleanup,
    collect_root_provenance,
    object_tracking::{
        ObjectSlice, TrackedObject, collect_root_slices, collect_tracked_objects,
        enum_tag_object_slice, enum_variant_field_object_slice, object_slice_overlaps_effect,
        slice_is_covered_by, slices_overlap, whole_root_slice_for_value,
    },
    provenance::{MayProvenance, MayRootSet},
    reconstruct::AggregateValueReconstructor,
    shape,
};

type AvailableMap = FxHashMap<ObjectSlice, ValueId>;

struct CallCaptureEndpoint<'a> {
    tracked: Option<TrackedObject>,
    roots: MayRootSet<'a>,
    slice: shape::AggregateSlice,
}

#[derive(Default)]
pub struct ObjectLoadStore {
    changed: bool,
    layout_cache: shape::AggregateLayoutCache,
    dead_pure_cleanup: DeadPureInstCleanup,
}

impl ObjectLoadStore {
    pub fn run(&mut self, func: &mut Function) -> bool {
        self.run_with_module_facts(func, None, None)
    }

    // `local_object_args` must be computed before entering `func_store.modify(...)`.
    pub(crate) fn run_for_func(
        &mut self,
        func_ref: FuncRef,
        func: &mut Function,
        local_object_args: &LocalObjectArgMap,
        object_effects: &ObjectEffectSummaryMap,
    ) -> bool {
        self.run_with_module_facts(func, local_object_args.get(&func_ref), Some(object_effects))
    }

    fn run_with_module_facts(
        &mut self,
        func: &mut Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
        object_effects: Option<&ObjectEffectSummaryMap>,
    ) -> bool {
        self.changed = false;
        self.layout_cache.clear();

        loop {
            func.rebuild_users();
            let root_slices = collect_root_slices(func, local_object_args, &mut self.layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut self.layout_cache,
                object_effects,
            );
            let tracked =
                collect_tracked_objects(func, provenance.complete(), &mut self.layout_cache);
            let may = provenance.may();
            let live_out_roots = self.collect_live_out_roots(&tracked, func, local_object_args);

            let mut iter_changed = self.run_forward(func, &tracked, may, object_effects);
            iter_changed |= self.run_backward(func, &tracked, may, &live_out_roots, object_effects);

            if iter_changed {
                func.rebuild_users();
            }
            iter_changed |= self.cleanup_dead_object_artifacts(func);
            if iter_changed {
                func.rebuild_users();
            }
            iter_changed |= self.dead_pure_cleanup.run_with_current_users(func);
            self.changed |= iter_changed;
            if !iter_changed {
                return self.changed;
            }
        }
    }

    fn run_forward(
        &mut self,
        func: &mut Function,
        tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
        provenance: MayProvenance<'_>,
        object_effects: Option<&ObjectEffectSummaryMap>,
    ) -> bool {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let reachable = cfg.reachable_blocks();
        let order: Vec<_> = cfg
            .post_order()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        let mut in_states = SecondaryMap::<BlockId, AvailableMap>::new();
        let mut out_states = SecondaryMap::<BlockId, AvailableMap>::new();
        let mut dataflow_changed = true;
        let mut changed = false;

        while dataflow_changed {
            dataflow_changed = false;
            for &block in &order {
                if !reachable[block] {
                    continue;
                }

                let in_state = meet_forward(
                    cfg.preds_of(block)
                        .copied()
                        .filter(|pred| reachable[*pred])
                        .map(|pred| out_states[pred].clone()),
                );
                if in_state != in_states[block] {
                    in_states[block] = in_state.clone();
                    dataflow_changed = true;
                }

                let mut available = in_state;
                for inst in func.layout.iter_inst(block).collect::<Vec<_>>() {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    changed |= self.transfer_forward(
                        func,
                        inst,
                        tracked,
                        provenance,
                        &mut available,
                        object_effects,
                    );
                }

                if available != out_states[block] {
                    out_states[block] = available;
                    dataflow_changed = true;
                }
            }
        }

        changed
    }

    fn replacement_for_load(
        &mut self,
        func: &mut Function,
        inst: InstId,
        slice: ObjectSlice,
        available: &AvailableMap,
    ) -> Option<ValueId> {
        for (&available_slice, &value) in available {
            if available_slice.root != slice.root || !slice_is_covered_by(available_slice, slice) {
                continue;
            }
            if available_slice == slice && func.dfg.value_ty(value) == slice.ty {
                return Some(value);
            }

            let source_slice = shape::aggregate_slice_for_leaf_range(
                func.ctx(),
                available_slice.ty,
                slice.first_leaf - available_slice.first_leaf,
                slice.leaf_count,
            )?;
            if let Some(rebuilt) = AggregateValueReconstructor::new(&mut self.layout_cache)
                .rebuild_slice(
                    func,
                    inst,
                    value,
                    available_slice.ty,
                    source_slice,
                    slice.ty,
                )
            {
                return Some(rebuilt);
            }
        }

        None
    }

    #[allow(clippy::too_many_arguments)]
    fn transfer_forward(
        &mut self,
        func: &mut Function,
        inst: InstId,
        tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
        provenance: MayProvenance<'_>,
        available: &mut AvailableMap,
        object_effects: Option<&ObjectEffectSummaryMap>,
    ) -> bool {
        if let Some(obj_load) = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)) {
            kill_observed_available(func, inst, provenance, available, &[*obj_load.object()]);
            if let Some(slice) = tracked[*obj_load.object()]
                .as_ref()
                .copied()
                .and_then(TrackedObject::exact)
                && let Some(replacement) = self.replacement_for_load(func, inst, slice, available)
                && let Some(result) = func.dfg.inst_result(inst)
            {
                func.dfg.change_to_alias(result, replacement);
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                return true;
            }
            return false;
        }

        if let Some(enum_get_tag) =
            downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst))
        {
            kill_observed_available(func, inst, provenance, available, &[*enum_get_tag.object()]);
            if let Some(slice) = tracked[*enum_get_tag.object()]
                .as_ref()
                .copied()
                .and_then(TrackedObject::exact)
                .and_then(|slice| enum_tag_object_slice(func.ctx(), slice))
                && let Some(replacement) = self.replacement_for_load(func, inst, slice, available)
                && let Some(result) = func.dfg.inst_result(inst)
            {
                func.dfg.change_to_alias(result, replacement);
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                return true;
            }
            return false;
        }

        if let Some(enum_assert_ref) =
            downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst))
            && tracked[*enum_assert_ref.object()].is_some()
        {
            return false;
        }

        if let Some(obj_store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)) {
            kill_observed_available(func, inst, provenance, available, &[*obj_store.object()]);

            let Some(tracked_object) = tracked[*obj_store.object()].as_ref().copied() else {
                kill_possible_roots_available(available, provenance.may_roots(*obj_store.object()));
                return false;
            };
            let Some(slice) = tracked_object.exact() else {
                kill_possible_roots_available(available, provenance.may_roots(*obj_store.object()));
                return false;
            };
            if available.get(&slice) == Some(obj_store.value()) {
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                return true;
            }
            kill_overlapping_available(available, slice);
            available.insert(slice, *obj_store.value());
            return false;
        }

        if let Some(enum_set_tag) =
            downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst))
        {
            kill_observed_available(func, inst, provenance, available, &[*enum_set_tag.object()]);
            let Some(tracked_object) = tracked[*enum_set_tag.object()].as_ref().copied() else {
                kill_possible_roots_available(
                    available,
                    provenance.may_roots(*enum_set_tag.object()),
                );
                return false;
            };
            let Some(slice) = tracked_object
                .exact()
                .and_then(|slice| enum_tag_object_slice(func.ctx(), slice))
            else {
                kill_possible_roots_available(
                    available,
                    provenance.may_roots(*enum_set_tag.object()),
                );
                return false;
            };
            let tag = func
                .dfg
                .make_imm_value(enum_variant_tag_imm(*enum_set_tag.variant(), slice.ty));
            if available.get(&slice) == Some(&tag) {
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                return true;
            }
            kill_overlapping_available(available, slice);
            available.insert(slice, tag);
            return false;
        }

        if let Some(enum_write_variant) =
            downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            kill_observed_available(
                func,
                inst,
                provenance,
                available,
                &[*enum_write_variant.object()],
            );
            let Some(tracked_object) = tracked[*enum_write_variant.object()].as_ref().copied()
            else {
                kill_possible_roots_available(
                    available,
                    provenance.may_roots(*enum_write_variant.object()),
                );
                return false;
            };
            let Some(base_slice) = tracked_object.exact() else {
                kill_possible_roots_available(
                    available,
                    provenance.may_roots(*enum_write_variant.object()),
                );
                return false;
            };
            for (field_idx, &value) in enum_write_variant.values().iter().enumerate() {
                let Some(field_idx) = u32::try_from(field_idx).ok() else {
                    continue;
                };
                let Some(field_slice) = enum_variant_field_object_slice(
                    func.ctx(),
                    base_slice,
                    *enum_write_variant.variant(),
                    field_idx,
                ) else {
                    continue;
                };
                kill_overlapping_available(available, field_slice);
                available.insert(field_slice, value);
            }
            let Some(tag_slice) = enum_tag_object_slice(func.ctx(), base_slice) else {
                return false;
            };
            kill_overlapping_available(available, tag_slice);
            available.insert(
                tag_slice,
                func.dfg.make_imm_value(enum_variant_tag_imm(
                    *enum_write_variant.variant(),
                    tag_slice.ty,
                )),
            );
            return false;
        }

        if handle_call_forward(func, inst, tracked, provenance, available, object_effects) {
            return false;
        }

        kill_observed_available(func, inst, provenance, available, &[]);
        false
    }

    fn run_backward(
        &mut self,
        func: &mut Function,
        tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
        provenance: MayProvenance<'_>,
        live_out_roots: &FxHashMap<ValueId, usize>,
        object_effects: Option<&ObjectEffectSummaryMap>,
    ) -> bool {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let reachable = cfg.reachable_blocks();
        let order: Vec<_> = cfg.post_order().collect();
        let mut in_states = SecondaryMap::<BlockId, FxHashMap<ValueId, FxHashSet<usize>>>::new();
        let mut out_states = SecondaryMap::<BlockId, FxHashMap<ValueId, FxHashSet<usize>>>::new();
        let mut changed = false;

        let mut dataflow_changed = true;
        while dataflow_changed {
            dataflow_changed = false;
            for &block in &order {
                if !reachable[block] {
                    continue;
                }

                let mut out_state = meet_live(
                    cfg.succs_of(block)
                        .copied()
                        .filter(|succ| reachable[*succ])
                        .map(|succ| in_states[succ].clone()),
                );
                if ends_with_return(func, block) {
                    for (&root, &total_leaves) in live_out_roots {
                        mark_root_live(&mut out_state, root, total_leaves);
                    }
                }
                if out_state != out_states[block] {
                    out_states[block] = out_state.clone();
                    dataflow_changed = true;
                }

                let mut live = out_state;
                for inst in func
                    .layout
                    .iter_inst(block)
                    .collect::<Vec<_>>()
                    .into_iter()
                    .rev()
                {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    transfer_backward_live(
                        func,
                        inst,
                        tracked,
                        provenance,
                        &mut live,
                        object_effects,
                    );
                }

                if live != in_states[block] {
                    in_states[block] = live;
                    dataflow_changed = true;
                }
            }
        }

        for &block in &order {
            if !reachable[block] {
                continue;
            }

            let mut live = out_states[block].clone();
            for inst in func
                .layout
                .iter_inst(block)
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
            {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                let removed = try_remove_dead_store(func, inst, tracked, provenance, &live);
                changed |= removed;
                if removed {
                    continue;
                }
                transfer_backward_live(func, inst, tracked, provenance, &mut live, object_effects);
            }
        }

        changed
    }

    fn cleanup_dead_object_artifacts(&mut self, func: &mut Function) -> bool {
        let mut changed = false;

        loop {
            let mut iter_changed = false;
            for block in func.layout.iter_block().collect::<Vec<_>>() {
                for inst in func.layout.iter_inst(block).collect::<Vec<_>>() {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    let removable =
                        downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)).is_some()
                            || downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst))
                                .is_some()
                            || downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst))
                                .is_some()
                            || downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                                .is_some();
                    if !removable {
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
                    iter_changed = true;
                }
            }
            changed |= iter_changed;
            if !iter_changed {
                return changed;
            }
            func.rebuild_users();
        }
    }

    fn collect_live_out_roots(
        &self,
        tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
        func: &Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
    ) -> FxHashMap<ValueId, usize> {
        let mut live_out_roots = FxHashMap::default();
        let Some(local_object_args) = local_object_args else {
            return live_out_roots;
        };

        for &idx in local_object_args.keys() {
            let Some(&root) = func.arg_values.get(idx) else {
                continue;
            };
            let Some(tracked_root) = tracked[root].as_ref().copied() else {
                continue;
            };
            live_out_roots.insert(root, tracked_root.total_leaves());
        }

        live_out_roots
    }
}

fn meet_forward(states: impl Iterator<Item = AvailableMap>) -> AvailableMap {
    let states: Vec<_> = states.collect();
    let Some(mut out) = states.first().cloned() else {
        return AvailableMap::default();
    };

    out.retain(|slice, value| {
        states[1..]
            .iter()
            .all(|state| state.get(slice) == Some(value))
    });
    out
}

fn observed_roots(
    func: &Function,
    inst: InstId,
    provenance: MayProvenance<'_>,
    skip: &[ValueId],
) -> (Vec<ValueId>, bool) {
    if downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_some()
    {
        return (Vec::new(), false);
    }

    let skipped: FxHashSet<_> = skip.iter().copied().collect();
    let mut roots = FxHashSet::default();
    let mut observed_unknown = false;
    for value in func.dfg.inst(inst).collect_values() {
        if skipped.contains(&value) {
            continue;
        }
        let root_set = provenance.may_roots(value);
        observed_unknown |= root_set.has_unknown();
        for root in root_set.observed().iter() {
            roots.insert(root.value());
        }
    }
    (roots.into_iter().collect(), observed_unknown)
}

fn kill_possible_roots_available(available: &mut AvailableMap, possible_roots: MayRootSet<'_>) {
    let Some(possible_roots) = possible_roots.exhaustive_known_roots() else {
        available.clear();
        return;
    };
    for root in possible_roots.iter() {
        kill_root_available(available, root.value());
    }
}

fn kill_observed_available(
    func: &Function,
    inst: InstId,
    provenance: MayProvenance<'_>,
    available: &mut AvailableMap,
    skip: &[ValueId],
) {
    let (roots, observed_unknown) = observed_roots(func, inst, provenance, skip);
    if observed_unknown {
        available.clear();
        return;
    }
    for root in roots {
        kill_root_available(available, root);
    }
}

fn mark_all_tracked_roots_live(
    func: &Function,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
) {
    for value in func.dfg.value_ids() {
        if let Some(root_slice) = whole_root_slice_for_value(tracked, value) {
            mark_root_live(live, root_slice.root, root_slice.total_leaves);
        }
    }
}

fn handle_call_forward(
    func: &Function,
    inst: InstId,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    provenance: MayProvenance<'_>,
    available: &mut AvailableMap,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> bool {
    let Some(call) = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)) else {
        return false;
    };
    let Some(summary) = object_effects.and_then(|effects| effects.get(call.callee())) else {
        kill_observed_available(func, inst, provenance, available, &[]);
        return true;
    };

    for (idx, &arg) in call.args().iter().enumerate() {
        let Some(effect) = summary.arg_effects.get(idx) else {
            continue;
        };
        apply_call_forward_effect(
            available,
            tracked[arg],
            provenance.may_roots(arg),
            &effect.writes,
            effect.needs_unknown_object_barrier(),
        );
    }
    true
}

fn apply_call_forward_effect(
    available: &mut AvailableMap,
    tracked_object: Option<TrackedObject>,
    possible_roots: MayRootSet<'_>,
    writes: &SliceSet,
    escapes: bool,
) {
    if escapes {
        kill_possible_roots_available(available, possible_roots);
        return;
    }
    if writes.is_empty() {
        return;
    }
    let Some(tracked_object) = tracked_object else {
        kill_possible_roots_available(available, possible_roots);
        return;
    };
    let Some(base_slice) = tracked_object.exact() else {
        kill_possible_roots_available(available, possible_roots);
        return;
    };
    kill_available_slice_set(available, base_slice, writes);
}

fn kill_available_slice_set(
    available: &mut AvailableMap,
    base_slice: ObjectSlice,
    slices: &SliceSet,
) {
    if slices.is_empty() {
        return;
    }
    if slices.is_whole_root() || base_slice.leaf_count != slices.total_leaves() {
        kill_overlapping_available(available, base_slice);
        return;
    }
    let Some(leaves) = slices.exact_leaves() else {
        kill_overlapping_available(available, base_slice);
        return;
    };
    available.retain(|slice, _| !object_slice_overlaps_effect(*slice, base_slice, leaves));
}

fn handle_call_backward(
    func: &Function,
    inst: InstId,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    provenance: MayProvenance<'_>,
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> bool {
    let Some(call) = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)) else {
        return false;
    };
    let Some(summary) = object_effects.and_then(|effects| effects.get(call.callee())) else {
        let (roots, observed_unknown) = observed_roots(func, inst, provenance, &[]);
        if observed_unknown {
            mark_all_tracked_roots_live(func, tracked, live);
        } else {
            for root in roots {
                mark_root_live(live, root, root_total_leaves(tracked, root));
            }
        }
        return true;
    };
    let call_result = single_result_value(func, inst);

    for capture in &summary.captures {
        let Some(&src_arg) = call.args().get(capture.src_arg) else {
            continue;
        };
        let dst = match capture.dst {
            super::object_effects::ObjectCaptureDestination::Arg { index, slice } => {
                let Some(&dst_arg) = call.args().get(index) else {
                    continue;
                };
                CallCaptureEndpoint {
                    tracked: tracked[dst_arg],
                    roots: provenance.may_roots(dst_arg),
                    slice,
                }
            }
            super::object_effects::ObjectCaptureDestination::Return { slice } => {
                let Some(result) = call_result else {
                    continue;
                };
                CallCaptureEndpoint {
                    tracked: tracked[result],
                    roots: provenance.may_roots(result),
                    slice,
                }
            }
        };
        let src = CallCaptureEndpoint {
            tracked: tracked[src_arg],
            roots: provenance.may_roots(src_arg),
            slice: capture.src_slice,
        };
        if dst.roots.has_unknown() || src.roots.has_unknown() {
            mark_all_tracked_roots_live(func, tracked, live);
            continue;
        }
        apply_call_backward_capture(live, tracked, &dst, &src);
    }

    for (idx, &arg) in call.args().iter().enumerate() {
        let Some(effect) = summary.arg_effects.get(idx) else {
            continue;
        };
        apply_call_backward_effect(
            func,
            live,
            tracked,
            tracked[arg],
            provenance.may_roots(arg),
            &effect.reads,
            &effect.writes,
            effect.needs_unknown_object_barrier(),
        );
    }
    true
}

fn apply_call_backward_capture(
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    dst: &CallCaptureEndpoint<'_>,
    src: &CallCaptureEndpoint<'_>,
) {
    if !capture_destination_has_live(live, dst) {
        return;
    }

    if let Some(slice) = src
        .tracked
        .and_then(|tracked| map_capture_slice(tracked, src.slice))
    {
        mark_live(live, TrackedObject::Exact(slice));
        return;
    }

    for root in src.roots.observed().iter() {
        mark_root_live(live, root.value(), root_total_leaves(tracked, root.value()));
    }
}

fn capture_destination_has_live(
    live: &FxHashMap<ValueId, FxHashSet<usize>>,
    dst: &CallCaptureEndpoint<'_>,
) -> bool {
    if dst.roots.has_unknown() {
        return true;
    }
    let Some(tracked) = dst.tracked else {
        return dst
            .roots
            .observed()
            .iter()
            .any(|root| root_has_live(live, root.value()));
    };
    if let Some(slice) = map_capture_slice(tracked, dst.slice) {
        return slice_has_live_leaf(live, slice);
    }
    tracked.exact().is_none()
        && dst
            .roots
            .observed()
            .iter()
            .any(|root| root_has_live(live, root.value()))
}

#[allow(clippy::too_many_arguments)]
fn apply_call_backward_effect(
    func: &Function,
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    tracked_object: Option<TrackedObject>,
    possible_roots: MayRootSet<'_>,
    reads: &SliceSet,
    writes: &SliceSet,
    escapes: bool,
) {
    if escapes {
        mark_live_may_roots(func, live, tracked, possible_roots);
        return;
    }
    let Some(tracked_object) = tracked_object else {
        if !reads.is_empty() || !writes.is_empty() {
            mark_live_may_roots(func, live, tracked, possible_roots);
        }
        return;
    };
    let Some(base_slice) = tracked_object.exact() else {
        if !reads.is_empty() || !writes.is_empty() {
            mark_live_may_roots(func, live, tracked, possible_roots);
        }
        return;
    };
    clear_live_slice_set(live, base_slice, writes);
    mark_live_slice_set(live, base_slice, reads);
}

fn mark_live_slice_set(
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    base_slice: ObjectSlice,
    slices: &SliceSet,
) {
    if slices.is_empty() {
        return;
    }
    if slices.is_whole_root() || base_slice.leaf_count != slices.total_leaves() {
        clear_or_mark_live_slice(live, base_slice, true);
        return;
    }
    let Some(leaves) = slices.exact_leaves() else {
        clear_or_mark_live_slice(live, base_slice, true);
        return;
    };
    let root_live = live.entry(base_slice.root).or_default();
    root_live.extend(leaves.iter().map(|leaf| base_slice.first_leaf + *leaf));
}

fn clear_live_slice_set(
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    base_slice: ObjectSlice,
    slices: &SliceSet,
) {
    if slices.is_empty() {
        return;
    }
    if slices.is_whole_root() || base_slice.leaf_count != slices.total_leaves() {
        clear_or_mark_live_slice(live, base_slice, false);
        return;
    }
    let Some(leaves) = slices.exact_leaves() else {
        clear_or_mark_live_slice(live, base_slice, false);
        return;
    };
    if let Some(root_live) = live.get_mut(&base_slice.root) {
        for leaf in leaves {
            root_live.remove(&(base_slice.first_leaf + leaf));
        }
    }
}

fn clear_or_mark_live_slice(
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    base_slice: ObjectSlice,
    mark: bool,
) {
    if mark {
        mark_live(live, TrackedObject::Exact(base_slice));
    } else {
        clear_live_slice(live, base_slice);
    }
}

fn meet_live(
    states: impl Iterator<Item = FxHashMap<ValueId, FxHashSet<usize>>>,
) -> FxHashMap<ValueId, FxHashSet<usize>> {
    let mut out = FxHashMap::default();
    for state in states {
        for (root, leaves) in state {
            out.entry(root)
                .or_insert_with(FxHashSet::default)
                .extend(leaves);
        }
    }
    out
}

fn transfer_backward_live(
    func: &Function,
    inst: InstId,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    provenance: MayProvenance<'_>,
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) {
    if let Some(obj_load) = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)) {
        if let Some(tracked_object) = tracked[*obj_load.object()].as_ref().copied() {
            mark_live(live, tracked_object);
        } else {
            mark_live_may_roots(
                func,
                live,
                tracked,
                provenance.may_roots(*obj_load.object()),
            );
        }
        let (roots, observed_unknown) =
            observed_roots(func, inst, provenance, &[*obj_load.object()]);
        if observed_unknown {
            mark_all_tracked_roots_live(func, tracked, live);
        } else {
            for root in roots {
                mark_root_live(live, root, root_total_leaves(tracked, root));
            }
        }
        return;
    }

    if let Some(obj_store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)) {
        let (roots, observed_unknown) =
            observed_roots(func, inst, provenance, &[*obj_store.object()]);
        if observed_unknown {
            mark_all_tracked_roots_live(func, tracked, live);
        } else {
            for root in roots {
                mark_root_live(live, root, root_total_leaves(tracked, root));
            }
        }

        let Some(tracked_object) = tracked[*obj_store.object()].as_ref().copied() else {
            mark_live_may_roots(
                func,
                live,
                tracked,
                provenance.may_roots(*obj_store.object()),
            );
            return;
        };
        if let Some(slice) = tracked_object.exact() {
            clear_live_slice(live, slice);
        } else {
            mark_live_may_roots(
                func,
                live,
                tracked,
                provenance.may_roots(*obj_store.object()),
            );
        }
        return;
    }

    if let Some(enum_get_tag) = downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst))
    {
        if let Some(tracked_object) = tracked[*enum_get_tag.object()].as_ref().copied() {
            if let Some(slice) = tracked_object
                .exact()
                .and_then(|slice| enum_tag_object_slice(func.ctx(), slice))
            {
                mark_live(live, TrackedObject::Exact(slice));
            } else {
                mark_live(live, tracked_object);
            }
        } else {
            mark_live_may_roots(
                func,
                live,
                tracked,
                provenance.may_roots(*enum_get_tag.object()),
            );
        }
        let (roots, observed_unknown) =
            observed_roots(func, inst, provenance, &[*enum_get_tag.object()]);
        if observed_unknown {
            mark_all_tracked_roots_live(func, tracked, live);
        } else {
            for root in roots {
                mark_root_live(live, root, root_total_leaves(tracked, root));
            }
        }
        return;
    }

    if let Some(enum_assert_ref) =
        downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst))
    {
        if let Some(tracked_object) = tracked[*enum_assert_ref.object()].as_ref().copied() {
            if let Some(slice) = tracked_object
                .exact()
                .and_then(|slice| enum_tag_object_slice(func.ctx(), slice))
            {
                mark_live(live, TrackedObject::Exact(slice));
            } else {
                mark_live(live, tracked_object);
            }
        }
        return;
    }

    if let Some(enum_set_tag) = downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst))
    {
        let (roots, observed_unknown) =
            observed_roots(func, inst, provenance, &[*enum_set_tag.object()]);
        if observed_unknown {
            mark_all_tracked_roots_live(func, tracked, live);
        } else {
            for root in roots {
                mark_root_live(live, root, root_total_leaves(tracked, root));
            }
        }
        let Some(tracked_object) = tracked[*enum_set_tag.object()].as_ref().copied() else {
            mark_live_may_roots(
                func,
                live,
                tracked,
                provenance.may_roots(*enum_set_tag.object()),
            );
            return;
        };
        if let Some(slice) = tracked_object
            .exact()
            .and_then(|slice| enum_tag_object_slice(func.ctx(), slice))
        {
            clear_live_slice(live, slice);
        } else {
            mark_live_may_roots(
                func,
                live,
                tracked,
                provenance.may_roots(*enum_set_tag.object()),
            );
        }
        return;
    }

    if let Some(enum_write_variant) =
        downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst))
    {
        let (roots, observed_unknown) =
            observed_roots(func, inst, provenance, &[*enum_write_variant.object()]);
        if observed_unknown {
            mark_all_tracked_roots_live(func, tracked, live);
        } else {
            for root in roots {
                mark_root_live(live, root, root_total_leaves(tracked, root));
            }
        }
        let Some(tracked_object) = tracked[*enum_write_variant.object()].as_ref().copied() else {
            mark_live_may_roots(
                func,
                live,
                tracked,
                provenance.may_roots(*enum_write_variant.object()),
            );
            return;
        };
        let Some(base_slice) = tracked_object.exact() else {
            mark_live_may_roots(
                func,
                live,
                tracked,
                provenance.may_roots(*enum_write_variant.object()),
            );
            return;
        };
        if let Some(tag_slice) = enum_tag_object_slice(func.ctx(), base_slice) {
            clear_live_slice(live, tag_slice);
        }
        for field_idx in 0..enum_write_variant.values().len() {
            let Some(field_slice) = enum_variant_field_object_slice(
                func.ctx(),
                base_slice,
                *enum_write_variant.variant(),
                u32::try_from(field_idx).ok().unwrap_or(u32::MAX),
            ) else {
                continue;
            };
            clear_live_slice(live, field_slice);
        }
        return;
    }

    if handle_call_backward(func, inst, tracked, provenance, live, object_effects) {
        return;
    }

    let (roots, observed_unknown) = observed_roots(func, inst, provenance, &[]);
    if observed_unknown {
        mark_all_tracked_roots_live(func, tracked, live);
    } else {
        for root in roots {
            mark_root_live(live, root, root_total_leaves(tracked, root));
        }
    }
}

fn try_remove_dead_store(
    func: &mut Function,
    inst: InstId,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    provenance: MayProvenance<'_>,
    live: &FxHashMap<ValueId, FxHashSet<usize>>,
) -> bool {
    if let Some(obj_store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)) {
        let Some(tracked_object) = tracked[*obj_store.object()].as_ref().copied() else {
            return false;
        };
        let needed = if let Some(slice) = tracked_object.exact() {
            slice_has_live_leaf(live, slice)
        } else {
            roots_have_live(live, provenance.may_roots(*obj_store.object()))
        };
        if needed {
            return false;
        }

        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        return true;
    }

    if let Some(enum_set_tag) = downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst))
    {
        let Some(tracked_object) = tracked[*enum_set_tag.object()].as_ref().copied() else {
            return false;
        };
        let needed = if let Some(slice) = tracked_object
            .exact()
            .and_then(|slice| enum_tag_object_slice(func.ctx(), slice))
        {
            slice_has_live_leaf(live, slice)
        } else {
            roots_have_live(live, provenance.may_roots(*enum_set_tag.object()))
        };
        if needed {
            return false;
        }

        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        return true;
    }

    let Some(enum_write_variant) =
        downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst))
    else {
        return false;
    };
    let Some(tracked_object) = tracked[*enum_write_variant.object()].as_ref().copied() else {
        return false;
    };
    let needed = if let Some(base_slice) = tracked_object.exact() {
        enum_write_variant_slices(func.ctx(), base_slice, enum_write_variant)
            .into_iter()
            .any(|slice| slice_has_live_leaf(live, slice))
    } else {
        roots_have_live(live, provenance.may_roots(*enum_write_variant.object()))
    };
    if needed {
        return false;
    }

    InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    true
}

fn root_total_leaves(
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    root: ValueId,
) -> usize {
    tracked[root]
        .as_ref()
        .copied()
        .map(TrackedObject::total_leaves)
        .expect("tracked root should exist")
}

fn mark_live_may_roots(
    func: &Function,
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    roots: MayRootSet<'_>,
) {
    if roots.has_unknown() {
        mark_all_tracked_roots_live(func, tracked, live);
        return;
    }
    for root in roots.observed().iter() {
        mark_root_live(live, root.value(), root_total_leaves(tracked, root.value()));
    }
}

fn roots_have_live(live: &FxHashMap<ValueId, FxHashSet<usize>>, roots: MayRootSet<'_>) -> bool {
    let Some(roots) = roots.exhaustive_known_roots() else {
        return true;
    };
    roots.iter().any(|root| root_has_live(live, root.value()))
}

fn single_result_value(func: &Function, inst: InstId) -> Option<ValueId> {
    let [result] = func.dfg.inst_results(inst) else {
        return None;
    };
    Some(*result)
}

fn map_capture_slice(
    tracked: TrackedObject,
    capture: shape::AggregateSlice,
) -> Option<ObjectSlice> {
    match tracked {
        TrackedObject::Exact(base) => (capture.first_leaf + capture.leaf_count <= base.leaf_count)
            .then_some(ObjectSlice {
                root: base.root,
                ty: capture.ty,
                first_leaf: base.first_leaf + capture.first_leaf,
                leaf_count: capture.leaf_count,
                total_leaves: base.total_leaves,
            }),
        TrackedObject::RootUnknown { .. } => None,
    }
}

fn kill_overlapping_available(available: &mut AvailableMap, slice: ObjectSlice) {
    available.retain(|other, _| other.root != slice.root || !slices_overlap(*other, slice));
}

fn kill_root_available(available: &mut AvailableMap, root: ValueId) {
    available.retain(|slice, _| slice.root != root);
}

fn mark_live(live: &mut FxHashMap<ValueId, FxHashSet<usize>>, tracked: TrackedObject) {
    match tracked {
        TrackedObject::Exact(slice) => {
            let entry = live.entry(slice.root).or_default();
            for leaf in slice.first_leaf..slice.first_leaf + slice.leaf_count {
                entry.insert(leaf);
            }
        }
        TrackedObject::RootUnknown { root, total_leaves } => {
            mark_root_live(live, root, total_leaves)
        }
    }
}

fn mark_root_live(
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    root: ValueId,
    total_leaves: usize,
) {
    let entry = live.entry(root).or_default();
    for leaf in 0..total_leaves {
        entry.insert(leaf);
    }
}

fn clear_live_slice(live: &mut FxHashMap<ValueId, FxHashSet<usize>>, slice: ObjectSlice) {
    let Some(entry) = live.get_mut(&slice.root) else {
        return;
    };
    for leaf in slice.first_leaf..slice.first_leaf + slice.leaf_count {
        entry.remove(&leaf);
    }
    if entry.is_empty() {
        live.remove(&slice.root);
    }
}

fn slice_has_live_leaf(live: &FxHashMap<ValueId, FxHashSet<usize>>, slice: ObjectSlice) -> bool {
    live.get(&slice.root).is_some_and(|entry| {
        (slice.first_leaf..slice.first_leaf + slice.leaf_count).any(|leaf| entry.contains(&leaf))
    })
}

fn root_has_live(live: &FxHashMap<ValueId, FxHashSet<usize>>, root: ValueId) -> bool {
    live.get(&root).is_some_and(|entry| !entry.is_empty())
}

fn enum_variant_tag_imm(variant: sonatina_ir::types::EnumVariantRef, ty: Type) -> Immediate {
    match ty {
        Type::EnumTag(enum_ty) => Immediate::EnumTag {
            enum_ty,
            value: I256::from(u64::from(variant.index())),
        },
        _ => Immediate::from_i256(I256::from(u64::from(variant.index())), ty),
    }
}

fn enum_write_variant_slices(
    ctx: &sonatina_ir::module::ModuleCtx,
    base: ObjectSlice,
    enum_write_variant: &data::EnumWriteVariant,
) -> Vec<ObjectSlice> {
    let mut slices = Vec::new();
    if let Some(tag_slice) = enum_tag_object_slice(ctx, base) {
        slices.push(tag_slice);
    }
    for field_idx in 0..enum_write_variant.values().len() {
        let Some(field_idx) = u32::try_from(field_idx).ok() else {
            continue;
        };
        if let Some(field_slice) =
            enum_variant_field_object_slice(ctx, base, *enum_write_variant.variant(), field_idx)
        {
            slices.push(field_slice);
        }
    }
    slices
}

fn ends_with_return(func: &Function, block: BlockId) -> bool {
    func.layout.last_inst_of(block).is_some_and(|inst| {
        downcast::<&control_flow::Return>(func.inst_set(), func.dfg.inst(inst)).is_some()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{ir_writer::FuncWriter, module::FuncRef};
    use sonatina_parser::parse_module;

    fn parse_test_module(src: &str) -> sonatina_ir::Module {
        parse_module(src).expect("parse should succeed").module
    }

    fn lookup_func(module: &sonatina_ir::Module, name: &str) -> FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .expect("function should exist")
    }

    fn run_with_effects(module: &sonatina_ir::Module, func_ref: FuncRef) {
        let object_effects = crate::transform::aggregate::compute_object_effect_summaries(module);
        let local_object_args = crate::transform::aggregate::collect_local_object_arg_info(module);
        module.func_store.modify(func_ref, |func| {
            ObjectLoadStore::default().run_for_func(
                func_ref,
                func,
                &local_object_args,
                &object_effects,
            );
        });
    }

    #[test]
    fn forwards_local_object_arg_field_store_then_load() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.objref<@pair>, v1.i256) -> i256 {
    block0:
        v2.objref<i256> = obj.proj v0 0.i8;
        obj.store v2 v1;
        v3.i256 = obj.load v2;
        return v3;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.load"),
                "local object arg load should be forwarded:\n{dumped}"
            );
            assert!(
                dumped.contains("obj.store v2 v1;"),
                "local object arg mutation must remain visible to the caller:\n{dumped}"
            );
            assert!(
                dumped.contains("return v1;"),
                "forwarded local object arg result should return the stored scalar:\n{dumped}"
            );
        });
    }

    #[test]
    fn forwards_local_object_arg_enum_field_store_then_load_without_lowering() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @option_i256 = enum {
    #None,
    #Some(i256),
};

type @wrapper = { @option_i256, i256 };

func private %f(v0.objref<@wrapper>, v1.i256) -> @option_i256 {
    block0:
        v2.@option_i256 = enum.make @option_i256 #Some (v1);
        v3.objref<@option_i256> = obj.proj v0 0.i8;
        obj.store v3 v2;
        v4.@option_i256 = obj.load v3;
        return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.load"),
                "enum field load should be forwarded without pre-lowering:\n{dumped}"
            );
            assert!(
                dumped.contains("obj.store v3 v2;"),
                "enum field store must remain visible to the caller:\n{dumped}"
            );
            assert!(
                dumped.contains("return v2;"),
                "forwarded enum field result should return the stored enum value:\n{dumped}"
            );
        });
    }

    #[test]
    fn summary_read_only_call_preserves_forwarding() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %peek(v0.objref<@pair>) -> i256 {
    block0:
        v1.objref<i256> = obj.proj v0 0.i8;
        v2.i256 = obj.load v1;
        return v2;
}

func private %f(v0.objref<@pair>, v1.i256) -> i256 {
    block0:
        v2.objref<i256> = obj.proj v0 0.i8;
        obj.store v2 v1;
        v3.i256 = call %peek v0;
        v4.i256 = obj.load v2;
        return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("call %peek v0;"),
                "call should remain:\n{dumped}"
            );
            assert!(
                !dumped.contains("obj.load v2"),
                "read-only call should not kill forwarding:\n{dumped}"
            );
            assert!(
                dumped.contains("return v1;"),
                "forwarded value should survive the call:\n{dumped}"
            );
        });
    }

    #[test]
    fn summary_write_one_field_only_kills_that_field() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %write_second(v0.objref<@pair>, v1.i256) {
    block0:
        v2.objref<i256> = obj.proj v0 1.i8;
        obj.store v2 v1;
        return;
}

func private %f(v0.objref<@pair>, v1.i256, v2.i256) -> i256 {
    block0:
        v3.objref<i256> = obj.proj v0 0.i8;
        obj.store v3 v1;
        v4.objref<i256> = obj.proj v0 1.i8;
        obj.store v4 v2;
        call %write_second v0 9.i256;
        v5.i256 = obj.load v3;
        return v5;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.load v3"),
                "callee write to field 1 should not kill field 0 availability:\n{dumped}"
            );
            assert!(
                dumped.contains("return v1;"),
                "field 0 load should still forward:\n{dumped}"
            );
        });
    }

    #[test]
    fn summary_propagates_transitively_through_nested_calls() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %leaf(v0.objref<@pair>) -> i256 {
    block0:
        v1.objref<i256> = obj.proj v0 0.i8;
        v2.i256 = obj.load v1;
        return v2;
}

func private %mid(v0.objref<@pair>) -> i256 {
    block0:
        v1.i256 = call %leaf v0;
        return v1;
}

func private %f(v0.objref<@pair>, v1.i256) -> i256 {
    block0:
        v2.objref<i256> = obj.proj v0 0.i8;
        obj.store v2 v1;
        v3.i256 = call %mid v0;
        v4.i256 = obj.load v2;
        return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.load v2"),
                "transitive read-only summary should preserve forwarding:\n{dumped}"
            );
            assert!(
                dumped.contains("return v1;"),
                "transitive summary should keep stored value available:\n{dumped}"
            );
        });
    }

    #[test]
    fn fresh_return_summary_tracks_returned_root() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %make_pair() -> objref<@pair> {
    block0:
        v0.objref<@pair> = obj.alloc @pair;
        return v0;
}

func private %f(v0.i256) -> i256 {
    block0:
        v1.objref<@pair> = call %make_pair;
        v2.objref<i256> = obj.proj v1 0.i8;
        obj.store v2 v0;
        v3.i256 = obj.load v2;
        return v3;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.load v2"),
                "fresh-return helper result should become a tracked root:\n{dumped}"
            );
            assert!(
                dumped.contains("return v0;"),
                "store/load on fresh call result should forward:\n{dumped}"
            );
        });
    }

    #[test]
    fn incomplete_phi_read_summary_keeps_precall_store_live() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

declare external %mystery() -> objref<@pair>;

func private %read_maybe(v0.i1, v1.objref<@pair>) -> i256 {
block0:
    br v0 block1 block2;

block1:
    jump block3;

block2:
    v2.objref<@pair> = call %mystery;
    jump block3;

block3:
    v3.objref<@pair> = phi (v1 block1) (v2 block2);
    v4.objref<i256> = obj.proj v3 0.i8;
    v5.i256 = obj.load v4;
    return v5;
}

func private %main(v0.i1, v1.objref<@pair>, v2.i256) -> i256 {
block0:
    v3.objref<i256> = obj.proj v1 0.i8;
    obj.store v3 v2;
    v4.i256 = call %read_maybe v0 v1;
    return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "main");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("obj.store v3 v2;"),
                "pre-call store must stay live when callee may read the arg through incomplete provenance:\n{dumped}"
            );
        });
    }

    #[test]
    fn inexact_fresh_call_read_summary_keeps_precall_store_live() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @cell = { i256 };
type @take = { objref<i256> };

func private %take(v0.objref<@cell>) -> objref<@take> {
block0:
    v1.objref<@take> = obj.alloc @take;
    v2.objref<objref<i256>> = obj.proj v1 0.i8;
    v3.objref<i256> = obj.proj v0 0.i8;
    obj.store v2 v3;
    return v1;
}

func private %read_two_calls(v0.i1, v1.objref<@cell>) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.objref<@take> = call %take v1;
    jump block3;

block2:
    v3.objref<@take> = call %take v1;
    jump block3;

block3:
    v4.objref<@take> = phi (v2 block1) (v3 block2);
    v5.objref<objref<i256>> = obj.proj v4 0.i8;
    v6.objref<i256> = obj.load v5;
    v7.i256 = obj.load v6;
    return v7;
}

func private %main(v0.i1, v1.objref<@cell>, v2.i256) -> i256 {
block0:
    v3.objref<i256> = obj.proj v1 0.i8;
    obj.store v3 v2;
    v4.i256 = call %read_two_calls v0 v1;
    return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "main");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("obj.store v3 v2;"),
                "pre-call store must stay live when callee may read through inexact fresh helper roots:\n{dumped}"
            );
        });
    }

    #[test]
    fn returned_capture_chain_keeps_source_store_live() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Take = { i256, objref<[i256; 8]> };

func private %reverse(v0.objref<[i256; 8]>) -> objref<[i256; 8]> {
block0:
    return v0;
}

func private %take(v0.i256, v1.objref<[i256; 8]>) -> objref<@Take> {
block0:
    v2.objref<@Take> = obj.alloc @Take;
    v3.objref<i256> = obj.proj v2 0.i8;
    obj.store v3 v0;
    v4.objref<objref<[i256; 8]>> = obj.proj v2 1.i8;
    obj.store v4 v1;
    return v2;
}

func private %take_get(v0.objref<@Take>, v1.i256) -> i256 {
block0:
    v2.objref<objref<[i256; 8]>> = obj.proj v0 1.i8;
    v3.objref<[i256; 8]> = obj.load v2;
    v4.objref<i256> = obj.index v3 v1;
    v5.i256 = obj.load v4;
    return v5;
}

func private %sum_last4(v0.objref<[i256; 8]>) -> i256 {
block0:
    v1.objref<[i256; 8]> = call %reverse v0;
    v2.objref<@Take> = call %take 4.i256 v1;
    v3.i256 = call %take_get v2 0.i256;
    return v3;
}

func private %main() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.objref<i256> = obj.index v0 0.i256;
    obj.store v1 4.i256;
    v2.i256 = call %sum_last4 v0;
    return v2;
}
"#,
        );
        let func_ref = lookup_func(&module, "main");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("obj.store v1 4.i256;"),
                "source store should stay live through returned capture chain:\n{dumped}"
            );
        });
    }

    #[test]
    fn ambiguous_return_capture_keeps_source_store_live() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Cell = { i256 };
type @Inner = { objref<i256>, objref<i256> };
type @Outer = { @Inner, @Inner };

func private %pick(v0.i1, v1.objref<@Cell>, v2.objref<@Cell>) -> objref<@Inner> {
block0:
    v3.objref<@Outer> = obj.alloc @Outer;
    br v0 block1 block2;

block1:
    v4.objref<@Inner> = obj.proj v3 0.i8;
    v5.objref<objref<i256>> = obj.proj v4 1.i8;
    v6.objref<i256> = obj.proj v1 0.i8;
    obj.store v5 v6;
    v7.objref<objref<i256>> = obj.proj v4 0.i8;
    v8.objref<i256> = obj.proj v2 0.i8;
    obj.store v7 v8;
    jump block3;

block2:
    v9.objref<@Inner> = obj.proj v3 1.i8;
    v10.objref<objref<i256>> = obj.proj v9 0.i8;
    v11.objref<i256> = obj.proj v1 0.i8;
    obj.store v10 v11;
    v12.objref<objref<i256>> = obj.proj v9 1.i8;
    v13.objref<i256> = obj.proj v2 0.i8;
    obj.store v12 v13;
    jump block3;

block3:
    v14.objref<@Inner> = phi (v4 block1) (v9 block2);
    return v14;
}

func private %read_first(v0.objref<@Inner>) -> i256 {
block0:
    v1.objref<objref<i256>> = obj.proj v0 0.i8;
    v2.objref<i256> = obj.load v1;
    v3.i256 = obj.load v2;
    return v3;
}

func private %main(v0.i1) -> i256 {
block0:
    v1.objref<@Cell> = obj.alloc @Cell;
    v2.objref<i256> = obj.proj v1 0.i8;
    obj.store v2 4.i256;
    v3.objref<@Cell> = obj.alloc @Cell;
    v4.objref<i256> = obj.proj v3 0.i8;
    obj.store v4 9.i256;
    v5.objref<@Inner> = call %pick v0 v1 v3;
    v6.i256 = call %read_first v5;
    return v6;
}
"#,
        );
        let func_ref = lookup_func(&module, "main");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("obj.store v2 4.i256;"),
                "ambiguous returned capture should keep the source store live:\n{dumped}"
            );
        });
    }

    #[test]
    fn overwritten_captured_pointer_store_becomes_dead() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Cell = { i256 };
type @Holder = { objref<@Cell> };

func private %f(v0.i256) -> i256 {
block0:
    v1.objref<@Cell> = obj.alloc @Cell;
    v2.objref<i256> = obj.proj v1 0.i8;
    obj.store v2 11.i256;
    v3.objref<@Cell> = obj.alloc @Cell;
    v4.objref<i256> = obj.proj v3 0.i8;
    obj.store v4 v0;
    v5.objref<@Holder> = obj.alloc @Holder;
    v6.objref<objref<@Cell>> = obj.proj v5 0.i8;
    obj.store v6 v1;
    obj.store v6 v3;
    v7.objref<@Cell> = obj.load v6;
    v8.objref<i256> = obj.proj v7 0.i8;
    v9.i256 = obj.load v8;
    return v9;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        run_with_effects(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.store v2 11.i256;"),
                "stale overwritten capture should not keep the first source store live:\n{dumped}"
            );
            assert!(
                dumped.contains("return v0;"),
                "precise overwritten capture provenance should let the final load collapse to the live source value:\n{dumped}"
            );
        });
    }

    #[test]
    fn forwards_store_into_successor_block() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.i256) -> i256 {
    block0:
        v1.objref<@pair> = obj.alloc @pair;
        v2.objref<i256> = obj.proj v1 0.i8;
        obj.store v2 v0;
        jump block1;

    block1:
        v3.objref<i256> = obj.proj v1 0.i8;
        v4.i256 = obj.load v3;
        return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(ObjectLoadStore::default().run(func))
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.load"),
                "store in predecessor should forward into successor:\n{dumped}"
            );
            assert!(
                dumped.contains("return v0;"),
                "successor should return the predecessor's stored value:\n{dumped}"
            );
        });
    }

    #[test]
    fn forwards_identical_pred_stores_into_join_block() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.i1, v1.i256) -> i256 {
    block0:
        v2.objref<@pair> = obj.alloc @pair;
        br v0 block1 block2;

    block1:
        v3.objref<i256> = obj.proj v2 0.i8;
        obj.store v3 v1;
        jump block3;

    block2:
        v4.objref<i256> = obj.proj v2 0.i8;
        obj.store v4 v1;
        jump block3;

    block3:
        v5.objref<i256> = obj.proj v2 0.i8;
        v6.i256 = obj.load v5;
        return v6;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(ObjectLoadStore::default().run(func))
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.load"),
                "matching predecessor stores should meet at the join:\n{dumped}"
            );
            assert!(
                dumped.contains("return v1;"),
                "join block should forward the common stored value:\n{dumped}"
            );
        });
    }

    #[test]
    fn does_not_forward_differing_pred_stores_into_join_block() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.i1, v1.i256, v2.i256) -> i256 {
    block0:
        v3.objref<@pair> = obj.alloc @pair;
        br v0 block1 block2;

    block1:
        v4.objref<i256> = obj.proj v3 0.i8;
        obj.store v4 v1;
        jump block3;

    block2:
        v5.objref<i256> = obj.proj v3 0.i8;
        obj.store v5 v2;
        jump block3;

    block3:
        v6.objref<i256> = obj.proj v3 0.i8;
        v7.i256 = obj.load v6;
        return v7;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(!ObjectLoadStore::default().run(func))
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("obj.load v6"),
                "join should not forward when predecessor stores disagree:\n{dumped}"
            );
        });
    }

    #[test]
    fn eliminates_dead_predecessor_store_before_successor_overwrite() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %use(v0.objref<@pair>) {
    block0:
        return;
}

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        v2.objref<@pair> = obj.alloc @pair;
        v3.objref<i256> = obj.proj v2 0.i8;
        obj.store v3 v0;
        jump block1;

    block1:
        v4.objref<i256> = obj.proj v2 0.i8;
        obj.store v4 v1;
        call %use v2;
        return v1;

}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(ObjectLoadStore::default().run(func))
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert_eq!(
                dumped.matches("obj.store").count(),
                1,
                "dead predecessor store should be removed:\n{dumped}"
            );
            assert!(
                dumped.contains("return v1;"),
                "successor overwrite should remain as the visible store:\n{dumped}"
            );
        });
    }

    #[test]
    fn forwards_header_store_into_loop_body() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.i256, v1.i1) -> i256 {
    block0:
        v2.objref<@pair> = obj.alloc @pair;
        jump block1;

    block1:
        v3.objref<i256> = obj.proj v2 0.i8;
        obj.store v3 v0;
        br v1 block2 block3;

    block2:
        v4.objref<i256> = obj.proj v2 0.i8;
        v5.i256 = obj.load v4;
        jump block1;

    block3:
        v6.objref<i256> = obj.proj v2 0.i8;
        v7.i256 = obj.load v6;
        return v7;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(ObjectLoadStore::default().run(func))
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.load"),
                "header store should forward into both loop body and exit:\n{dumped}"
            );
            assert!(
                dumped.contains("return v0;"),
                "exit should return the header-stored value:\n{dumped}"
            );
        });
    }
}
