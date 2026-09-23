use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, I256, Immediate, InstId, Type, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
    module::FuncRef,
};

use super::{
    LocalObjectArgInfo, LocalObjectArgMap, ObjectEffectSummaryMap,
    cleanup::DeadPureInstCleanup,
    object_access::{ObjectAccess, ObjectAccessFacts, ObjectInstEffects},
    object_state::{
        LiveLeafMap, enum_write_variant_slices, mark_live_slice, mark_root_live,
        slice_has_live_leaf, union_live_leaf_maps,
    },
    object_tracking::{
        ObjectSlice, TrackedObject, enum_tag_object_slice, enum_variant_field_object_slice,
        slice_is_covered_by, whole_root_slice_for_value,
    },
    provenance::{MayProvenance, MayRootSet, RootValue},
    reconstruct::AggregateValueReconstructor,
    shape,
};

type AvailableMap = FxHashMap<ObjectSlice, ValueId>;

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
            // There can be no object-memory optimization target without an
            // object reference. Preserve the pass's ordinary dead-pure cleanup
            // without building an access universe for raw/scalar-only code.
            if !func
                .dfg
                .value_ids()
                .any(|value| func.dfg.value_ty(value).is_obj_ref(func.ctx()))
            {
                self.changed |= self.dead_pure_cleanup.run_with_current_users(func);
                if self.changed {
                    func.rebuild_users();
                }
                return self.changed;
            }
            let accesses = ObjectAccessFacts::new(func, object_effects);
            let tracked = accesses.tracked(func, local_object_args, &mut self.layout_cache);
            let tracked = &tracked;
            let may = accesses.may();
            let live_out_roots = self.collect_live_out_roots(tracked, func, &accesses);
            let mut iter_changed = self.run_forward(func, tracked, &accesses, object_effects);
            iter_changed |= self.run_backward(
                func,
                tracked,
                may,
                &accesses,
                &live_out_roots,
                object_effects,
            );

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
        accesses: &ObjectAccessFacts,
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
                        accesses,
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

    fn transfer_forward(
        &mut self,
        func: &mut Function,
        inst: InstId,
        tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
        accesses: &ObjectAccessFacts,
        available: &mut AvailableMap,
        object_effects: Option<&ObjectEffectSummaryMap>,
    ) -> bool {
        let effects = accesses.effects(func, inst, object_effects);
        let exact = |value| tracked[value].and_then(TrackedObject::exact);
        let read =
            if let Some(load) = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)) {
                exact(*load.object())
            } else if let Some(load) =
                downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst))
            {
                exact(*load.object()).and_then(|slice| enum_tag_object_slice(func.ctx(), slice))
            } else {
                None
            };
        if let Some(slice) = read
            && let Some(replacement) = self.replacement_for_load(func, inst, slice, available)
            && let Some(result) = func.dfg.inst_result(inst)
        {
            func.dfg.change_to_alias(result, replacement);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return true;
        }

        let mut written = Vec::new();
        if let Some(store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)) {
            if let Some(slice) = exact(*store.object()) {
                written.push((slice, *store.value()));
            }
        } else if let Some(store) =
            downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst)).copied()
        {
            if let Some(slice) =
                exact(*store.object()).and_then(|slice| enum_tag_object_slice(func.ctx(), slice))
            {
                written.push((
                    slice,
                    func.dfg
                        .make_imm_value(enum_variant_tag_imm(*store.variant(), slice.ty)),
                ));
            }
        } else if let Some(store) =
            downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst)).cloned()
            && let Some(base) = exact(*store.object())
        {
            for (index, &value) in store.values().iter().enumerate() {
                if let Some(slice) = u32::try_from(index).ok().and_then(|index| {
                    enum_variant_field_object_slice(func.ctx(), base, *store.variant(), index)
                }) {
                    written.push((slice, value));
                }
            }
            if let Some(slice) = enum_tag_object_slice(func.ctx(), base) {
                written.push((
                    slice,
                    func.dfg
                        .make_imm_value(enum_variant_tag_imm(*store.variant(), slice.ty)),
                ));
            }
        }
        written.retain(|(slice, _)| {
            effects
                .overwrites
                .iter()
                .any(|&write| accesses.write_covers(write, *slice))
        });
        // Check redundancy against the old contents, before invalidating aliases.
        if !written.is_empty()
            && written
                .iter()
                .all(|(slice, value)| available.get(slice) == Some(value))
        {
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return true;
        }
        available.retain(|slice, _| {
            !effects
                .writes
                .iter()
                .any(|&effect| accesses.may_overlap(effect, *slice))
        });
        available.extend(written);
        false
    }

    fn run_backward(
        &mut self,
        func: &mut Function,
        tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
        provenance: MayProvenance<'_>,
        accesses: &ObjectAccessFacts,
        live_out_roots: &FxHashMap<ValueId, usize>,
        object_effects: Option<&ObjectEffectSummaryMap>,
    ) -> bool {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let reachable = cfg.reachable_blocks();
        let order: Vec<_> = cfg.post_order().collect();
        let mut in_states = SecondaryMap::<BlockId, LiveLeafMap>::new();
        let mut out_states = SecondaryMap::<BlockId, LiveLeafMap>::new();
        let mut changed = false;

        let mut dataflow_changed = true;
        while dataflow_changed {
            dataflow_changed = false;
            for &block in &order {
                if !reachable[block] {
                    continue;
                }

                let mut out_state = union_live_leaf_maps(
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
                        accesses,
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
                transfer_backward_live(func, inst, tracked, accesses, &mut live, object_effects);
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
        accesses: &ObjectAccessFacts,
    ) -> FxHashMap<ValueId, usize> {
        let mut live_out_roots = FxHashMap::default();
        for value in func.dfg.value_ids() {
            if let Some(root) = whole_root_slice_for_value(tracked, value)
                && accesses.exposed(RootValue::new(root.root))
            {
                live_out_roots.insert(root.root, root.total_leaves);
            }
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

fn mark_access_live(
    func: &Function,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    accesses: &ObjectAccessFacts,
    access: ObjectAccess,
    live: &mut LiveLeafMap,
) {
    for value in func.dfg.value_ids() {
        let Some(root) = whole_root_slice_for_value(tracked, value) else {
            continue;
        };
        if !accesses.may_overlap(access, root) {
            continue;
        }
        if let ObjectAccess::Exact(projection) = access
            && projection.root_value.value() == root.root
        {
            mark_live_slice(
                live,
                ObjectSlice {
                    ty: projection.slice.ty,
                    first_leaf: projection.slice.first_leaf,
                    leaf_count: projection.slice.leaf_count,
                    ..root
                },
            );
        } else {
            mark_root_live(live, root.root, root.total_leaves);
        }
    }
}

fn transfer_backward_live(
    func: &Function,
    inst: InstId,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    accesses: &ObjectAccessFacts,
    live: &mut LiveLeafMap,
    object_effects: Option<&ObjectEffectSummaryMap>,
) {
    let effects = accesses.effects(func, inst, object_effects);
    transfer_backward_effects(func, tracked, accesses, &effects, live);
}

pub(crate) fn transfer_backward_effects(
    func: &Function,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    accesses: &ObjectAccessFacts,
    effects: &ObjectInstEffects,
    live: &mut LiveLeafMap,
) {
    let mut captured_reads = Vec::new();
    // Capture observations are conditional on the destination's future demand,
    // evaluated before a direct overwrite removes that demand.
    for (destinations, sources) in &effects.captures {
        if live.iter().any(|(&root, leaves)| {
            whole_root_slice_for_value(tracked, root).is_some_and(|root| {
                leaves.iter().any(|&leaf| {
                    destinations.iter().any(|&destination| {
                        accesses.may_overlap(
                            destination,
                            ObjectSlice {
                                first_leaf: leaf,
                                leaf_count: 1,
                                ..root
                            },
                        )
                    })
                })
            })
        }) {
            captured_reads.extend(sources.iter().copied());
        }
    }
    live.retain(|&root, leaves| {
        if let Some(root) = whole_root_slice_for_value(tracked, root) {
            leaves.retain(|&leaf| {
                !effects.overwrites.iter().any(|&write| {
                    accesses.write_covers(
                        write,
                        ObjectSlice {
                            first_leaf: leaf,
                            leaf_count: 1,
                            ..root
                        },
                    )
                })
            });
        }
        !leaves.is_empty()
    });
    for access in effects.reads.iter().copied().chain(captured_reads) {
        mark_access_live(func, tracked, accesses, access, live);
    }
}

fn try_remove_dead_store(
    func: &mut Function,
    inst: InstId,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    provenance: MayProvenance<'_>,
    live: &LiveLeafMap,
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

fn roots_have_live(live: &LiveLeafMap, roots: MayRootSet<'_>) -> bool {
    let Some(roots) = roots.exhaustive_known_roots() else {
        return true;
    };
    roots.iter().any(|root| root_has_live(live, root.value()))
}

fn root_has_live(live: &LiveLeafMap, root: ValueId) -> bool {
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
    fn aggregate_argument_writes_invalidate_caller_loads() {
        let module = parse_test_module(
            r#"target = "evm-ethereum-osaka"
type @Wrapper = { objref<i256> };
func inline(never) private %overwrite(v0.@Wrapper) {
block0:
 v1.objref<i256> = extract_value v0 0.i8;
 obj.store v1 22.i256;
 return;
}
func public %entry() -> i256 {
block0:
 v0.objref<i256> = obj.alloc i256;
 v1.@Wrapper = insert_value undef.@Wrapper 0.i8 v0;
 obj.store v0 11.i256;
 call %overwrite v1;
 v2.i256 = obj.load v0;
 return v2;
}
"#,
        );
        let entry = lookup_func(&module, "entry");
        run_with_effects(&module, entry);
        module.func_store.view(entry, |func| {
            let dumped = FuncWriter::new(entry, func).dump_string();
            assert!(dumped.contains("obj.load"), "{dumped}");
            assert!(dumped.contains("obj.store"), "{dumped}");
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
