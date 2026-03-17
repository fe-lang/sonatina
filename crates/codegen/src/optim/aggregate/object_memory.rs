use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, ValueId,
    inst::{cast, control_flow, data, downcast},
};

use crate::loop_analysis::{Loop, LoopTree};

use super::{
    LocalObjectArgInfo, ObjectEffectSummaryMap, RootInit, SliceSet, collect_root_provenance,
    object_tracking::{
        ObjectSlice, TrackedObject, collect_root_slices, collect_tracked_objects,
        enum_tag_object_slice, enum_variant_field_object_slice, object_slice_overlaps_effect,
        slice_is_covered_by, slices_overlap, whole_root_slice_for_value,
    },
    shape,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ObjectMemToken {
    LiveIn { root: ValueId },
    FreshEntry { root: ValueId },
    Inst { inst: InstId },
    Phi { block: BlockId, slice: ObjectSlice },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum MemoryCarrier {
    Value {
        value: ValueId,
        slice: ObjectSlice,
    },
    Token {
        token: ObjectMemToken,
        slice: ObjectSlice,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ObjectReadGvnKey {
    ValueCarrier {
        value: ValueId,
        carrier_slice: ObjectSlice,
        read_slice: ObjectSlice,
    },
    Memory {
        token: ObjectMemToken,
        carrier_slice: ObjectSlice,
        read_slice: ObjectSlice,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ObjectReadState {
    read_slice: ObjectSlice,
    key: ObjectReadGvnKey,
    may_be_undef: bool,
}

impl ObjectReadState {
    pub(crate) fn key(self) -> ObjectReadGvnKey {
        self.key
    }

    pub(crate) fn may_be_undef(self) -> bool {
        self.may_be_undef
    }

    pub(crate) fn read_slice(self) -> ObjectSlice {
        self.read_slice
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ObjectClobber {
    Slice(ObjectSlice),
    LeafSet {
        base_slice: ObjectSlice,
        leaves: FxHashSet<usize>,
    },
    Root(ValueId),
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
struct MemoryState {
    carriers: FxHashMap<ObjectSlice, MemoryCarrier>,
    initialized_leaves: FxHashMap<ValueId, FxHashSet<usize>>,
    active_roots: FxHashSet<ValueId>,
    blocked_roots: FxHashSet<ValueId>,
}

struct TransferCtx<'a> {
    func: &'a Function,
    tracked: &'a SecondaryMap<ValueId, Option<TrackedObject>>,
    possible_roots: &'a SecondaryMap<ValueId, FxHashSet<ValueId>>,
    relevant_slices: &'a FxHashMap<ValueId, Vec<ObjectSlice>>,
    object_effects: Option<&'a ObjectEffectSummaryMap>,
}

#[derive(Default)]
pub(crate) struct ObjectMemoryAnalysis {
    layout_cache: shape::AggregateLayoutCache,
    read_states: FxHashMap<InstId, ObjectReadState>,
    clobbers: FxHashMap<InstId, Vec<ObjectClobber>>,
}

impl ObjectMemoryAnalysis {
    pub(crate) fn compute(
        &mut self,
        func: &Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
        object_effects: Option<&ObjectEffectSummaryMap>,
    ) {
        self.layout_cache.clear();
        self.read_states.clear();
        self.clobbers.clear();

        let root_slices = collect_root_slices(func, local_object_args, &mut self.layout_cache);
        let provenance = collect_root_provenance(
            func,
            func.ctx(),
            &root_slices,
            &mut self.layout_cache,
            object_effects,
        );
        let tracked = collect_tracked_objects(func, &provenance, &mut self.layout_cache);
        let possible_roots = provenance.into_possible_roots();
        let relevant_slices = collect_relevant_slices(func, &tracked);
        if relevant_slices.is_empty() {
            return;
        }

        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let reachable = cfg.reachable_blocks();
        let order: Vec<_> = cfg
            .post_order()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        let initial_state = initial_state(func, local_object_args, &tracked, &relevant_slices);
        let mut in_states = SecondaryMap::<BlockId, MemoryState>::new();
        let mut out_states = SecondaryMap::<BlockId, MemoryState>::new();
        let mut out_valid = SecondaryMap::<BlockId, bool>::new();
        let entry = func.layout.entry_block();

        let mut dataflow_changed = true;
        while dataflow_changed {
            dataflow_changed = false;
            for &block in &order {
                if !reachable[block] {
                    continue;
                }

                let in_state = if Some(block) == entry {
                    initial_state.clone()
                } else {
                    meet_memory_states(
                        block,
                        cfg.preds_of(block)
                            .copied()
                            .filter(|pred| reachable[*pred])
                            .filter(|pred| out_valid[*pred])
                            .map(|pred| &out_states[pred]),
                        &relevant_slices,
                    )
                };
                if in_states[block] != in_state {
                    in_states[block] = in_state.clone();
                    dataflow_changed = true;
                }

                let mut state = in_state;
                let transfer_ctx = TransferCtx {
                    func,
                    tracked: &tracked,
                    possible_roots: &possible_roots,
                    relevant_slices: &relevant_slices,
                    object_effects,
                };
                for inst in func.layout.iter_inst(block) {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    transfer_inst(&transfer_ctx, inst, &mut state, &mut None);
                }

                if !out_valid[block] || out_states[block] != state {
                    out_states[block] = state;
                    out_valid[block] = true;
                    dataflow_changed = true;
                }
            }
        }

        for &block in &order {
            if !reachable[block] {
                continue;
            }

            let mut state = in_states[block].clone();
            let transfer_ctx = TransferCtx {
                func,
                tracked: &tracked,
                possible_roots: &possible_roots,
                relevant_slices: &relevant_slices,
                object_effects,
            };
            for inst in func.layout.iter_inst(block) {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                let mut record = Some(&mut *self);
                transfer_inst(&transfer_ctx, inst, &mut state, &mut record);
            }
        }
    }

    pub(crate) fn read_state(&self, inst: InstId) -> Option<ObjectReadState> {
        self.read_states.get(&inst).copied()
    }

    pub(crate) fn read_is_loop_invariant(
        &self,
        func: &Function,
        cfg: &ControlFlowGraph,
        lpt: &LoopTree,
        lp: Loop,
        inst: InstId,
    ) -> bool {
        let Some(read) = self.read_state(inst) else {
            return false;
        };
        if read.may_be_undef() {
            return false;
        }

        for block in lpt.iter_blocks_post_order(cfg, lp) {
            for loop_inst in func.layout.iter_inst(block) {
                if !func.layout.is_inst_inserted(loop_inst) || loop_inst == inst {
                    continue;
                }
                if self.inst_clobbers_slice(loop_inst, read.read_slice()) {
                    return false;
                }
            }
        }
        true
    }

    fn inst_clobbers_slice(&self, inst: InstId, slice: ObjectSlice) -> bool {
        self.clobbers.get(&inst).is_some_and(|effects| {
            effects
                .iter()
                .any(|effect| clobber_overlaps_slice(effect, slice))
        })
    }
}

fn collect_relevant_slices(
    func: &Function,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
) -> FxHashMap<ValueId, Vec<ObjectSlice>> {
    let mut relevant = FxHashMap::<ValueId, FxHashSet<ObjectSlice>>::default();

    for value in func.dfg.value_ids() {
        if let Some(slice) = whole_root_slice_for_value(tracked, value) {
            relevant.entry(slice.root).or_default().insert(slice);
        }
    }

    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if !func.layout.is_inst_inserted(inst) {
                continue;
            }

            if let Some(obj_load) = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                && let Some(slice) = tracked[*obj_load.object()]
                    .as_ref()
                    .copied()
                    .and_then(TrackedObject::exact)
            {
                relevant.entry(slice.root).or_default().insert(slice);
            }

            if let Some(enum_get_tag) =
                downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst))
                && let Some(slice) = tracked[*enum_get_tag.object()]
                    .as_ref()
                    .copied()
                    .and_then(TrackedObject::exact)
                    .and_then(|slice| enum_tag_object_slice(func.ctx(), slice))
            {
                relevant.entry(slice.root).or_default().insert(slice);
            }
        }
    }

    relevant
        .into_iter()
        .map(|(root, slices)| {
            let mut slices: Vec<_> = slices.into_iter().collect();
            slices.sort_unstable_by_key(|slice| (slice.first_leaf, slice.leaf_count));
            (root, slices)
        })
        .collect()
}

fn initial_state(
    func: &Function,
    local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    relevant_slices: &FxHashMap<ValueId, Vec<ObjectSlice>>,
) -> MemoryState {
    let mut state = MemoryState::default();
    let Some(local_object_args) = local_object_args else {
        return state;
    };

    for (&idx, info) in local_object_args {
        let Some(&root) = func.arg_values.get(idx) else {
            continue;
        };
        let Some(root_slice) = whole_root_slice_for_value(tracked, root) else {
            continue;
        };
        let token = match info.init {
            RootInit::LoadLiveIn => ObjectMemToken::LiveIn { root },
            RootInit::UndefFresh => ObjectMemToken::FreshEntry { root },
        };
        activate_root(&mut state, root_slice, token, relevant_slices);
        if info.init == RootInit::LoadLiveIn {
            mark_slice_initialized(&mut state, root_slice);
        } else {
            state.initialized_leaves.entry(root).or_default();
        }
    }

    state
}

fn meet_memory_states<'a>(
    block: BlockId,
    mut preds: impl Iterator<Item = &'a MemoryState>,
    relevant_slices: &FxHashMap<ValueId, Vec<ObjectSlice>>,
) -> MemoryState {
    let Some(first) = preds.next() else {
        return MemoryState::default();
    };
    let rest: Vec<_> = preds.collect();
    let mut state = MemoryState {
        active_roots: first.active_roots.clone(),
        ..MemoryState::default()
    };
    for pred in &rest {
        state
            .active_roots
            .retain(|root| pred.active_roots.contains(root));
    }

    state.blocked_roots = first.blocked_roots.clone();
    for pred in &rest {
        state
            .blocked_roots
            .extend(pred.blocked_roots.iter().copied());
    }

    for root in state.active_roots.iter().copied() {
        if state.blocked_roots.contains(&root) {
            continue;
        }
        let mut initialized = first
            .initialized_leaves
            .get(&root)
            .cloned()
            .unwrap_or_default();
        for pred in &rest {
            if let Some(pred_initialized) = pred.initialized_leaves.get(&root) {
                initialized.retain(|leaf| pred_initialized.contains(leaf));
            } else {
                initialized.clear();
            }
        }
        state.initialized_leaves.insert(root, initialized);
    }

    for slices in relevant_slices.values() {
        for &slice in slices {
            if !state.active_roots.contains(&slice.root)
                || state.blocked_roots.contains(&slice.root)
            {
                continue;
            }
            let Some(first_carrier) = first.carriers.get(&slice).copied() else {
                continue;
            };
            let carrier = if rest
                .iter()
                .all(|pred| pred.carriers.get(&slice).copied() == Some(first_carrier))
            {
                first_carrier
            } else {
                MemoryCarrier::Token {
                    token: ObjectMemToken::Phi { block, slice },
                    slice,
                }
            };
            state.carriers.insert(slice, carrier);
        }
    }

    state
}

fn transfer_inst(
    ctx: &TransferCtx<'_>,
    inst: InstId,
    state: &mut MemoryState,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    if let Some(call) =
        downcast::<&control_flow::Call>(ctx.func.inst_set(), ctx.func.dfg.inst(inst))
    {
        apply_call_transfer(ctx, inst, call, state, record);
        activate_defined_root(ctx.func, inst, ctx.tracked, ctx.relevant_slices, state);
        return;
    }

    activate_defined_root(ctx.func, inst, ctx.tracked, ctx.relevant_slices, state);

    if let Some(obj_load) = downcast::<&data::ObjLoad>(ctx.func.inst_set(), ctx.func.dfg.inst(inst))
    {
        record_read_state(inst, ctx.tracked[*obj_load.object()], state, record);
        return;
    }

    if let Some(enum_get_tag) =
        downcast::<&data::EnumGetTag>(ctx.func.inst_set(), ctx.func.dfg.inst(inst))
    {
        let tracked_tag = ctx.tracked[*enum_get_tag.object()]
            .as_ref()
            .copied()
            .and_then(TrackedObject::exact)
            .and_then(|slice| enum_tag_object_slice(ctx.func.ctx(), slice))
            .map(TrackedObject::Exact);
        record_read_state(inst, tracked_tag, state, record);
        return;
    }

    if downcast::<&data::EnumAssertVariantRef>(ctx.func.inst_set(), ctx.func.dfg.inst(inst))
        .is_some()
    {
        return;
    }

    if let Some(obj_store) =
        downcast::<&data::ObjStore>(ctx.func.inst_set(), ctx.func.dfg.inst(inst))
    {
        apply_exact_value_write(
            inst,
            ctx.tracked[*obj_store.object()],
            &ctx.possible_roots[*obj_store.object()],
            ctx.relevant_slices,
            *obj_store.value(),
            state,
            record,
        );
        return;
    }

    if let Some(enum_set_tag) =
        downcast::<&data::EnumSetTag>(ctx.func.inst_set(), ctx.func.dfg.inst(inst))
    {
        if let Some(tag_slice) = ctx.tracked[*enum_set_tag.object()]
            .as_ref()
            .copied()
            .and_then(TrackedObject::exact)
            .and_then(|slice| enum_tag_object_slice(ctx.func.ctx(), slice))
        {
            apply_unknown_slice_write(inst, tag_slice, ctx.relevant_slices, state, record);
        } else {
            block_possible_roots(
                state,
                &ctx.possible_roots[*enum_set_tag.object()],
                inst,
                record,
            );
        }
        return;
    }

    if let Some(enum_write_variant) =
        downcast::<&data::EnumWriteVariant>(ctx.func.inst_set(), ctx.func.dfg.inst(inst))
    {
        let Some(base_slice) = ctx.tracked[*enum_write_variant.object()]
            .as_ref()
            .copied()
            .and_then(TrackedObject::exact)
        else {
            block_possible_roots(
                state,
                &ctx.possible_roots[*enum_write_variant.object()],
                inst,
                record,
            );
            return;
        };

        if let Some(tag_slice) = enum_tag_object_slice(ctx.func.ctx(), base_slice) {
            apply_unknown_slice_write(inst, tag_slice, ctx.relevant_slices, state, record);
        }
        for (field_idx, &value) in enum_write_variant.values().iter().enumerate() {
            let Some(field_idx) = u32::try_from(field_idx).ok() else {
                continue;
            };
            let Some(field_slice) = enum_variant_field_object_slice(
                ctx.func.ctx(),
                base_slice,
                *enum_write_variant.variant(),
                field_idx,
            ) else {
                continue;
            };
            apply_known_slice_write(inst, field_slice, value, ctx.relevant_slices, state, record);
        }
        return;
    }

    if downcast::<&data::ObjAlloc>(ctx.func.inst_set(), ctx.func.dfg.inst(inst)).is_some()
        || downcast::<&data::Gep>(ctx.func.inst_set(), ctx.func.dfg.inst(inst)).is_some()
        || downcast::<&cast::Bitcast>(ctx.func.inst_set(), ctx.func.dfg.inst(inst)).is_some()
        || downcast::<&data::ObjProj>(ctx.func.inst_set(), ctx.func.dfg.inst(inst)).is_some()
        || downcast::<&data::ObjIndex>(ctx.func.inst_set(), ctx.func.dfg.inst(inst)).is_some()
        || downcast::<&data::EnumProj>(ctx.func.inst_set(), ctx.func.dfg.inst(inst)).is_some()
        || downcast::<&control_flow::Phi>(ctx.func.inst_set(), ctx.func.dfg.inst(inst)).is_some()
    {
        return;
    }

    block_observed_roots(ctx.func, inst, ctx.possible_roots, state, record);
}

fn activate_defined_root(
    func: &Function,
    inst: InstId,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    relevant_slices: &FxHashMap<ValueId, Vec<ObjectSlice>>,
    state: &mut MemoryState,
) {
    let Some(result) = single_result_value(func, inst) else {
        return;
    };
    let Some(root_slice) = whole_root_slice_for_value(tracked, result) else {
        return;
    };
    if state.active_roots.contains(&root_slice.root) {
        return;
    }

    activate_root(
        state,
        root_slice,
        ObjectMemToken::Inst { inst },
        relevant_slices,
    );
    state.initialized_leaves.entry(root_slice.root).or_default();
}

fn record_read_state(
    inst: InstId,
    tracked_object: Option<TrackedObject>,
    state: &MemoryState,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    let Some(record) = record.as_deref_mut() else {
        return;
    };
    let Some(slice) = tracked_object.and_then(TrackedObject::exact) else {
        return;
    };
    if !state.active_roots.contains(&slice.root) || state.blocked_roots.contains(&slice.root) {
        return;
    }
    let Some(carrier) = state.carriers.get(&slice).copied() else {
        return;
    };

    let key = match carrier {
        MemoryCarrier::Value {
            value,
            slice: carrier_slice,
        } => ObjectReadGvnKey::ValueCarrier {
            value,
            carrier_slice,
            read_slice: slice,
        },
        MemoryCarrier::Token {
            token,
            slice: carrier_slice,
        } => ObjectReadGvnKey::Memory {
            token,
            carrier_slice,
            read_slice: slice,
        },
    };
    record.read_states.insert(
        inst,
        ObjectReadState {
            read_slice: slice,
            key,
            may_be_undef: !slice_is_fully_initialized(state, slice),
        },
    );
}

fn apply_exact_value_write(
    inst: InstId,
    tracked_object: Option<TrackedObject>,
    possible_roots: &FxHashSet<ValueId>,
    relevant_slices: &FxHashMap<ValueId, Vec<ObjectSlice>>,
    value: ValueId,
    state: &mut MemoryState,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    if let Some(slice) = tracked_object.and_then(TrackedObject::exact) {
        apply_known_slice_write(inst, slice, value, relevant_slices, state, record);
    } else {
        block_possible_roots(state, possible_roots, inst, record);
    }
}

fn apply_known_slice_write(
    inst: InstId,
    slice: ObjectSlice,
    value: ValueId,
    relevant_slices: &FxHashMap<ValueId, Vec<ObjectSlice>>,
    state: &mut MemoryState,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    if !state.active_roots.contains(&slice.root) || state.blocked_roots.contains(&slice.root) {
        return;
    }

    for &relevant in relevant_slices.get(&slice.root).into_iter().flatten() {
        if !slices_overlap(relevant, slice) {
            continue;
        }
        let carrier = if slice_is_covered_by(slice, relevant) {
            MemoryCarrier::Value { value, slice }
        } else {
            MemoryCarrier::Token {
                token: ObjectMemToken::Inst { inst },
                slice: relevant,
            }
        };
        state.carriers.insert(relevant, carrier);
    }
    mark_slice_initialized(state, slice);
    record_clobber(record, inst, ObjectClobber::Slice(slice));
}

fn apply_call_transfer(
    ctx: &TransferCtx<'_>,
    inst: InstId,
    call: &control_flow::Call,
    state: &mut MemoryState,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    let Some(summary) = ctx
        .object_effects
        .and_then(|effects| effects.get(call.callee()))
    else {
        block_observed_roots(ctx.func, inst, ctx.possible_roots, state, record);
        return;
    };

    for (idx, &arg) in call.args().iter().enumerate() {
        let Some(effect) = summary.arg_effects.get(idx) else {
            continue;
        };
        if effect.escapes || effect.materializes_heap {
            block_possible_roots(state, &ctx.possible_roots[arg], inst, record);
            continue;
        }

        if let Some(slice) = ctx.tracked[arg].and_then(TrackedObject::exact) {
            apply_slice_set_write(
                inst,
                slice,
                &effect.writes,
                ctx.relevant_slices,
                state,
                record,
            );
        } else if !effect.writes.is_empty() {
            block_possible_roots(state, &ctx.possible_roots[arg], inst, record);
        }
    }
}

fn apply_slice_set_write(
    inst: InstId,
    base_slice: ObjectSlice,
    writes: &SliceSet,
    relevant_slices: &FxHashMap<ValueId, Vec<ObjectSlice>>,
    state: &mut MemoryState,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    if writes.is_empty()
        || !state.active_roots.contains(&base_slice.root)
        || state.blocked_roots.contains(&base_slice.root)
    {
        return;
    }

    if writes.is_whole_root() || base_slice.leaf_count != writes.total_leaves() {
        apply_unknown_slice_write(inst, base_slice, relevant_slices, state, record);
        return;
    }

    let Some(leaves) = writes.exact_leaves() else {
        apply_unknown_slice_write(inst, base_slice, relevant_slices, state, record);
        return;
    };

    for &relevant in relevant_slices.get(&base_slice.root).into_iter().flatten() {
        if !object_slice_overlaps_effect(relevant, base_slice, leaves) {
            continue;
        }
        state.carriers.insert(
            relevant,
            MemoryCarrier::Token {
                token: ObjectMemToken::Inst { inst },
                slice: relevant,
            },
        );
    }
    mark_effect_leaves_initialized(state, base_slice, leaves);
    record_clobber(
        record,
        inst,
        ObjectClobber::LeafSet {
            base_slice,
            leaves: leaves.clone(),
        },
    );
}

fn apply_unknown_slice_write(
    inst: InstId,
    slice: ObjectSlice,
    relevant_slices: &FxHashMap<ValueId, Vec<ObjectSlice>>,
    state: &mut MemoryState,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    for &relevant in relevant_slices.get(&slice.root).into_iter().flatten() {
        if !slices_overlap(relevant, slice) {
            continue;
        }
        let carrier_slice = if slice_is_covered_by(slice, relevant) {
            slice
        } else {
            relevant
        };
        state.carriers.insert(
            relevant,
            MemoryCarrier::Token {
                token: ObjectMemToken::Inst { inst },
                slice: carrier_slice,
            },
        );
    }
    mark_slice_initialized(state, slice);
    record_clobber(record, inst, ObjectClobber::Slice(slice));
}

fn activate_root(
    state: &mut MemoryState,
    root_slice: ObjectSlice,
    token: ObjectMemToken,
    relevant_slices: &FxHashMap<ValueId, Vec<ObjectSlice>>,
) {
    state.active_roots.insert(root_slice.root);
    for &relevant in relevant_slices.get(&root_slice.root).into_iter().flatten() {
        state.carriers.insert(
            relevant,
            MemoryCarrier::Token {
                token,
                slice: root_slice,
            },
        );
    }
}

fn block_possible_roots(
    state: &mut MemoryState,
    roots: &FxHashSet<ValueId>,
    inst: InstId,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    for &root in roots {
        state.blocked_roots.insert(root);
        record_clobber(record, inst, ObjectClobber::Root(root));
    }
}

fn block_observed_roots(
    func: &Function,
    inst: InstId,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    state: &mut MemoryState,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    for root in observed_roots(func, inst, possible_roots, &[]) {
        state.blocked_roots.insert(root);
        record_clobber(record, inst, ObjectClobber::Root(root));
    }
}

fn record_clobber(
    record: &mut Option<&mut ObjectMemoryAnalysis>,
    inst: InstId,
    clobber: ObjectClobber,
) {
    if let Some(record) = record.as_deref_mut() {
        record.clobbers.entry(inst).or_default().push(clobber);
    }
}

fn mark_slice_initialized(state: &mut MemoryState, slice: ObjectSlice) {
    state
        .initialized_leaves
        .entry(slice.root)
        .or_default()
        .extend(slice.first_leaf..slice.first_leaf + slice.leaf_count);
}

fn mark_effect_leaves_initialized(
    state: &mut MemoryState,
    base_slice: ObjectSlice,
    leaves: &FxHashSet<usize>,
) {
    state
        .initialized_leaves
        .entry(base_slice.root)
        .or_default()
        .extend(leaves.iter().map(|leaf| base_slice.first_leaf + *leaf));
}

fn slice_is_fully_initialized(state: &MemoryState, slice: ObjectSlice) -> bool {
    state
        .initialized_leaves
        .get(&slice.root)
        .is_some_and(|initialized| {
            (slice.first_leaf..slice.first_leaf + slice.leaf_count)
                .all(|leaf| initialized.contains(&leaf))
        })
}

fn single_result_value(func: &Function, inst: InstId) -> Option<ValueId> {
    let results = func.dfg.inst_results(inst);
    if results.len() == 1 {
        Some(results[0])
    } else {
        None
    }
}

fn observed_roots(
    func: &Function,
    inst: InstId,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    skip: &[ValueId],
) -> Vec<ValueId> {
    let skipped: FxHashSet<_> = skip.iter().copied().collect();
    let mut roots = FxHashSet::default();
    for value in func.dfg.inst(inst).collect_values() {
        if skipped.contains(&value) {
            continue;
        }
        for &root in &possible_roots[value] {
            roots.insert(root);
        }
    }
    roots.into_iter().collect()
}

fn clobber_overlaps_slice(effect: &ObjectClobber, slice: ObjectSlice) -> bool {
    match effect {
        ObjectClobber::Slice(effect_slice) => slices_overlap(*effect_slice, slice),
        ObjectClobber::LeafSet { base_slice, leaves } => {
            object_slice_overlaps_effect(slice, *base_slice, leaves)
        }
        ObjectClobber::Root(root) => *root == slice.root,
    }
}
