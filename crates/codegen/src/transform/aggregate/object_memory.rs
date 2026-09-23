use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, ValueId,
    inst::{control_flow, data, downcast},
};

use crate::loop_analysis::{Loop, LoopTree};

use super::{
    LocalObjectArgInfo, ObjectEffectSummaryMap, RootInit,
    object_access::{
        ObjectAccess, ObjectAccessFacts, ObjectGuard, ObjectInitializationSource, ObjectInstEffects,
    },
    object_initialization::{InitializedValue, value_initialization},
    object_tracking::{
        AggregateObjectFacts, ObjectSlice, TrackedObject, enum_tag_object_slice,
        whole_root_slice_for_value,
    },
    provenance::RootValue,
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

#[derive(Clone, Debug, PartialEq, Eq, Default)]
struct MemoryState {
    carriers: FxHashMap<ObjectSlice, MemoryCarrier>,
    initialized: FxHashMap<ValueId, InitializedValue>,
    // Loaded SSA values retain their initialization evidence after memory changes.
    initialized_values: FxHashMap<ValueId, InitializedValue>,
    active_roots: FxHashSet<ValueId>,
    blocked_roots: FxHashSet<ValueId>,
}

struct TransferCtx<'a> {
    func: &'a Function,
    tracked: &'a SecondaryMap<ValueId, Option<TrackedObject>>,
    accesses: &'a ObjectAccessFacts,
    effects: &'a FxHashMap<InstId, ObjectInstEffects>,
    relevant_slices: &'a FxHashMap<ValueId, Vec<ObjectSlice>>,
    promote_loaded_values: bool,
}

#[derive(Default)]
pub(crate) struct ObjectMemoryAnalysis {
    layout_cache: shape::AggregateLayoutCache,
    read_states: FxHashMap<InstId, ObjectReadState>,
    clobbers: FxHashMap<InstId, Vec<ObjectSlice>>,
    inst_pre_states: FxHashMap<InstId, MemoryState>,
    block_entry_states: SecondaryMap<BlockId, MemoryState>,
    promote_loaded_values: bool,
}

impl ObjectMemoryAnalysis {
    pub(crate) fn compute(
        &mut self,
        func: &Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
        object_effects: Option<&ObjectEffectSummaryMap>,
    ) {
        self.compute_internal(func, local_object_args, object_effects, None, false);
    }

    pub(crate) fn compute_with_loaded_value_carriers(
        &mut self,
        func: &Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
        object_effects: Option<&ObjectEffectSummaryMap>,
    ) {
        self.compute_internal(func, local_object_args, object_effects, None, true);
    }

    pub(crate) fn compute_with_facts(
        &mut self,
        func: &Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
        object_effects: Option<&ObjectEffectSummaryMap>,
        facts: &AggregateObjectFacts,
        promote_loaded_values: bool,
    ) {
        self.compute_internal(
            func,
            local_object_args,
            object_effects,
            Some(facts),
            promote_loaded_values,
        );
    }

    fn compute_internal(
        &mut self,
        func: &Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
        object_effects: Option<&ObjectEffectSummaryMap>,
        selected: Option<&AggregateObjectFacts>,
        promote_loaded_values: bool,
    ) {
        self.reset(promote_loaded_values);
        if !func
            .dfg
            .value_ids()
            .any(|value| func.dfg.value_ty(value).is_obj_ref(func.ctx()))
        {
            return;
        }
        let accesses = ObjectAccessFacts::new(func, object_effects);
        let tracked = if let Some(selected) = selected {
            accesses.tracked_for_roots(
                func,
                &selected.root_slices().keys().copied().collect(),
                &mut self.layout_cache,
            )
        } else {
            accesses.tracked(func, local_object_args, &mut self.layout_cache)
        };
        self.compute_from_accesses(func, local_object_args, object_effects, &accesses, &tracked);
    }

    fn reset(&mut self, promote_loaded_values: bool) {
        self.layout_cache.clear();
        self.read_states.clear();
        self.clobbers.clear();
        self.inst_pre_states.clear();
        self.block_entry_states.clear();
        self.promote_loaded_values = promote_loaded_values;
    }

    fn compute_from_accesses(
        &mut self,
        func: &Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
        object_effects: Option<&ObjectEffectSummaryMap>,
        accesses: &ObjectAccessFacts,
        tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    ) {
        let relevant_slices = collect_relevant_slices(func, tracked);
        if relevant_slices.is_empty() {
            return;
        }

        let effects: FxHashMap<_, _> = func
            .layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .map(|inst| (inst, accesses.effects(func, inst, object_effects)))
            .collect();
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let reachable = cfg.reachable_blocks();
        let order: Vec<_> = cfg
            .post_order()
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        let initial_state = initial_state(
            func,
            local_object_args,
            tracked,
            &relevant_slices,
            self.promote_loaded_values,
        );
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
                        func,
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
                    tracked,
                    accesses,
                    effects: &effects,
                    relevant_slices: &relevant_slices,
                    promote_loaded_values: self.promote_loaded_values,
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
                tracked,
                accesses,
                effects: &effects,
                relevant_slices: &relevant_slices,
                promote_loaded_values: self.promote_loaded_values,
            };
            for inst in func.layout.iter_inst(block) {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                let mut record = Some(&mut *self);
                transfer_inst(&transfer_ctx, inst, &mut state, &mut record);
            }
        }
        self.block_entry_states = in_states;
    }

    pub(crate) fn read_state(&self, inst: InstId) -> Option<ObjectReadState> {
        self.read_states.get(&inst).copied()
    }

    pub(crate) fn value_matches_current_object_slice_before_inst(
        &self,
        inst: InstId,
        value: ValueId,
        slice: ObjectSlice,
    ) -> bool {
        self.inst_pre_states.get(&inst).is_some_and(|state| {
            state.active_roots.contains(&slice.root)
                && !state.blocked_roots.contains(&slice.root)
                && matches!(
                    state.carriers.get(&slice),
                    Some(MemoryCarrier::Value { value: current, .. }) if *current == value
                )
        })
    }

    pub(crate) fn guards_hold_before_inst(
        &self,
        func: &Function,
        inst: InstId,
        guards: &[ObjectGuard],
    ) -> bool {
        // Guard validity is separate from scalar definedness. A readable snapshot
        // containing undef can still share storage while its ancestor tags hold.
        guards.is_empty()
            || self.inst_pre_states.get(&inst).is_some_and(|state| {
                guards.iter().all(|guard| {
                    slice_initialization(func, state, guard.object).variant() == Some(guard.variant)
                })
            })
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
        // Facts established inside the loop cannot justify a preheader read.
        // This also checks ancestor enum guards in the sparse subtree state.
        if read.may_be_undef()
            || !slice_initialization(
                func,
                &self.block_entry_states[lpt.loop_header(lp)],
                read.read_slice(),
            )
            .defined(func.ctx())
        {
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
        // Clobbers already use the precise coordinates of each relevant read.
        self.clobbers
            .get(&inst)
            .is_some_and(|effects| effects.contains(&slice))
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
    seed_all_arg_roots: bool,
) -> MemoryState {
    let mut state = MemoryState::default();
    if seed_all_arg_roots {
        for (idx, &root) in func.arg_values.iter().enumerate() {
            let Some(root_slice) = whole_root_slice_for_value(tracked, root) else {
                continue;
            };
            let init = local_object_args
                .and_then(|args| args.get(&idx))
                .and_then(|info| info.init(func, idx))
                .unwrap_or(RootInit::LoadLiveIn);
            let token = match init {
                RootInit::LoadLiveIn => ObjectMemToken::LiveIn { root },
                RootInit::UndefFresh => ObjectMemToken::FreshEntry { root },
            };
            activate_root(&mut state, root_slice, token, relevant_slices);
            if init == RootInit::LoadLiveIn {
                mark_slice_initialized(
                    func,
                    &mut state,
                    root_slice,
                    InitializedValue::new(root_slice.ty, true),
                );
            } else {
                state
                    .initialized
                    .insert(root, InitializedValue::new(root_slice.ty, false));
            }
        }
        return state;
    }

    let Some(local_object_args) = local_object_args else {
        return state;
    };

    for (&idx, info) in local_object_args {
        let Some(init) = info.init(func, idx) else {
            continue;
        };
        let Some(&root) = func.arg_values.get(idx) else {
            continue;
        };
        let Some(root_slice) = whole_root_slice_for_value(tracked, root) else {
            continue;
        };
        let token = match init {
            RootInit::LoadLiveIn => ObjectMemToken::LiveIn { root },
            RootInit::UndefFresh => ObjectMemToken::FreshEntry { root },
        };
        activate_root(&mut state, root_slice, token, relevant_slices);
        if init == RootInit::LoadLiveIn {
            mark_slice_initialized(
                func,
                &mut state,
                root_slice,
                InitializedValue::new(root_slice.ty, true),
            );
        } else {
            state
                .initialized
                .insert(root, InitializedValue::new(root_slice.ty, false));
        }
    }

    state
}

fn meet_memory_states<'a>(
    func: &Function,
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
        initialized_values: first.initialized_values.clone(),
        ..MemoryState::default()
    };
    for pred in &rest {
        state.initialized_values.retain(|value, facts| {
            if let Some(other) = pred.initialized_values.get(value) {
                *facts = facts.join(func.ctx(), other);
                true
            } else {
                false
            }
        });
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
        if let Some(initialized) = first.initialized.get(&root)
            && let Some(initialized) = rest.iter().try_fold(initialized.clone(), |facts, pred| {
                Some(facts.join(func.ctx(), pred.initialized.get(&root)?))
            })
        {
            state.initialized.insert(root, initialized);
        }
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
    let data = ctx.func.dfg.inst(inst);
    let is = ctx.func.inst_set();
    let is_call = downcast::<&control_flow::Call>(is, data).is_some();
    if is_call || downcast::<&control_flow::Return>(is, data).is_some() {
        record_inst_pre_state(inst, state, record);
    }
    if !is_call {
        activate_defined_root(ctx, inst, state);
    }

    let read = if let Some(load) = downcast::<&data::ObjLoad>(is, data) {
        ctx.tracked[*load.object()]
    } else if let Some(tag) = downcast::<&data::EnumGetTag>(is, data) {
        ctx.tracked[*tag.object()]
            .and_then(TrackedObject::exact)
            .and_then(|slice| enum_tag_object_slice(ctx.func.ctx(), slice))
            .map(TrackedObject::Exact)
    } else {
        None
    };
    if let Some(read) = read {
        record_read_state(ctx.func, inst, Some(read), state, record);
        if let Some(result) = single_result_value(ctx.func, inst) {
            let facts = read
                .exact()
                .map(|slice| slice_initialization(ctx.func, state, slice))
                .unwrap_or_else(|| InitializedValue::new(ctx.func.dfg.value_ty(result), false));
            state.initialized_values.insert(result, facts);
        }

        if ctx.promote_loaded_values && downcast::<&data::ObjLoad>(is, data).is_some() {
            promote_loaded_value_to_carrier(ctx.func, inst, Some(read), state);
        }
    }

    let effects = &ctx.effects[&inst];
    for &(value, variant) in &effects.variant_assumptions {
        if ctx.func.dfg.value_ty(value).is_obj_ref(ctx.func.ctx()) {
            if let Some(slice) = ctx.tracked[value].and_then(TrackedObject::exact)
                && state.active_roots.contains(&slice.root)
                && !state.blocked_roots.contains(&slice.root)
            {
                let mut facts = slice_initialization(ctx.func, state, slice);
                facts.assume_variant(variant);
                mark_slice_initialized(ctx.func, state, slice, facts);
            }
        } else {
            let mut facts = value_initialization(
                ctx.func,
                value,
                &state.initialized_values,
                &mut shape::AggregateLayoutCache::default(),
            );
            facts.assume_variant(variant);
            state.initialized_values.insert(value, facts);
        }
    }
    if effects.writes.is_empty() && effects.unreadable.is_empty() {
        if is_call {
            activate_defined_root(ctx, inst, state);
        }
        return;
    }
    // Evaluate sources in the pre-write state, including partial/self copies.
    let mut layout = shape::AggregateLayoutCache::default();
    let initialized: Vec<_> = effects
        .initialization
        .iter()
        .map(|write| {
            let slice = ctx.accesses.write_slice(write.destination);
            let value = match write.source {
                ObjectInitializationSource::Intrinsic => InitializedValue::new(slice.ty, true),
                ObjectInitializationSource::Value(value) => {
                    value_initialization(ctx.func, value, &state.initialized_values, &mut layout)
                }
            };
            (write, value)
        })
        .collect();
    let preserved: Vec<_> = effects
        .tag_selections
        .iter()
        .filter_map(|&(projection, variant)| {
            let slice = ctx.accesses.projection_slice(projection);
            (ctx.accesses.single_instance(projection.root_value)
                && slice_initialization(ctx.func, state, slice).variant() == Some(variant))
            .then_some(slice)
        })
        .collect();
    let invalidated: Vec<_> = effects
        .writes
        .iter()
        .chain(effects.unreadable.iter().filter(|access| {
            !preserved.iter().any(|slice| {
                matches!(access, ObjectAccess::Exact(projection)
                    if projection.root_value.value() == slice.root
                        && projection.slice.first_leaf == slice.first_leaf
                        && projection.slice.leaf_count == slice.leaf_count)
            })
        }))
        .copied()
        .collect();

    // Writers need not be tracked, active, or eligible for value propagation.
    // Logical invalidation also breaks snapshot equality: restoring a tag does
    // not restore the old payload's readability, even if its bytes survived.
    for slices in ctx.relevant_slices.values() {
        for &slice in slices {
            if invalidated
                .iter()
                .any(|&write| ctx.accesses.may_overlap(write, slice))
            {
                record_clobber(record, inst, slice);
                if state.active_roots.contains(&slice.root)
                    && !state.blocked_roots.contains(&slice.root)
                {
                    state.carriers.insert(
                        slice,
                        MemoryCarrier::Token {
                            token: ObjectMemToken::Inst { inst },
                            slice,
                        },
                    );
                }
            }
        }
    }
    for (&root, value) in &mut state.initialized {
        let Some(root_slice) = whole_root_slice_for_value(ctx.tracked, root) else {
            continue;
        };
        for &access in &invalidated {
            if !ctx.accesses.may_overlap(access, root_slice) {
                continue;
            }
            if let ObjectAccess::Exact(projection) = access
                && projection.root_value.value() == root
            {
                value.forget(ctx.func.ctx(), projection.slice, &mut layout);
            } else {
                *value = InitializedValue::new(root_slice.ty, false);
            }
        }
    }
    for &(projection, variant) in &effects.tag_selections {
        let slice = ctx.accesses.projection_slice(projection);
        if state.active_roots.contains(&slice.root)
            && !state.blocked_roots.contains(&slice.root)
            && ctx.accesses.single_instance(projection.root_value)
        {
            let mut facts = slice_initialization(ctx.func, state, slice);
            facts.select(ctx.func.ctx(), variant);
            mark_slice_initialized(ctx.func, state, slice, facts);
        }
    }
    for (write, value) in initialized {
        let slice = ctx.accesses.write_slice(write.destination);
        if !state.active_roots.contains(&slice.root)
            || state.blocked_roots.contains(&slice.root)
            || !ctx.accesses.write_covers(write.destination, slice)
        {
            continue;
        }
        let defined = value.defined(ctx.func.ctx());
        mark_slice_initialized(ctx.func, state, slice, value);
        if defined && let ObjectInitializationSource::Value(value) = write.source {
            for &relevant in ctx.relevant_slices.get(&slice.root).into_iter().flatten() {
                if ctx.accesses.write_covers(write.destination, relevant) {
                    state
                        .carriers
                        .insert(relevant, MemoryCarrier::Value { value, slice });
                }
            }
        }
    }
    if is_call {
        activate_defined_root(ctx, inst, state);
    }
}

fn activate_defined_root(ctx: &TransferCtx<'_>, inst: InstId, state: &mut MemoryState) {
    let Some(result) = single_result_value(ctx.func, inst) else {
        return;
    };
    let Some(root_slice) = whole_root_slice_for_value(ctx.tracked, result) else {
        return;
    };
    if state.active_roots.contains(&root_slice.root) {
        return;
    }
    activate_root(
        state,
        root_slice,
        ObjectMemToken::Inst { inst },
        ctx.relevant_slices,
    );
    state
        .initialized
        .insert(root_slice.root, InitializedValue::new(root_slice.ty, false));
    if !ctx
        .accesses
        .single_instance(RootValue::new(root_slice.root))
    {
        state.blocked_roots.insert(root_slice.root);
    }
}

fn record_read_state(
    func: &Function,
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
            may_be_undef: !slice_initialization(func, state, slice).defined(func.ctx()),
        },
    );
}

fn record_inst_pre_state(
    inst: InstId,
    state: &MemoryState,
    record: &mut Option<&mut ObjectMemoryAnalysis>,
) {
    if let Some(record) = record.as_deref_mut() {
        record.inst_pre_states.insert(inst, state.clone());
    }
}

fn promote_loaded_value_to_carrier(
    func: &Function,
    inst: InstId,
    tracked_object: Option<TrackedObject>,
    state: &mut MemoryState,
) {
    let Some(result) = single_result_value(func, inst) else {
        return;
    };
    let Some(slice) = tracked_object.and_then(TrackedObject::exact) else {
        return;
    };
    if !state.active_roots.contains(&slice.root) || state.blocked_roots.contains(&slice.root) {
        return;
    }
    state.carriers.insert(
        slice,
        MemoryCarrier::Value {
            value: result,
            slice,
        },
    );
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

fn record_clobber(
    record: &mut Option<&mut ObjectMemoryAnalysis>,
    inst: InstId,
    clobber: ObjectSlice,
) {
    if let Some(record) = record.as_deref_mut() {
        record.clobbers.entry(inst).or_default().push(clobber);
    }
}

fn mark_slice_initialized(
    func: &Function,
    state: &mut MemoryState,
    slice: ObjectSlice,
    value: InitializedValue,
) {
    if let Some(root) = state.initialized.get_mut(&slice.root) {
        root.put(
            func.ctx(),
            shape::AggregateSlice {
                ty: slice.ty,
                first_leaf: slice.first_leaf,
                leaf_count: slice.leaf_count,
            },
            value,
            &mut shape::AggregateLayoutCache::default(),
        );
    } else {
        state.initialized.insert(slice.root, value);
    }
}

fn slice_initialization(
    func: &Function,
    state: &MemoryState,
    slice: ObjectSlice,
) -> InitializedValue {
    if !state.active_roots.contains(&slice.root) || state.blocked_roots.contains(&slice.root) {
        return InitializedValue::new(slice.ty, false);
    }
    state.initialized.get(&slice.root).map_or_else(
        || InitializedValue::new(slice.ty, false),
        |value| {
            value.at(
                func.ctx(),
                shape::AggregateSlice {
                    ty: slice.ty,
                    first_leaf: slice.first_leaf,
                    leaf_count: slice.leaf_count,
                },
                &mut shape::AggregateLayoutCache::default(),
            )
        },
    )
}

fn single_result_value(func: &Function, inst: InstId) -> Option<ValueId> {
    let results = func.dfg.inst_results(inst);
    if results.len() == 1 {
        Some(results[0])
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        domtree::DomTree,
        transform::aggregate::{
            collect_local_object_arg_info_with_effects, compute_object_effect_summaries,
        },
    };
    use sonatina_ir::{Module, module::FuncRef};
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    fn parse_test_module(src: &str) -> Module {
        let module = parse_module(src).expect("parse should succeed").module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(report.is_ok(), "{report}");
        module
    }

    fn lookup_func(module: &Module, name: &str) -> FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .expect("function should exist")
    }

    fn analyzed_read_key(module: &Module, func_name: &str) -> Option<ObjectReadGvnKey> {
        let object_effects = compute_object_effect_summaries(module);
        let local_object_args = collect_local_object_arg_info_with_effects(module, &object_effects);
        let func_ref = lookup_func(module, func_name);

        module.func_store.view(func_ref, |func| {
            let mut object_memory = ObjectMemoryAnalysis::default();
            object_memory.compute_with_loaded_value_carriers(
                func,
                local_object_args.get(&func_ref),
                Some(&object_effects),
            );

            let load_inst = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find(|&inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)).is_some()
                })
                .expect("function should contain an obj.load");
            object_memory
                .read_state(load_inst)
                .map(ObjectReadState::key)
        })
    }

    #[test]
    fn read_only_helper_call_preserves_value_carrier() {
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
    v4.i256 = call %peek v0;
    v3.i256 = obj.load v2;
    return v3;
}
"#,
        );

        assert!(
            matches!(
                analyzed_read_key(&module, "f"),
                Some(ObjectReadGvnKey::ValueCarrier { .. })
            ),
            "read-only helper summary should preserve the value carrier"
        );
    }

    #[test]
    fn stack_materialize_helper_call_blocks_value_carrier() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %write_ptr(v0.objref<@pair>, v1.i256) {
block0:
    v2.*@pair = obj.materialize.stack v0;
    v3.*i256 = gep v2 0.i64 0.i8;
    mstore v3 v1 i256;
    return;
}

func private %f(v0.objref<@pair>, v1.i256) -> i256 {
block0:
    v2.objref<i256> = obj.proj v0 0.i8;
    obj.store v2 1.i256;
    call %write_ptr v0 v1;
    v3.i256 = obj.load v2;
    return v3;
}
"#,
        );

        assert!(
            analyzed_read_key(&module, "f").is_none(),
            "stack-materializing helper summary should block tracked object reads entirely"
        );
    }

    fn check_memory(
        source: &str,
        selected_args: &[usize],
        check: impl FnOnce(&Function, &ObjectMemoryAnalysis, &[InstId]),
    ) {
        let module = parse_test_module(source);
        let summaries = compute_object_effect_summaries(&module);
        let selected = selected_args
            .iter()
            .map(|&index| (index, LocalObjectArgInfo::Borrowed))
            .collect();
        module.func_store.view(lookup_func(&module, "f"), |func| {
            let mut memory = ObjectMemoryAnalysis::default();
            memory.compute(func, Some(&selected), Some(&summaries));
            let loads: Vec<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .filter(|&inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)).is_some()
                })
                .collect();
            check(func, &memory, &loads);
        });
    }

    #[test]
    fn excluded_writer_invalidates_active_alias_and_records_clobber() {
        check_memory(
            r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    v2.i256 = obj.load v0;
    obj.store v1 22.i256;
    v3.i256 = obj.load v0;
    v4.i256 = add v2 v3;
    return v4;
}
"#,
            &[0],
            |func, memory, loads| {
                let before = memory.read_state(loads[0]).unwrap();
                let after = memory.read_state(loads[1]).unwrap();
                assert_ne!(before.key(), after.key());
                assert!(
                    after.may_be_undef(),
                    "an aliased coordinate does not prove initialization"
                );
                let store = func.layout.next_inst_of(loads[0]).unwrap();
                assert!(memory.inst_clobbers_slice(store, before.read_slice()));
            },
        );
    }

    #[test]
    fn conditional_call_neither_establishes_nor_preserves_initialization() {
        for initial in ["", "obj.store v1 11.i256;"] {
            check_memory(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
func private %maybe_write(v0.objref<i256>, v1.i1) {{
block0:
    br v1 block1 block2;
block1:
    obj.store v0 22.i256;
    jump block2;
block2:
    return;
}}
func private %f(v0.i1) -> i256 {{
block0:
    v1.objref<i256> = obj.alloc i256;
    {initial}
    call %maybe_write v1 v0;
    v2.i256 = obj.load v1;
    obj.store v1 33.i256;
    v3.i256 = obj.load v1;
    v4.i256 = add v2 v3;
    return v4;
}}
"#
                ),
                &[],
                |_, memory, loads| {
                    assert!(memory.read_state(loads[0]).unwrap().may_be_undef());
                    assert!(!memory.read_state(loads[1]).unwrap().may_be_undef());
                },
            );
        }
    }

    #[test]
    fn copied_load_keeps_its_own_initialization_snapshot() {
        for (initial, expected_undef) in [("", true), ("obj.store v0 11.i256;", false)] {
            check_memory(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
func private %f() -> i256 {{
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.objref<i256> = obj.alloc i256;
    {initial}
    v2.i256 = obj.load v0;
    obj.store v0 undef.i256;
    obj.store v1 v2;
    v3.i256 = obj.load v1;
    return v3;
}}
"#
                ),
                &[],
                |_, memory, loads| {
                    assert_eq!(
                        memory.read_state(loads[0]).unwrap().may_be_undef(),
                        expected_undef
                    );
                    assert_eq!(
                        memory.read_state(loads[1]).unwrap().may_be_undef(),
                        expected_undef
                    );
                },
            );
        }
    }

    #[test]
    fn sibling_write_preserves_read_key_initialization_and_clobber_precision() {
        check_memory(
            r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
func private %f(v0.objref<@Pair>) -> i256 {
block0:
    v1.objref<i256> = obj.proj v0 0.i8;
    v2.objref<i256> = obj.proj v0 1.i8;
    v3.i256 = obj.load v1;
    obj.store v2 22.i256;
    v4.i256 = obj.load v1;
    v5.i256 = add v3 v4;
    return v5;
}
"#,
            &[0],
            |func, memory, loads| {
                let before = memory.read_state(loads[0]).unwrap();
                let after = memory.read_state(loads[1]).unwrap();
                assert_eq!(before.key(), after.key());
                assert!(!after.may_be_undef());
                let store = func.layout.next_inst_of(loads[0]).unwrap();
                assert!(!memory.inst_clobbers_slice(store, before.read_slice()));
            },
        );
    }
    #[test]
    fn ambient_write_clobbers_incoming_but_preserves_private_fresh_memory() {
        for write in ["call %opaque;", "mstore 0.i256 22.i256 i256;"] {
            check_memory(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
declare external %opaque();
func private %f(v0.objref<i256>) -> i256 {{
block0:
    v1.objref<i256> = obj.alloc i256;
    obj.store v1 11.i256;
    v2.i256 = obj.load v0;
    v3.i256 = obj.load v1;
    {write}
    v4.i256 = obj.load v0;
    v5.i256 = obj.load v1;
    v6.i256 = add v2 v3;
    v7.i256 = add v4 v5;
    v8.i256 = add v6 v7;
    return v8;
}}
"#
                ),
                &[0],
                |_, memory, loads| {
                    let reads: Vec<_> = loads
                        .iter()
                        .map(|&load| memory.read_state(load).unwrap())
                        .collect();
                    assert_ne!(reads[0].key(), reads[2].key());
                    assert!(reads[2].may_be_undef());
                    assert_eq!(reads[1].key(), reads[3].key());
                    assert!(!reads[3].may_be_undef());
                },
            );
        }
    }

    #[test]
    fn loop_alias_write_blocks_invariance_but_sibling_write_does_not() {
        for (destination, invariant) in [("v1", false), ("v4", true)] {
            check_memory(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
type @Pair = {{ i256, i256 }};
func private %f(v0.objref<@Pair>, v1.objref<i256>, v2.i1) -> i256 {{
block0:
    v3.objref<i256> = obj.proj v0 0.i8;
    v4.objref<i256> = obj.proj v0 1.i8;
    jump block1;
block1:
    v5.i256 = obj.load v3;
    obj.store {destination} 22.i256;
    br v2 block1 block2;
block2:
    return v5;
}}
"#
                ),
                &[0],
                |func, memory, loads| {
                    let mut cfg = ControlFlowGraph::new();
                    cfg.compute(func);
                    let mut domtree = DomTree::new();
                    domtree.compute(&cfg);
                    let mut loops = LoopTree::new();
                    loops.compute(&cfg, &domtree);
                    let lp = loops.loops().next().unwrap();
                    assert_eq!(
                        memory.read_is_loop_invariant(func, &cfg, &loops, lp, loads[0]),
                        invariant
                    );
                },
            );
        }
    }
    #[test]
    fn repeating_allocation_site_does_not_supply_single_instance_read_facts() {
        check_memory(
            r#"
target = "evm-ethereum-osaka"
func private %f(v0.i1) -> i256 {
block0:
    jump block1;
block1:
    v1.objref<i256> = obj.alloc i256;
    obj.store v1 11.i256;
    v2.i256 = obj.load v1;
    br v0 block1 block2;
block2:
    return v2;
}
"#,
            &[],
            |_, memory, loads| {
                assert!(memory.read_state(loads[0]).is_none());
            },
        );
    }
    #[test]
    fn enum_tag_selection_preserves_only_the_same_active_payload() {
        for (variant, defined) in [("Some", true), ("Other", false), ("None", true)] {
            check_memory(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256), #Other(i256) }};
func private %observe(v0.objref<@Choice>) {{
block0:
    return;
}}
func private %f() {{
block0:
    v0.objref<@Choice> = obj.alloc @Choice;
    enum.write_variant v0 #Some (11.i256);
    enum.set_tag v0 #{variant};
    call %observe v0;
    return;
}}
"#
                ),
                &[],
                |func, memory, _| {
                    let call = func
                        .layout
                        .iter_block()
                        .flat_map(|b| func.layout.iter_inst(b))
                        .find(|&inst| {
                            downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                                .is_some()
                        })
                        .unwrap();
                    let state = &memory.inst_pre_states[&call];
                    assert_eq!(
                        state
                            .initialized
                            .values()
                            .next()
                            .unwrap()
                            .defined(func.ctx()),
                        defined
                    );
                },
            );
        }
    }

    #[test]
    fn enum_snapshot_copies_active_payload_without_requiring_inactive_slots() {
        check_memory(
            r#"
target = "evm-ethereum-osaka"
type @Choice = enum { #None, #Some(i256), #Other(i256) };
func private %f() -> @Choice {
block0:
    v0.objref<@Choice> = obj.alloc @Choice;
    v1.objref<@Choice> = obj.alloc @Choice;
    enum.write_variant v0 #Some (11.i256);
    v2.@Choice = obj.load v0;
    enum.set_tag v0 #Other;
    obj.store v1 v2;
    v3.@Choice = obj.load v1;
    return v3;
}
"#,
            &[],
            |_, memory, loads| {
                assert_eq!(loads.len(), 2);
                for &load in loads {
                    assert!(!memory.read_state(load).unwrap().may_be_undef());
                }
            },
        );
    }

    #[test]
    fn aggregate_construction_and_partial_snapshot_preserve_field_definedness() {
        for (field, undefined) in [("11.i256", false), ("undef.i256", true)] {
            check_memory(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
type @Pair = {{ i256, i256 }};
func private %f() -> i256 {{
block0:
    v0.objref<@Pair> = obj.alloc @Pair;
    v1.objref<@Pair> = obj.alloc @Pair;
    v2.@Pair = insert_value undef.@Pair 0.i8 {field};
    v3.@Pair = insert_value v2 1.i8 22.i256;
    obj.store v0 v3;
    v4.@Pair = obj.load v0;
    obj.store v0 undef.@Pair;
    obj.store v1 v4;
    v5.objref<i256> = obj.proj v1 0.i8;
    v6.objref<i256> = obj.proj v1 1.i8;
    v7.i256 = obj.load v5;
    v8.i256 = obj.load v6;
    v9.i256 = add v7 v8;
    return v9;
}}
"#
                ),
                &[],
                |_, memory, loads| {
                    assert_eq!(
                        memory.read_state(loads[0]).unwrap().may_be_undef(),
                        undefined
                    );
                    assert_eq!(
                        memory.read_state(loads[1]).unwrap().may_be_undef(),
                        undefined
                    );
                    assert!(!memory.read_state(loads[2]).unwrap().may_be_undef());
                },
            );
        }
    }

    #[test]
    fn scalar_computation_from_defined_field_ignores_undefined_sibling() {
        check_memory(
            r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
func private %f() -> i256 {
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.@Pair = insert_value undef.@Pair 0.i8 11.i256;
    v2.i256 = extract_value v1 0.i8;
    v3.i256 = add v2 1.i256;
    obj.store v0 v3;
    v4.i256 = obj.load v0;
    return v4;
}
"#,
            &[],
            |_, memory, loads| {
                assert!(!memory.read_state(loads[0]).unwrap().may_be_undef());
            },
        );
    }

    #[test]
    fn million_element_array_initialization_uses_sparse_subtrees() {
        check_memory(
            r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<[i256; 1000000]>) -> i256 {
block0:
    v1.objref<i256> = obj.index v0 123456.i256;
    v2.objref<i256> = obj.index v0 999999.i256;
    obj.store v1 undef.i256;
    v3.i256 = obj.load v1;
    v4.i256 = obj.load v2;
    v5.i256 = add v3 v4;
    return v5;
}
"#,
            &[0],
            |_, memory, loads| {
                assert!(memory.read_state(loads[0]).unwrap().may_be_undef());
                assert!(!memory.read_state(loads[1]).unwrap().may_be_undef());
            },
        );
    }
    #[test]
    fn variant_assertion_refines_tag_without_defining_scalar_payload() {
        for (allocate, args, selected, undefined) in [
            ("v0.objref<@Choice> = obj.alloc @Choice;", "", &[][..], true),
            ("", "v0.objref<@Choice>", &[0][..], false),
        ] {
            check_memory(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256) }};
func private %f({args}) -> i256 {{
block0:
    {allocate}
    v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.i256 = obj.load v2;
    return v3;
}}
"#
                ),
                selected,
                |func, memory, loads| {
                    let read = memory.read_state(loads[0]).unwrap();
                    assert_eq!(read.may_be_undef(), undefined);
                    let assertion = func
                        .layout
                        .iter_block()
                        .flat_map(|b| func.layout.iter_inst(b))
                        .find(|&inst| {
                            downcast::<&data::EnumAssertVariantRef>(
                                func.inst_set(),
                                func.dfg.inst(inst),
                            )
                            .is_some()
                        })
                        .unwrap();
                    assert!(!memory.inst_clobbers_slice(assertion, read.read_slice()));
                },
            );
        }
    }

    #[test]
    fn variant_value_assumption_does_not_define_undefined_scalar() {
        for (payload, undefined) in [("11.i256", false), ("undef.i256", true)] {
            check_memory(
                &format!(
                    r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256) }};
func private %f() -> i256 {{
block0:
    v0.@Choice = enum.make @Choice #Some ({payload});
    enum.assert_variant v0 #Some;
    v1.i256 = enum.extract v0 #Some 0.i8;
    v2.objref<i256> = obj.alloc i256;
    obj.store v2 v1;
    v3.i256 = obj.load v2;
    return v3;
}}
"#
                ),
                &[],
                |_, memory, loads| {
                    assert_eq!(
                        memory.read_state(loads[0]).unwrap().may_be_undef(),
                        undefined
                    );
                },
            );
        }
    }

    #[test]
    fn different_initialized_variants_join_as_a_defined_enum() {
        check_memory(
            r#"
target = "evm-ethereum-osaka"
type @Choice = enum { #None, #Some(i256), #Other(i256) };
func private %f(v0.i1) -> @Choice {
block0:
    v1.objref<@Choice> = obj.alloc @Choice;
    br v0 block1 block2;
block1:
    enum.write_variant v1 #Some (11.i256);
    jump block3;
block2:
    enum.write_variant v1 #Other (22.i256);
    jump block3;
block3:
    v2.@Choice = obj.load v1;
    return v2;
}
"#,
            &[],
            |_, memory, loads| {
                assert!(!memory.read_state(loads[0]).unwrap().may_be_undef());
            },
        );
    }
    #[test]
    fn trusted_variant_assumption_does_not_initialize_an_undefined_tag() {
        check_memory(
            r#"
target = "evm-ethereum-osaka"
type @Choice = enum { #None, #Some(i256) };
func private %f() -> enumtag(@Choice) {
block0:
    v0.objref<@Choice> = obj.alloc @Choice;
    v1.objref<@Choice> = enum.assert_variant_ref v0 #None;
    v2.enumtag(@Choice) = enum.get_tag v1;
    return v2;
}
"#,
            &[],
            |func, memory, _| {
                let tag = func
                    .layout
                    .iter_block()
                    .flat_map(|b| func.layout.iter_inst(b))
                    .find(|&inst| {
                        downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst))
                            .is_some()
                    })
                    .unwrap();
                assert!(memory.read_state(tag).unwrap().may_be_undef());
            },
        );
    }
    #[test]
    fn value_analysis_limit_keeps_initialization_conservative() {
        let inserts: String = (2..=300)
            .map(|index| {
                let previous = index - 1;
                format!("    v{index}.@Pair = insert_value v{previous} 0.i8 11.i256;\n")
            })
            .collect();
        check_memory(
            &format!(
                r#"
target = "evm-ethereum-osaka"
type @Pair = {{ i256, i256 }};
func private %f() -> @Pair {{
block0:
    v0.objref<@Pair> = obj.alloc @Pair;
    v1.@Pair = insert_value undef.@Pair 0.i8 11.i256;
{inserts}
    v301.@Pair = insert_value v300 1.i8 22.i256;
    obj.store v0 v301;
    v302.@Pair = obj.load v0;
    return v302;
}}
"#
            ),
            &[],
            |_, memory, loads| {
                assert!(memory.read_state(loads[0]).unwrap().may_be_undef());
            },
        );
    }
}
