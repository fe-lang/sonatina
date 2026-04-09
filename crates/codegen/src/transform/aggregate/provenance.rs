//! Root provenance keeps one internal fact table and exposes two semantic views:
//!
//! - `CompleteProvenance` is for proof-grade consumers that must reject incomplete
//!   provenance. It is used by `object_abi`, `object_tracking`, `scalarize`, and
//!   return classification in `object_effects`.
//! - `MayProvenance` is for conservative analyses that may still observe known
//!   roots when unknown contributors exist. It is used by `object_load_store`
//!   and `object_memory`.
//!
//! Mixed consumers such as `object_effects` receive both views through a
//! domain-specific adapter instead of querying raw provenance facts directly.

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, Type, ValueId,
    cfg::ControlFlowGraph,
    inst::{cast, control_flow, data, downcast},
    module::ModuleCtx,
    types::CompoundType,
};

use super::{ObjectEffectSummaryMap, ObjectReturnEffect, SliceSet, shape};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RootCaptureSource {
    dst_slice: shape::AggregateSlice,
    src_root: Option<ValueId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Projection {
    pub root_value: ValueId,
    pub slice: shape::AggregateSlice,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct KnownRoots<'a>(&'a FxHashSet<ValueId>);

impl<'a> KnownRoots<'a> {
    pub(crate) fn iter(self) -> impl Iterator<Item = ValueId> + 'a {
        self.0.iter().copied()
    }

    pub(crate) fn contains(self, root: ValueId) -> bool {
        self.0.contains(&root)
    }

    pub(crate) fn len(self) -> usize {
        self.0.len()
    }

    pub(crate) fn is_empty(self) -> bool {
        self.0.is_empty()
    }
}

#[derive(Default)]
pub(crate) struct ProvenanceFacts {
    exact: SecondaryMap<ValueId, Option<Projection>>,
    possible_projections: SecondaryMap<ValueId, Vec<Projection>>,
    possible_roots: SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: SecondaryMap<ValueId, bool>,
}

#[derive(Clone, Copy)]
pub(crate) struct CompleteProvenance<'a> {
    facts: &'a ProvenanceFacts,
}

#[derive(Clone, Copy)]
pub(crate) struct MayProvenance<'a> {
    facts: &'a ProvenanceFacts,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CompleteRootSet<'a> {
    Single(ValueId),
    Multiple(KnownRoots<'a>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MayRootSet<'a> {
    KnownOnly(KnownRoots<'a>),
    KnownAndUnknown(KnownRoots<'a>),
}

impl<'a> MayRootSet<'a> {
    pub(crate) fn observed(self) -> KnownRoots<'a> {
        match self {
            Self::KnownOnly(roots) | Self::KnownAndUnknown(roots) => roots,
        }
    }

    pub(crate) fn exhaustive_known_roots(self) -> Option<KnownRoots<'a>> {
        match self {
            Self::KnownOnly(roots) => Some(roots),
            Self::KnownAndUnknown(_) => None,
        }
    }

    pub(crate) fn has_unknown(self) -> bool {
        matches!(self, Self::KnownAndUnknown(_))
    }
}

pub(crate) struct ExactProjectionMap(SecondaryMap<ValueId, Option<Projection>>);

impl ExactProjectionMap {
    pub(crate) fn get(&self, value: ValueId) -> Option<Projection> {
        self.0[value]
    }

    pub(crate) fn clear(&mut self, value: ValueId) {
        self.set(value, None);
    }

    pub(crate) fn set(&mut self, value: ValueId, projection: Option<Projection>) {
        self.0[value] = projection;
    }
}

impl ProvenanceFacts {
    pub(crate) fn complete(&self) -> CompleteProvenance<'_> {
        CompleteProvenance { facts: self }
    }

    pub(crate) fn may(&self) -> MayProvenance<'_> {
        MayProvenance { facts: self }
    }

    pub(crate) fn into_exact_projection_map(mut self) -> ExactProjectionMap {
        for value in self.exact.keys() {
            if self.maybe_unknown[value] {
                self.exact[value] = None;
            }
        }
        ExactProjectionMap(self.exact)
    }
}

impl<'a> CompleteProvenance<'a> {
    pub(crate) fn exact_projection(self, value: ValueId) -> Option<Projection> {
        if self.facts.maybe_unknown[value] {
            return None;
        }
        self.facts.exact[value]
    }

    pub(crate) fn exact_root_slice(self, root: ValueId) -> Option<shape::AggregateSlice> {
        let projection = self.exact_projection(root)?;
        (projection.root_value == root).then_some(projection.slice)
    }

    pub(crate) fn root_set(self, value: ValueId) -> Option<CompleteRootSet<'a>> {
        if self.facts.maybe_unknown[value] {
            return None;
        }

        let roots = KnownRoots(&self.facts.possible_roots[value]);
        if roots.is_empty() {
            None
        } else if roots.len() == 1 {
            Some(CompleteRootSet::Single(
                roots
                    .iter()
                    .next()
                    .expect("singleton root set must have an element"),
            ))
        } else {
            Some(CompleteRootSet::Multiple(roots))
        }
    }

    pub(crate) fn possible_projections(self, value: ValueId) -> Option<&'a [Projection]> {
        if self.facts.maybe_unknown[value] {
            return None;
        }
        Some(&self.facts.possible_projections[value])
    }
}

impl<'a> MayProvenance<'a> {
    pub(crate) fn root_set(self, value: ValueId) -> MayRootSet<'a> {
        let roots = KnownRoots(&self.facts.possible_roots[value]);
        if self.facts.maybe_unknown[value] {
            MayRootSet::KnownAndUnknown(roots)
        } else {
            MayRootSet::KnownOnly(roots)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExactState {
    Unknown,
    Exact(Projection),
    Blocked,
}

#[derive(Clone, Copy)]
struct CaptureStateView<'a> {
    exact_states: &'a SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &'a SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &'a SecondaryMap<ValueId, bool>,
    root_slices: &'a FxHashMap<ValueId, shape::AggregateSlice>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct RootTransfer {
    roots: FxHashSet<ValueId>,
    maybe_unknown: bool,
}

pub(crate) fn collect_root_provenance(
    func: &Function,
    module: &ModuleCtx,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
    layout_cache: &mut shape::AggregateLayoutCache,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> ProvenanceFacts {
    let mut provenance = ProvenanceFacts::default();
    let mut exact_states = SecondaryMap::default();

    for (&root_value, &slice) in root_slices {
        provenance.possible_roots[root_value].insert(root_value);
        exact_states[root_value] = Some(ExactState::Exact(Projection { root_value, slice }));
    }

    compute_possible_roots(
        func,
        &mut provenance.possible_roots,
        &mut provenance.maybe_unknown,
        object_effects,
    );
    let value_sccs = compute_supported_value_sccs(func, root_slices);

    loop {
        let mut changed = false;

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }

                let Some(result) = single_result_value(func, inst) else {
                    continue;
                };

                let next = if let Some(&slice) = root_slices.get(&result) {
                    ExactState::Exact(Projection {
                        root_value: result,
                        slice,
                    })
                } else if let Some(projection) =
                    fresh_call_root_projection(func, result, inst, object_effects, layout_cache)
                {
                    ExactState::Exact(projection)
                } else {
                    derive_exact_state(
                        func,
                        module,
                        inst,
                        result,
                        &exact_states,
                        &provenance.possible_roots,
                        &provenance.maybe_unknown,
                        &value_sccs,
                        layout_cache,
                        object_effects,
                    )
                };

                let current = exact_states[result].unwrap_or(ExactState::Unknown);
                if current == ExactState::Blocked || current == next {
                    continue;
                }
                exact_states[result] = Some(next);
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    for value in func.dfg.value_ids() {
        provenance.exact[value] = match exact_states[value].unwrap_or(ExactState::Unknown) {
            ExactState::Exact(projection) if !provenance.maybe_unknown[value] => Some(projection),
            ExactState::Unknown | ExactState::Blocked => None,
            ExactState::Exact(_) => None,
        };
    }

    refine_possible_roots_from_objref_loads(
        func,
        root_slices,
        &exact_states,
        &mut provenance.possible_roots,
        &mut provenance.maybe_unknown,
        object_effects,
    );

    provenance.possible_projections = collect_possible_projections(
        func,
        module,
        root_slices,
        &provenance.possible_roots,
        &provenance.maybe_unknown,
        &exact_states,
        layout_cache,
        object_effects,
    );

    provenance
}

#[allow(clippy::too_many_arguments)]
fn collect_possible_projections(
    func: &Function,
    module: &ModuleCtx,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    layout_cache: &mut shape::AggregateLayoutCache,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> SecondaryMap<ValueId, Vec<Projection>> {
    let mut possible_projections = SecondaryMap::<ValueId, Vec<Projection>>::default();

    for (&root_value, &slice) in root_slices {
        possible_projections[root_value].push(Projection { root_value, slice });
    }

    for value in func.dfg.value_ids() {
        if let Some(projection) = exact_projection_of(exact_states, maybe_unknown, value) {
            possible_projections[value].push(projection);
        }
    }

    loop {
        let mut changed = false;

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }

                let Some(result) = single_result_value(func, inst) else {
                    continue;
                };
                let next = if let Some(projection) =
                    exact_projection_of(exact_states, maybe_unknown, result)
                {
                    vec![projection]
                } else {
                    derive_possible_projections(
                        func,
                        module,
                        inst,
                        result,
                        &possible_projections,
                        possible_roots,
                        maybe_unknown,
                        layout_cache,
                        object_effects,
                    )
                };

                if next != possible_projections[result] {
                    possible_projections[result] = next;
                    changed = true;
                }
            }
        }

        if !changed {
            return possible_projections;
        }
    }
}

fn compute_possible_roots(
    func: &Function,
    possible_roots: &mut SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &mut SecondaryMap<ValueId, bool>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) {
    loop {
        let mut changed = false;

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }

                let Some(updated) = possible_root_transfer(
                    func,
                    inst,
                    possible_roots,
                    maybe_unknown,
                    object_effects,
                ) else {
                    continue;
                };
                let Some(result) = single_result_value(func, inst) else {
                    continue;
                };

                if updated.roots != possible_roots[result]
                    || updated.maybe_unknown != maybe_unknown[result]
                {
                    possible_roots[result] = updated.roots;
                    maybe_unknown[result] = updated.maybe_unknown;
                    changed = true;
                }
            }
        }

        if !changed {
            break;
        }
    }
}

fn refine_possible_roots_from_objref_loads(
    func: &Function,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &mut SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &mut SecondaryMap<ValueId, bool>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) {
    let mut cfg = ControlFlowGraph::default();
    cfg.compute(func);
    let reachable = cfg.reachable_blocks();

    loop {
        let mut changed = false;
        let possible_roots_snapshot = possible_roots.clone();
        let maybe_unknown_snapshot = maybe_unknown.clone();
        let capture_state = CaptureStateView {
            exact_states,
            possible_roots: &possible_roots_snapshot,
            maybe_unknown: &maybe_unknown_snapshot,
            root_slices,
        };
        let block_entry_captures = compute_capture_states_for_blocks(
            func,
            capture_state,
            object_effects,
            &cfg,
            &reachable,
        );

        for block in func.layout.iter_block() {
            if !reachable[block] {
                continue;
            }

            let mut root_captures = block_entry_captures[block].clone();
            for inst in func.layout.iter_inst(block) {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }

                if let Some(updated) = possible_root_transfer(
                    func,
                    inst,
                    &possible_roots_snapshot,
                    &maybe_unknown_snapshot,
                    object_effects,
                ) && let Some(result) = single_result_value(func, inst)
                    && union_root_transfer(
                        &mut possible_roots[result],
                        &mut maybe_unknown[result],
                        &updated,
                    )
                {
                    changed = true;
                }

                if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                    && reference_element_ty(func.ctx(), func.dfg.value_ty(*obj_load.object()))
                        .is_some()
                    && let Some(result) = single_result_value(func, inst)
                {
                    let loaded_roots =
                        capture_roots_for_value(*obj_load.object(), capture_state, &root_captures);
                    if union_root_transfer(
                        &mut possible_roots[result],
                        &mut maybe_unknown[result],
                        &loaded_roots,
                    ) {
                        changed = true;
                    }
                }

                apply_inst_capture_transfer(
                    func,
                    inst,
                    capture_state,
                    object_effects,
                    &mut root_captures,
                );
            }
        }

        if !changed {
            return;
        }
    }
}

fn compute_capture_states_for_blocks(
    func: &Function,
    capture_state: CaptureStateView<'_>,
    object_effects: Option<&ObjectEffectSummaryMap>,
    cfg: &ControlFlowGraph,
    reachable: &SecondaryMap<BlockId, bool>,
) -> SecondaryMap<BlockId, FxHashMap<ValueId, Vec<RootCaptureSource>>> {
    let mut block_entry_captures = SecondaryMap::default();
    let mut block_exit_captures = SecondaryMap::default();

    loop {
        let mut changed = false;

        for block in func.layout.iter_block() {
            if !reachable[block] {
                continue;
            }

            let mut entry_captures = FxHashMap::default();
            for &pred in cfg.preds_of(block) {
                if reachable[pred] {
                    merge_root_capture_maps(&mut entry_captures, &block_exit_captures[pred]);
                }
            }
            dedup_root_capture_roots(&mut entry_captures);

            if block_entry_captures[block] != entry_captures {
                block_entry_captures[block] = entry_captures.clone();
                changed = true;
            }

            let mut exit_captures = entry_captures;
            for inst in func.layout.iter_inst(block) {
                apply_inst_capture_transfer(
                    func,
                    inst,
                    capture_state,
                    object_effects,
                    &mut exit_captures,
                );
            }
            dedup_root_capture_roots(&mut exit_captures);

            if block_exit_captures[block] != exit_captures {
                block_exit_captures[block] = exit_captures;
                changed = true;
            }
        }

        if !changed {
            return block_entry_captures;
        }
    }
}

fn apply_inst_capture_transfer(
    func: &Function,
    inst: InstId,
    capture_state: CaptureStateView<'_>,
    object_effects: Option<&ObjectEffectSummaryMap>,
    root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureSource>>,
) {
    if !func.layout.is_inst_inserted(inst) {
        return;
    }

    if let Some(obj_store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)) {
        kill_capture_access(root_captures, *obj_store.object(), None, capture_state);
        if reference_element_ty(func.ctx(), func.dfg.value_ty(*obj_store.value())).is_some() {
            record_root_capture_sources(
                root_captures,
                capture_destinations_for_value(*obj_store.object(), None, capture_state),
                &capture_state.possible_roots[*obj_store.value()],
                capture_state.maybe_unknown[*obj_store.value()],
            );
        }
        return;
    }

    if let Some(enum_set_tag) = downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst))
    {
        kill_capture_access(
            root_captures,
            *enum_set_tag.object(),
            Some((0, 1)),
            capture_state,
        );
        return;
    }

    if let Some(enum_write_variant) =
        downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst))
    {
        kill_capture_access(
            root_captures,
            *enum_write_variant.object(),
            None,
            capture_state,
        );
        record_enum_variant_capture_sources(
            func,
            root_captures,
            *enum_write_variant.object(),
            enum_write_variant.values(),
            *enum_write_variant.variant(),
            capture_state,
        );
        return;
    }

    if downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)).is_some() {
        merge_call_capture_roots(func, inst, capture_state, object_effects, root_captures);
    }
}

fn merge_call_capture_roots(
    func: &Function,
    inst: InstId,
    capture_state: CaptureStateView<'_>,
    object_effects: Option<&ObjectEffectSummaryMap>,
    root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureSource>>,
) {
    let call = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
        .expect("merge_call_capture_roots requires a call instruction");
    let Some(summary) = object_effects.and_then(|effects| effects.get(call.callee())) else {
        return;
    };

    for (idx, &arg) in call.args().iter().enumerate() {
        let Some(effect) = summary.arg_effects.get(idx) else {
            continue;
        };
        kill_capture_slice_set(root_captures, arg, &effect.writes, capture_state);
    }

    let call_result = single_result_value(func, inst);
    for capture in &summary.captures {
        let Some(&src_arg) = call.args().get(capture.src_arg) else {
            continue;
        };
        let dsts = match capture.dst {
            super::object_effects::ObjectCaptureDestination::Arg { index, slice } => call
                .args()
                .get(index)
                .map(|&dst_arg| capture_destinations_for_value(dst_arg, Some(slice), capture_state))
                .unwrap_or_default(),
            super::object_effects::ObjectCaptureDestination::Return { slice } => call_result
                .map(|result| capture_destinations_for_value(result, Some(slice), capture_state))
                .unwrap_or_default(),
        };
        record_root_capture_sources(
            root_captures,
            dsts,
            &capture_state.possible_roots[src_arg],
            capture_state.maybe_unknown[src_arg],
        );
    }
}

fn merge_root_capture_maps(
    dst: &mut FxHashMap<ValueId, Vec<RootCaptureSource>>,
    src: &FxHashMap<ValueId, Vec<RootCaptureSource>>,
) {
    for (&root, captures) in src {
        let entry = dst.entry(root).or_default();
        for &capture in captures {
            if entry.contains(&capture) {
                continue;
            }
            entry.push(capture);
        }
    }
}

fn dedup_root_capture_roots(root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureSource>>) {
    for captures in root_captures.values_mut() {
        let mut seen = FxHashSet::default();
        captures.retain(|capture| seen.insert(*capture));
    }
}

fn record_root_capture_sources(
    root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureSource>>,
    dsts: Vec<(ValueId, shape::AggregateSlice)>,
    src_roots: &FxHashSet<ValueId>,
    src_maybe_unknown: bool,
) {
    for (root, dst_slice) in dsts {
        for &src_root in src_roots {
            let entry = root_captures.entry(root).or_default();
            let capture = RootCaptureSource {
                dst_slice,
                src_root: Some(src_root),
            };
            if entry.contains(&capture) {
                continue;
            }
            entry.push(capture);
        }
        if src_maybe_unknown {
            let entry = root_captures.entry(root).or_default();
            let capture = RootCaptureSource {
                dst_slice,
                src_root: None,
            };
            if entry.contains(&capture) {
                continue;
            }
            entry.push(capture);
        }
    }
}

fn record_enum_variant_capture_sources(
    func: &Function,
    root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureSource>>,
    object: ValueId,
    values: &[ValueId],
    variant: sonatina_ir::types::EnumVariantRef,
    capture_state: CaptureStateView<'_>,
) {
    let Some(enum_ty) = reference_element_ty(func.ctx(), func.dfg.value_ty(object)) else {
        return;
    };
    for (field_idx, &value) in values.iter().enumerate() {
        if reference_element_ty(func.ctx(), func.dfg.value_ty(value)).is_none() {
            continue;
        }
        let Some(field_slice) = shape::enum_variant_field_slice(
            func.ctx(),
            enum_ty,
            variant,
            u32::try_from(field_idx).ok().unwrap_or(u32::MAX),
        ) else {
            continue;
        };
        record_root_capture_sources(
            root_captures,
            capture_destinations_for_value(object, Some(field_slice), capture_state),
            &capture_state.possible_roots[value],
            capture_state.maybe_unknown[value],
        );
    }
}

fn kill_capture_access(
    root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureSource>>,
    object: ValueId,
    relative_slice: Option<(usize, usize)>,
    capture_state: CaptureStateView<'_>,
) {
    let Some(projection) = exact_projection_of(
        capture_state.exact_states,
        capture_state.maybe_unknown,
        object,
    ) else {
        return;
    };
    let access_slice = relative_slice.map_or(projection.slice, |(first_leaf, leaf_count)| {
        shape::AggregateSlice {
            ty: projection.slice.ty,
            first_leaf: projection.slice.first_leaf + first_leaf,
            leaf_count,
        }
    });
    kill_capture_root_slice(root_captures, projection.root_value, Some(access_slice));
}

fn kill_capture_slice_set(
    root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureSource>>,
    value: ValueId,
    slices: &SliceSet,
    capture_state: CaptureStateView<'_>,
) {
    if slices.is_empty() {
        return;
    }
    let Some((root, base_slice)) = exact_capture_destination_for_value(value, None, capture_state)
    else {
        return;
    };
    if slices.is_whole_root() || base_slice.leaf_count != slices.total_leaves() {
        kill_capture_root_slice(root_captures, root, Some(base_slice));
        return;
    }
    let Some(exact_leaves) = slices.exact_leaves() else {
        kill_capture_root_slice(root_captures, root, Some(base_slice));
        return;
    };
    for &leaf in exact_leaves {
        kill_capture_root_slice(
            root_captures,
            root,
            Some(shape::AggregateSlice {
                ty: base_slice.ty,
                first_leaf: base_slice.first_leaf + leaf,
                leaf_count: 1,
            }),
        );
    }
}

fn kill_capture_root_slice(
    root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureSource>>,
    root: ValueId,
    access_slice: Option<shape::AggregateSlice>,
) {
    let Some(captures) = root_captures.get_mut(&root) else {
        return;
    };
    let Some(access_slice) = access_slice else {
        root_captures.remove(&root);
        return;
    };
    captures.retain(|capture| !slices_overlap_relative(access_slice, capture.dst_slice));
    if captures.is_empty() {
        root_captures.remove(&root);
    }
}

fn capture_destinations_for_value(
    value: ValueId,
    relative_slice: Option<shape::AggregateSlice>,
    capture_state: CaptureStateView<'_>,
) -> Vec<(ValueId, shape::AggregateSlice)> {
    if let Some((root, slice)) =
        exact_capture_destination_for_value(value, relative_slice, capture_state)
    {
        return vec![(root, slice)];
    }

    capture_state.possible_roots[value]
        .iter()
        .copied()
        .filter_map(|root| whole_root_projection(root, capture_state).map(|slice| (root, slice)))
        .collect()
}

fn exact_capture_destination_for_value(
    value: ValueId,
    relative_slice: Option<shape::AggregateSlice>,
    capture_state: CaptureStateView<'_>,
) -> Option<(ValueId, shape::AggregateSlice)> {
    // Capture state is a may-analysis, so strong updates are only sound when the
    // destination itself is exact. Multi-root, same-root-ambiguous, and
    // known-plus-unknown destinations must remain weak updates.
    let projection = exact_projection_of(
        capture_state.exact_states,
        capture_state.maybe_unknown,
        value,
    )?;
    let access_slice = relative_slice
        .map(|slice| offset_projection_slice(projection.slice, slice))
        .unwrap_or(Some(projection.slice))?;
    Some((projection.root_value, access_slice))
}

fn capture_roots_for_value(
    value: ValueId,
    capture_state: CaptureStateView<'_>,
    root_captures: &FxHashMap<ValueId, Vec<RootCaptureSource>>,
) -> RootTransfer {
    let mut transfer = RootTransfer {
        maybe_unknown: capture_state.maybe_unknown[value],
        ..RootTransfer::default()
    };
    for (root, access_slice) in capture_destinations_for_value(value, None, capture_state) {
        let Some(captures) = root_captures.get(&root) else {
            continue;
        };
        for capture in captures {
            if slices_overlap_relative(access_slice, capture.dst_slice) {
                if let Some(src_root) = capture.src_root {
                    transfer.roots.insert(src_root);
                } else {
                    transfer.maybe_unknown = true;
                }
            }
        }
    }
    transfer
}

fn whole_root_projection(
    root: ValueId,
    capture_state: CaptureStateView<'_>,
) -> Option<shape::AggregateSlice> {
    capture_state.root_slices.get(&root).copied().or_else(|| {
        exact_projection_of(
            capture_state.exact_states,
            capture_state.maybe_unknown,
            root,
        )
        .map(|projection| projection.slice)
    })
}

fn offset_projection_slice(
    base_slice: shape::AggregateSlice,
    relative_slice: shape::AggregateSlice,
) -> Option<shape::AggregateSlice> {
    (relative_slice.first_leaf + relative_slice.leaf_count <= base_slice.leaf_count).then_some(
        shape::AggregateSlice {
            ty: relative_slice.ty,
            first_leaf: base_slice.first_leaf + relative_slice.first_leaf,
            leaf_count: relative_slice.leaf_count,
        },
    )
}

fn union_root_set(dst: &mut FxHashSet<ValueId>, src: &FxHashSet<ValueId>) -> bool {
    let before = dst.len();
    dst.extend(src.iter().copied());
    dst.len() != before
}

fn union_root_transfer(
    dst_roots: &mut FxHashSet<ValueId>,
    dst_maybe_unknown: &mut bool,
    src: &RootTransfer,
) -> bool {
    let roots_changed = union_root_set(dst_roots, &src.roots);
    let unknown_changed = !*dst_maybe_unknown && src.maybe_unknown;
    *dst_maybe_unknown |= src.maybe_unknown;
    roots_changed || unknown_changed
}

fn slices_overlap_relative(lhs: shape::AggregateSlice, rhs: shape::AggregateSlice) -> bool {
    lhs.first_leaf < rhs.first_leaf + rhs.leaf_count
        && rhs.first_leaf < lhs.first_leaf + lhs.leaf_count
}

fn possible_root_transfer(
    func: &Function,
    inst: InstId,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> Option<RootTransfer> {
    if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)) {
        return gep.values().first().map(|base| RootTransfer {
            roots: possible_roots[*base].clone(),
            maybe_unknown: maybe_unknown[*base],
        });
    }

    if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(RootTransfer {
            roots: possible_roots[*bitcast.from()].clone(),
            maybe_unknown: maybe_unknown[*bitcast.from()],
        });
    }

    if let Some(obj_proj) = downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)) {
        return obj_proj.values().first().map(|base| RootTransfer {
            roots: possible_roots[*base].clone(),
            maybe_unknown: maybe_unknown[*base],
        });
    }

    if let Some(obj_index) = downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(RootTransfer {
            roots: possible_roots[*obj_index.object()].clone(),
            maybe_unknown: maybe_unknown[*obj_index.object()],
        });
    }

    if let Some(enum_proj) = downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(RootTransfer {
            roots: possible_roots[*enum_proj.object()].clone(),
            maybe_unknown: maybe_unknown[*enum_proj.object()],
        });
    }

    if let Some(enum_assert_ref) =
        downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst))
    {
        return Some(RootTransfer {
            roots: possible_roots[*enum_assert_ref.object()].clone(),
            maybe_unknown: maybe_unknown[*enum_assert_ref.object()],
        });
    }

    if let Some(call) = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)) {
        return call_return_root_transfer(
            func,
            inst,
            call,
            possible_roots,
            maybe_unknown,
            object_effects,
        );
    }

    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).map(|phi| {
        let mut transfer = RootTransfer::default();
        for &(arg, _) in phi.args() {
            transfer.roots.extend(possible_roots[arg].iter().copied());
            transfer.maybe_unknown |= maybe_unknown[arg];
        }
        transfer
    })
}

#[allow(clippy::too_many_arguments)]
fn derive_exact_state(
    func: &Function,
    module: &ModuleCtx,
    inst: InstId,
    result: ValueId,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    value_sccs: &FxHashMap<ValueId, usize>,
    layout_cache: &mut shape::AggregateLayoutCache,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> ExactState {
    if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)) {
        let Some(&base) = gep.values().first() else {
            return exact_state_or_unknown(exact_states, possible_roots, maybe_unknown, result);
        };
        let Some(base_projection) = exact_projection_of(exact_states, maybe_unknown, base) else {
            return pending_or_blocked(exact_states, base);
        };
        let Some(sub) = shape::aggregate_slice_for_gep_path(
            module,
            base_projection.slice.ty,
            &gep.values()[1..],
            &func.dfg,
        ) else {
            return ExactState::Blocked;
        };
        return ExactState::Exact(Projection {
            root_value: base_projection.root_value,
            slice: shape::AggregateSlice {
                ty: sub.ty,
                first_leaf: base_projection.slice.first_leaf + sub.first_leaf,
                leaf_count: sub.leaf_count,
            },
        });
    }

    if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)) {
        let source = *bitcast.from();
        let Some(source_projection) = exact_projection_of(exact_states, maybe_unknown, source)
        else {
            return pending_or_blocked(exact_states, source);
        };
        let Some(slice) = bitcast_projection_slice(
            layout_cache,
            module,
            source_projection.slice,
            func.dfg.value_ty(result),
        ) else {
            return ExactState::Blocked;
        };
        return ExactState::Exact(Projection {
            root_value: source_projection.root_value,
            slice,
        });
    }

    if let Some(obj_proj) = downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)) {
        let Some((&base, indices)) = obj_proj.values().split_first() else {
            return exact_state_or_unknown(exact_states, possible_roots, maybe_unknown, result);
        };
        let Some(base_projection) = exact_projection_of(exact_states, maybe_unknown, base) else {
            return pending_or_blocked(exact_states, base);
        };
        let Some(sub) = shape::aggregate_slice_for_object_path(
            module,
            base_projection.slice.ty,
            indices,
            &func.dfg,
        ) else {
            return ExactState::Blocked;
        };
        return ExactState::Exact(Projection {
            root_value: base_projection.root_value,
            slice: shape::AggregateSlice {
                ty: sub.ty,
                first_leaf: base_projection.slice.first_leaf + sub.first_leaf,
                leaf_count: sub.leaf_count,
            },
        });
    }

    if let Some(obj_index) = downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)) {
        let base = *obj_index.object();
        let Some(base_projection) = exact_projection_of(exact_states, maybe_unknown, base) else {
            return pending_or_blocked(exact_states, base);
        };
        let Some(sub) = shape::aggregate_slice_for_object_path(
            module,
            base_projection.slice.ty,
            &[*obj_index.index()],
            &func.dfg,
        ) else {
            return ExactState::Blocked;
        };
        return ExactState::Exact(Projection {
            root_value: base_projection.root_value,
            slice: shape::AggregateSlice {
                ty: sub.ty,
                first_leaf: base_projection.slice.first_leaf + sub.first_leaf,
                leaf_count: sub.leaf_count,
            },
        });
    }

    if let Some(enum_proj) = downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst)) {
        let base = *enum_proj.object();
        let Some(base_projection) = exact_projection_of(exact_states, maybe_unknown, base) else {
            return pending_or_blocked(exact_states, base);
        };
        let Some(field_idx) = shape::const_u32(&func.dfg, *enum_proj.field()) else {
            return ExactState::Blocked;
        };
        let Some(sub) = shape::enum_variant_field_slice(
            module,
            base_projection.slice.ty,
            *enum_proj.variant(),
            field_idx,
        ) else {
            return ExactState::Blocked;
        };
        return ExactState::Exact(Projection {
            root_value: base_projection.root_value,
            slice: shape::AggregateSlice {
                ty: sub.ty,
                first_leaf: base_projection.slice.first_leaf + sub.first_leaf,
                leaf_count: sub.leaf_count,
            },
        });
    }

    if let Some(enum_assert_ref) =
        downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst))
    {
        let base = *enum_assert_ref.object();
        let Some(base_projection) = exact_projection_of(exact_states, maybe_unknown, base) else {
            return pending_or_blocked(exact_states, base);
        };
        return ExactState::Exact(base_projection);
    }

    if let Some(call) = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)) {
        return derive_call_exact_state(
            func,
            inst,
            call,
            exact_states,
            possible_roots,
            maybe_unknown,
            layout_cache,
            object_effects,
        );
    }

    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).map_or(
        ExactState::Unknown,
        |phi| {
            derive_phi_state(
                func,
                result,
                phi,
                exact_states,
                possible_roots,
                maybe_unknown,
                value_sccs,
            )
        },
    )
}

#[allow(clippy::too_many_arguments)]
fn derive_possible_projections(
    func: &Function,
    module: &ModuleCtx,
    inst: InstId,
    result: ValueId,
    possible_projections: &SecondaryMap<ValueId, Vec<Projection>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    layout_cache: &mut shape::AggregateLayoutCache,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> Vec<Projection> {
    let Some(root_value) = singleton_root(possible_roots, maybe_unknown, result) else {
        return Vec::new();
    };

    if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)) {
        let Some(&base) = gep.values().first() else {
            return Vec::new();
        };
        return map_candidate_projections(possible_projections, base, |projection| {
            let sub = shape::aggregate_slice_for_gep_path(
                module,
                projection.slice.ty,
                &gep.values()[1..],
                &func.dfg,
            )?;
            Some(Projection {
                root_value: projection.root_value,
                slice: shape::AggregateSlice {
                    ty: sub.ty,
                    first_leaf: projection.slice.first_leaf + sub.first_leaf,
                    leaf_count: sub.leaf_count,
                },
            })
        });
    }

    if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)) {
        return map_candidate_projections(possible_projections, *bitcast.from(), |projection| {
            let slice = bitcast_projection_slice(
                layout_cache,
                module,
                projection.slice,
                func.dfg.value_ty(result),
            )?;
            Some(Projection {
                root_value: projection.root_value,
                slice,
            })
        });
    }

    if let Some(obj_proj) = downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)) {
        let Some((&base, indices)) = obj_proj.values().split_first() else {
            return Vec::new();
        };
        return map_candidate_projections(possible_projections, base, |projection| {
            let sub = shape::aggregate_slice_for_object_path(
                module,
                projection.slice.ty,
                indices,
                &func.dfg,
            )?;
            Some(Projection {
                root_value: projection.root_value,
                slice: shape::AggregateSlice {
                    ty: sub.ty,
                    first_leaf: projection.slice.first_leaf + sub.first_leaf,
                    leaf_count: sub.leaf_count,
                },
            })
        });
    }

    if let Some(obj_index) = downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)) {
        return map_candidate_projections(
            possible_projections,
            *obj_index.object(),
            |projection| {
                let sub = shape::aggregate_slice_for_object_path(
                    module,
                    projection.slice.ty,
                    &[*obj_index.index()],
                    &func.dfg,
                )?;
                Some(Projection {
                    root_value: projection.root_value,
                    slice: shape::AggregateSlice {
                        ty: sub.ty,
                        first_leaf: projection.slice.first_leaf + sub.first_leaf,
                        leaf_count: sub.leaf_count,
                    },
                })
            },
        );
    }

    if let Some(enum_proj) = downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst)) {
        let Some(field_idx) = shape::const_u32(&func.dfg, *enum_proj.field()) else {
            return Vec::new();
        };
        return map_candidate_projections(
            possible_projections,
            *enum_proj.object(),
            |projection| {
                let sub = shape::enum_variant_field_slice(
                    module,
                    projection.slice.ty,
                    *enum_proj.variant(),
                    field_idx,
                )?;
                Some(Projection {
                    root_value: projection.root_value,
                    slice: shape::AggregateSlice {
                        ty: sub.ty,
                        first_leaf: projection.slice.first_leaf + sub.first_leaf,
                        leaf_count: sub.leaf_count,
                    },
                })
            },
        );
    }

    if let Some(enum_assert_ref) =
        downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst))
    {
        return map_candidate_projections(possible_projections, *enum_assert_ref.object(), Some);
    }

    if let Some(call) = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)) {
        return derive_call_possible_projections(
            func,
            inst,
            result,
            call,
            possible_projections,
            possible_roots,
            maybe_unknown,
            root_value,
            layout_cache,
            object_effects,
        );
    }

    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst))
        .map(|phi| {
            derive_phi_projection_candidates(func, result, phi, possible_projections, root_value)
        })
        .unwrap_or_default()
}

fn derive_phi_state(
    func: &Function,
    result: ValueId,
    phi: &control_flow::Phi,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    value_sccs: &FxHashMap<ValueId, usize>,
) -> ExactState {
    if maybe_unknown[result] {
        return ExactState::Unknown;
    }
    let roots = &possible_roots[result];
    if roots.is_empty() {
        return ExactState::Unknown;
    }
    if roots.len() != 1 {
        return ExactState::Blocked;
    }
    let root_value = *roots
        .iter()
        .next()
        .expect("singleton root set must have an element");
    let result_scc = value_sccs.get(&result).copied();

    let mut candidate = None;
    for &(arg, _) in phi.args() {
        if maybe_unknown[arg] {
            return ExactState::Unknown;
        }
        let Some(projection) = exact_projection_of(exact_states, maybe_unknown, arg) else {
            if matches!(
                exact_states[arg].unwrap_or(ExactState::Unknown),
                ExactState::Blocked
            ) {
                return ExactState::Blocked;
            }
            continue;
        };
        if projection.root_value != root_value {
            return ExactState::Blocked;
        }
        match candidate {
            Some(existing) if existing != projection => return ExactState::Blocked,
            Some(_) => {}
            None => candidate = Some(projection),
        }
    }

    let Some(candidate) = candidate else {
        return ExactState::Unknown;
    };

    for &(arg, _) in phi.args() {
        match exact_states[arg].unwrap_or(ExactState::Unknown) {
            ExactState::Exact(projection) if projection == candidate => {}
            ExactState::Exact(_) | ExactState::Blocked => return ExactState::Blocked,
            ExactState::Unknown => {
                if possible_roots[arg].len() == 1
                    && possible_roots[arg].contains(&root_value)
                    && value_sccs.get(&arg).copied() == result_scc
                {
                    continue;
                }
                return ExactState::Unknown;
            }
        }
    }

    let result_ty = func.dfg.value_ty(result);
    if projection_value_ty_matches(result_ty, candidate.slice.ty, func.ctx()) {
        ExactState::Exact(candidate)
    } else {
        ExactState::Blocked
    }
}

fn derive_phi_projection_candidates(
    func: &Function,
    result: ValueId,
    phi: &control_flow::Phi,
    possible_projections: &SecondaryMap<ValueId, Vec<Projection>>,
    root_value: ValueId,
) -> Vec<Projection> {
    let result_ty = func.dfg.value_ty(result);
    let mut candidates = Vec::new();
    for &(arg, _) in phi.args() {
        for &projection in &possible_projections[arg] {
            if projection.root_value != root_value
                || !projection_value_ty_matches(result_ty, projection.slice.ty, func.ctx())
            {
                continue;
            }
            push_unique_projection(&mut candidates, projection);
        }
    }
    candidates
}

fn exact_projection_of(
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    value: ValueId,
) -> Option<Projection> {
    if maybe_unknown[value] {
        return None;
    }
    match exact_states[value].unwrap_or(ExactState::Unknown) {
        ExactState::Exact(projection) => Some(projection),
        ExactState::Unknown | ExactState::Blocked => None,
    }
}

fn exact_state_or_unknown(
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    value: ValueId,
) -> ExactState {
    if maybe_unknown[value] || possible_roots[value].is_empty() {
        ExactState::Unknown
    } else {
        exact_states[value].unwrap_or(ExactState::Unknown)
    }
}

fn pending_or_blocked(
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    source: ValueId,
) -> ExactState {
    match exact_states[source].unwrap_or(ExactState::Unknown) {
        ExactState::Blocked => ExactState::Blocked,
        ExactState::Unknown => ExactState::Unknown,
        ExactState::Exact(_) => unreachable!("exact source should have been handled earlier"),
    }
}

fn projection_value_ty_matches(value_ty: Type, projection_ty: Type, module: &ModuleCtx) -> bool {
    reference_element_ty(module, value_ty).is_some_and(|pointee| pointee == projection_ty)
}

fn compute_supported_value_sccs(
    func: &Function,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
) -> FxHashMap<ValueId, usize> {
    let mut nodes = FxHashSet::default();
    nodes.extend(root_slices.keys().copied());

    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if !func.layout.is_inst_inserted(inst) {
                continue;
            }
            if supported_value_deps(func, inst).is_some()
                && let Some(result) = single_result_value(func, inst)
            {
                nodes.insert(result);
            }
        }
    }

    let mut edges = FxHashMap::<ValueId, Vec<ValueId>>::default();
    let mut reverse_edges = FxHashMap::<ValueId, Vec<ValueId>>::default();
    for &node in &nodes {
        edges.entry(node).or_default();
        reverse_edges.entry(node).or_default();
    }

    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if !func.layout.is_inst_inserted(inst) {
                continue;
            }
            let Some(result) = single_result_value(func, inst) else {
                continue;
            };
            let Some(deps) = supported_value_deps(func, inst) else {
                continue;
            };

            for dep in deps {
                if !nodes.contains(&result) || !nodes.contains(&dep) {
                    continue;
                }
                edges.entry(result).or_default().push(dep);
                reverse_edges.entry(dep).or_default().push(result);
            }
        }
    }

    let mut visited = FxHashSet::default();
    let mut order = Vec::with_capacity(nodes.len());
    for &node in &nodes {
        dfs_postorder(node, &edges, &mut visited, &mut order);
    }

    let mut components = FxHashMap::default();
    let mut component_id = 0usize;
    while let Some(node) = order.pop() {
        if components.contains_key(&node) {
            continue;
        }
        assign_component(node, component_id, &reverse_edges, &mut components);
        component_id += 1;
    }

    components
}

fn supported_value_deps(func: &Function, inst: InstId) -> Option<Vec<ValueId>> {
    if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)) {
        return gep.values().first().copied().map(|base| vec![base]);
    }

    if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(vec![*bitcast.from()]);
    }

    if let Some(obj_proj) = downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)) {
        return obj_proj.values().first().copied().map(|base| vec![base]);
    }

    if let Some(obj_index) = downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(vec![*obj_index.object()]);
    }

    if let Some(enum_proj) = downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(vec![*enum_proj.object()]);
    }

    if let Some(enum_assert_ref) =
        downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst))
    {
        return Some(vec![*enum_assert_ref.object()]);
    }

    if let Some(call) = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(call.args().iter().copied().collect());
    }

    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst))
        .map(|phi| phi.args().iter().map(|(arg, _)| *arg).collect())
}

fn call_return_root_transfer(
    func: &Function,
    inst: InstId,
    call: &control_flow::Call,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> Option<RootTransfer> {
    let [result] = func.dfg.inst_results(inst) else {
        return None;
    };
    let Some(summary) = object_effects.and_then(|effects| effects.get(call.callee())) else {
        return reference_element_ty(func.ctx(), func.dfg.value_ty(*result)).map(|_| {
            RootTransfer {
                maybe_unknown: true,
                ..RootTransfer::default()
            }
        });
    };
    match summary.ret_effect {
        ObjectReturnEffect::SameAsArg { index } | ObjectReturnEffect::DerivedFromArg { index } => {
            call.args().get(index).map(|arg| RootTransfer {
                roots: possible_roots[*arg].clone(),
                maybe_unknown: maybe_unknown[*arg],
            })
        }
        ObjectReturnEffect::FreshObject => {
            let mut transfer = RootTransfer::default();
            transfer.roots.insert(*result);
            Some(transfer)
        }
        ObjectReturnEffect::None | ObjectReturnEffect::Unknown => {
            reference_element_ty(func.ctx(), func.dfg.value_ty(*result)).map(|_| RootTransfer {
                maybe_unknown: true,
                ..RootTransfer::default()
            })
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn derive_call_exact_state(
    func: &Function,
    inst: InstId,
    call: &control_flow::Call,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    layout_cache: &mut shape::AggregateLayoutCache,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> ExactState {
    let Some(result) = single_result_value(func, inst) else {
        return ExactState::Blocked;
    };
    let Some(summary) = object_effects.and_then(|effects| effects.get(call.callee())) else {
        return exact_state_or_unknown(exact_states, possible_roots, maybe_unknown, result);
    };

    match summary.ret_effect {
        ObjectReturnEffect::SameAsArg { index } => {
            let Some(&arg) = call.args().get(index) else {
                return ExactState::Blocked;
            };
            let Some(projection) = exact_projection_of(exact_states, maybe_unknown, arg) else {
                return pending_or_blocked(exact_states, arg);
            };
            if projection_value_ty_matches(
                func.dfg.value_ty(result),
                projection.slice.ty,
                func.ctx(),
            ) {
                ExactState::Exact(projection)
            } else {
                ExactState::Blocked
            }
        }
        ObjectReturnEffect::DerivedFromArg { index } => {
            let Some(&arg) = call.args().get(index) else {
                return ExactState::Blocked;
            };
            exact_state_or_unknown(exact_states, possible_roots, maybe_unknown, arg)
        }
        ObjectReturnEffect::FreshObject => {
            fresh_call_root_projection(func, result, inst, object_effects, layout_cache)
                .map_or(ExactState::Blocked, ExactState::Exact)
        }
        ObjectReturnEffect::None | ObjectReturnEffect::Unknown => {
            exact_state_or_unknown(exact_states, possible_roots, maybe_unknown, result)
        }
    }
}

fn fresh_call_root_projection(
    func: &Function,
    result: ValueId,
    inst: InstId,
    object_effects: Option<&ObjectEffectSummaryMap>,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> Option<Projection> {
    let call = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))?;
    if !matches!(
        object_effects
            .and_then(|effects| effects.get(call.callee()))
            .map(|summary| &summary.ret_effect),
        Some(ObjectReturnEffect::FreshObject)
    ) {
        return None;
    }
    let pointee_ty = reference_element_ty(func.ctx(), func.dfg.value_ty(result))?;
    Some(Projection {
        root_value: result,
        slice: shape::AggregateSlice {
            ty: pointee_ty,
            first_leaf: 0,
            leaf_count: layout_cache
                .shape(func.ctx(), pointee_ty)
                .map_or(1, |shape| shape.leaves.len()),
        },
    })
}

#[allow(clippy::too_many_arguments)]
fn derive_call_possible_projections(
    func: &Function,
    inst: InstId,
    result: ValueId,
    call: &control_flow::Call,
    possible_projections: &SecondaryMap<ValueId, Vec<Projection>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    root_value: ValueId,
    layout_cache: &mut shape::AggregateLayoutCache,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> Vec<Projection> {
    let Some(summary) = object_effects.and_then(|effects| effects.get(call.callee())) else {
        return Vec::new();
    };

    match summary.ret_effect {
        ObjectReturnEffect::SameAsArg { index } | ObjectReturnEffect::DerivedFromArg { index } => {
            let Some(&arg) = call.args().get(index) else {
                return Vec::new();
            };
            filter_projection_candidates(
                func,
                result,
                &possible_projections[arg],
                possible_roots,
                maybe_unknown,
                root_value,
            )
        }
        ObjectReturnEffect::FreshObject => {
            fresh_call_root_projection(func, result, inst, object_effects, layout_cache)
                .into_iter()
                .collect()
        }
        ObjectReturnEffect::None | ObjectReturnEffect::Unknown => Vec::new(),
    }
}

fn map_candidate_projections(
    possible_projections: &SecondaryMap<ValueId, Vec<Projection>>,
    value: ValueId,
    mut map: impl FnMut(Projection) -> Option<Projection>,
) -> Vec<Projection> {
    let mut projections = Vec::new();
    for &projection in &possible_projections[value] {
        let Some(mapped) = map(projection) else {
            continue;
        };
        push_unique_projection(&mut projections, mapped);
    }
    projections
}

fn filter_projection_candidates(
    func: &Function,
    result: ValueId,
    projections: &[Projection],
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    root_value: ValueId,
) -> Vec<Projection> {
    if maybe_unknown[result] {
        return Vec::new();
    }
    let result_ty = func.dfg.value_ty(result);
    let mut filtered = Vec::new();
    for &projection in projections {
        if projection.root_value != root_value
            || !possible_roots[result].contains(&projection.root_value)
            || !projection_value_ty_matches(result_ty, projection.slice.ty, func.ctx())
        {
            continue;
        }
        push_unique_projection(&mut filtered, projection);
    }
    filtered
}

fn singleton_root(
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    maybe_unknown: &SecondaryMap<ValueId, bool>,
    value: ValueId,
) -> Option<ValueId> {
    (!maybe_unknown[value] && possible_roots[value].len() == 1).then(|| {
        *possible_roots[value]
            .iter()
            .next()
            .expect("singleton root set must have an element")
    })
}

fn push_unique_projection(projections: &mut Vec<Projection>, projection: Projection) {
    if !projections.contains(&projection) {
        projections.push(projection);
    }
}

fn single_result_value(func: &Function, inst: InstId) -> Option<ValueId> {
    let [result] = func.dfg.inst_results(inst) else {
        return None;
    };
    Some(*result)
}

fn dfs_postorder(
    node: ValueId,
    edges: &FxHashMap<ValueId, Vec<ValueId>>,
    visited: &mut FxHashSet<ValueId>,
    order: &mut Vec<ValueId>,
) {
    if !visited.insert(node) {
        return;
    }

    if let Some(neighbors) = edges.get(&node) {
        for &neighbor in neighbors {
            dfs_postorder(neighbor, edges, visited, order);
        }
    }

    order.push(node);
}

fn assign_component(
    node: ValueId,
    component_id: usize,
    reverse_edges: &FxHashMap<ValueId, Vec<ValueId>>,
    components: &mut FxHashMap<ValueId, usize>,
) {
    if components.insert(node, component_id).is_some() {
        return;
    }

    if let Some(neighbors) = reverse_edges.get(&node) {
        for &neighbor in neighbors {
            if !components.contains_key(&neighbor) {
                assign_component(neighbor, component_id, reverse_edges, components);
            }
        }
    }
}

fn bitcast_projection_slice(
    layout_cache: &mut shape::AggregateLayoutCache,
    module: &ModuleCtx,
    slice: shape::AggregateSlice,
    ptr_ty: Type,
) -> Option<shape::AggregateSlice> {
    let pointee_ty = reference_element_ty(module, ptr_ty)?;
    projection_slice_can_view_as(layout_cache, module, slice, pointee_ty).then_some(
        shape::AggregateSlice {
            ty: pointee_ty,
            ..slice
        },
    )
}

fn reference_element_ty(module: &ModuleCtx, ty: Type) -> Option<Type> {
    match ty.resolve_compound(module)? {
        CompoundType::Ptr(elem) | CompoundType::ObjRef(elem) | CompoundType::ConstRef(elem) => {
            Some(elem)
        }
        CompoundType::Struct(_)
        | CompoundType::Array { .. }
        | CompoundType::Enum(_)
        | CompoundType::Func { .. } => None,
    }
}

fn projection_slice_can_view_as(
    layout_cache: &mut shape::AggregateLayoutCache,
    module: &ModuleCtx,
    slice: shape::AggregateSlice,
    view_ty: Type,
) -> bool {
    let Some(from_leaf_tys) = projection_view_leaf_tys(layout_cache, module, slice.ty) else {
        return false;
    };
    let Some(to_leaf_tys) = projection_view_leaf_tys(layout_cache, module, view_ty) else {
        return false;
    };

    from_leaf_tys.len() == slice.leaf_count
        && from_leaf_tys.len() == to_leaf_tys.len()
        && (view_ty == slice.ty
            || from_leaf_tys.len() == 1
                && shape::runtime_size_bytes(module, from_leaf_tys[0])
                    == shape::runtime_size_bytes(module, to_leaf_tys[0])
            || shape::is_supported_scalar_shape_ty(module, slice.ty)
                && shape::is_supported_scalar_shape_ty(module, view_ty)
                && layout_cache
                    .compatible_bitcast_runtime_leaves(module, slice.ty, view_ty)
                    .is_some())
}

fn projection_view_leaf_tys(
    layout_cache: &mut shape::AggregateLayoutCache,
    module: &ModuleCtx,
    ty: Type,
) -> Option<Vec<Type>> {
    if shape::is_supported_scalar_shape_ty(module, ty) {
        return Some(
            layout_cache
                .shape(module, ty)?
                .leaves
                .into_iter()
                .map(|leaf| leaf.ty)
                .collect(),
        );
    }

    Some(vec![ty])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transform::aggregate::compute_object_effect_summaries;
    use sonatina_ir::{Module, module::FuncRef};
    use sonatina_parser::parse_module;

    use super::super::object_tracking::{collect_root_slices, whole_root_slice};

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

    fn sorted_known_roots(roots: KnownRoots<'_>) -> Vec<ValueId> {
        let mut roots: Vec<_> = roots.iter().collect();
        roots.sort_unstable_by_key(|root| root.as_u32());
        roots
    }

    fn collect_root_slices_with_arg_roots(
        func: &Function,
        layout_cache: &mut shape::AggregateLayoutCache,
    ) -> FxHashMap<ValueId, shape::AggregateSlice> {
        let mut root_slices = collect_root_slices(func, None, layout_cache);
        for &arg in &func.arg_values {
            let Some(root_ty) = reference_element_ty(func.ctx(), func.dfg.value_ty(arg)) else {
                continue;
            };
            root_slices.insert(arg, whole_root_slice(layout_cache, func.ctx(), root_ty));
        }
        root_slices
    }

    #[test]
    fn exact_known_root_uses_complete_and_may_views() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %f() -> objref<[i256; 8]> {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    return v0;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices_with_arg_roots(func, &mut layout_cache);
            let provenance =
                collect_root_provenance(func, func.ctx(), &root_slices, &mut layout_cache, None);
            let complete = provenance.complete();
            let may = provenance.may();
            let root = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .expect("alloc root should exist");

            assert_eq!(
                complete.exact_projection(root),
                Some(Projection {
                    root_value: root,
                    slice: root_slices[&root],
                })
            );
            assert_eq!(complete.root_set(root), Some(CompleteRootSet::Single(root)));
            match may.root_set(root) {
                MayRootSet::KnownOnly(roots) => assert_eq!(sorted_known_roots(roots), vec![root]),
                MayRootSet::KnownAndUnknown(_) => panic!("exact root should not be unknown"),
            }
        });
    }

    #[test]
    fn objref_load_from_captured_field_keeps_source_root_provenance() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Take = { i256, objref<[i256; 8]> };

func private %f() -> objref<[i256; 8]> {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.objref<@Take> = obj.alloc @Take;
    v2.objref<objref<[i256; 8]>> = obj.proj v1 1.i8;
    obj.store v2 v0;
    v3.objref<[i256; 8]> = obj.load v2;
    return v3;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices_with_arg_roots(func, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );

            let loaded = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .expect("load result should exist");

            let source_root = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                        .filter(|&result| func.dfg.value_ty(result) == func.dfg.value_ty(loaded))
                })
                .expect("source root should exist");

            let complete = provenance.complete();
            assert_eq!(
                complete.root_set(loaded),
                Some(CompleteRootSet::Single(source_root))
            );
        });
    }

    #[test]
    fn overwritten_captured_field_drops_old_source_root() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Take = { i256, objref<[i256; 8]> };

func private %f() -> objref<[i256; 8]> {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    v2.objref<@Take> = obj.alloc @Take;
    v3.objref<objref<[i256; 8]>> = obj.proj v2 1.i8;
    obj.store v3 v0;
    obj.store v3 v1;
    v4.objref<[i256; 8]> = obj.load v3;
    return v4;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices_with_arg_roots(func, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );

            let loads: Vec<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .filter_map(|inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .collect();
            let [loaded] = loads.as_slice() else {
                panic!("expected exactly one obj.load result");
            };
            let roots: Vec<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .filter_map(|inst| {
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                        .filter(|&result| func.dfg.value_ty(result) == func.dfg.value_ty(*loaded))
                })
                .collect();
            let [_, overwritten_root] = roots.as_slice() else {
                panic!("expected exactly two array roots");
            };

            let complete = provenance.complete();
            assert_eq!(
                complete.root_set(*loaded),
                Some(CompleteRootSet::Single(*overwritten_root))
            );
        });
    }

    #[test]
    fn branch_local_overwrite_keeps_all_possible_captured_roots() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Take = { i256, objref<[i256; 8]> };

func private %f(v0.i1) -> objref<[i256; 8]> {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    v2.objref<[i256; 8]> = obj.alloc [i256; 8];
    v3.objref<@Take> = obj.alloc @Take;
    v4.objref<objref<[i256; 8]>> = obj.proj v3 1.i8;
    obj.store v4 v1;
    br v0 block1 block2;

block1:
    jump block3;

block2:
    obj.store v4 v2;
    jump block3;

block3:
    v5.objref<[i256; 8]> = obj.load v4;
    return v5;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices_with_arg_roots(func, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );

            let loaded = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .expect("load result should exist");
            let roots: FxHashSet<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .filter_map(|inst| {
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                        .filter(|&result| func.dfg.value_ty(result) == func.dfg.value_ty(loaded))
                })
                .collect();

            let complete = provenance.complete();
            let may = provenance.may();
            match complete.root_set(loaded) {
                Some(CompleteRootSet::Multiple(actual)) => {
                    assert_eq!(sorted_known_roots(actual), {
                        let mut expected: Vec<_> = roots.into_iter().collect();
                        expected.sort_unstable_by_key(|root| root.as_u32());
                        expected
                    });
                }
                other => panic!("expected complete multiple root set, got {other:?}"),
            }
            match may.root_set(loaded) {
                MayRootSet::KnownOnly(actual) => {
                    let mut expected: Vec<_> = complete
                        .root_set(loaded)
                        .map(|set| match set {
                            CompleteRootSet::Multiple(roots) => sorted_known_roots(roots),
                            CompleteRootSet::Single(root) => vec![root],
                        })
                        .expect("multiple roots should stay complete");
                    expected.sort_unstable_by_key(|root| root.as_u32());
                    assert_eq!(sorted_known_roots(actual), expected);
                }
                MayRootSet::KnownAndUnknown(_) => panic!("known-only roots should stay complete"),
            }
        });
    }

    #[test]
    fn later_store_does_not_retroactively_change_earlier_objref_load() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Take = { i256, objref<[i256; 8]> };

func private %f() -> objref<[i256; 8]> {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    v2.objref<@Take> = obj.alloc @Take;
    v3.objref<objref<[i256; 8]>> = obj.proj v2 1.i8;
    obj.store v3 v0;
    v4.objref<[i256; 8]> = obj.load v3;
    obj.store v3 v1;
    return v4;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices_with_arg_roots(func, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );

            let loads: Vec<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .filter_map(|inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .collect();
            let [loaded] = loads.as_slice() else {
                panic!("expected exactly one obj.load result");
            };
            let roots: Vec<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .filter_map(|inst| {
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                        .filter(|&result| func.dfg.value_ty(result) == func.dfg.value_ty(*loaded))
                })
                .collect();
            let [loaded_root, _] = roots.as_slice() else {
                panic!("expected exactly two array roots");
            };

            let complete = provenance.complete();
            assert_eq!(
                complete.root_set(*loaded),
                Some(CompleteRootSet::Single(*loaded_root))
            );
        });
    }

    #[test]
    fn call_write_kills_stale_captured_root_provenance() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Take = { i256, objref<[i256; 8]> };

func private %overwrite(v0.objref<@Take>, v1.objref<[i256; 8]>) {
block0:
    v2.objref<objref<[i256; 8]>> = obj.proj v0 1.i8;
    obj.store v2 v1;
    return;
}

func private %f() -> objref<[i256; 8]> {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    v2.objref<@Take> = obj.alloc @Take;
    v3.objref<objref<[i256; 8]>> = obj.proj v2 1.i8;
    obj.store v3 v0;
    call %overwrite v2 v1;
    v4.objref<[i256; 8]> = obj.load v3;
    return v4;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices_with_arg_roots(func, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );

            let loads: Vec<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .filter_map(|inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .collect();
            let [loaded] = loads.as_slice() else {
                panic!("expected exactly one obj.load result");
            };
            let roots: Vec<_> = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .filter_map(|inst| {
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                        .filter(|&result| func.dfg.value_ty(result) == func.dfg.value_ty(*loaded))
                })
                .collect();
            let [_, overwritten_root] = roots.as_slice() else {
                panic!("expected exactly two array roots");
            };

            let complete = provenance.complete();
            assert_eq!(
                complete.root_set(*loaded),
                Some(CompleteRootSet::Single(*overwritten_root))
            );
        });
    }

    #[test]
    fn weak_update_through_multi_root_phi_preserves_captured_source_roots() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Cell = { i256 };
type @Take = { objref<i256> };

func private %take(v0.objref<@Cell>) -> objref<@Take> {
block0:
    v1.objref<@Take> = obj.alloc @Take;
    v2.objref<objref<i256>> = obj.proj v1 0.i8;
    v3.objref<i256> = obj.proj v0 0.i8;
    obj.store v2 v3;
    return v1;
}

func private %f(v0.i1, v1.objref<@Cell>, v2.objref<@Cell>) -> objref<i256> {
block0:
    br v0 block1 block2;

block1:
    v3.objref<@Take> = call %take v1;
    jump block3;

block2:
    v4.objref<@Take> = call %take v1;
    jump block3;

block3:
    v5.objref<@Take> = phi (v3 block1) (v4 block2);
    v6.objref<i256> = obj.proj v2 0.i8;
    v7.objref<objref<i256>> = obj.proj v5 0.i8;
    obj.store v7 v6;
    v8.objref<objref<i256>> = obj.proj v3 0.i8;
    v9.objref<i256> = obj.load v8;
    return v9;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices_with_arg_roots(func, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );
            let loaded = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                        .filter(|&result| {
                            reference_element_ty(func.ctx(), func.dfg.value_ty(result)).is_some()
                        })
                })
                .expect("objref load result should exist");
            let expected = vec![func.arg_values[1], func.arg_values[2]];
            let may = provenance.may();

            assert_eq!(
                sorted_known_roots(may.root_set(loaded).observed()),
                expected
            );
        });
    }

    #[test]
    fn unknown_capture_target_does_not_clear_known_captured_roots() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Cell = { i256 };
type @Take = { objref<i256> };

declare external %mystery_take() -> objref<@Take>;

func private %take(v0.objref<@Cell>) -> objref<@Take> {
block0:
    v1.objref<@Take> = obj.alloc @Take;
    v2.objref<objref<i256>> = obj.proj v1 0.i8;
    v3.objref<i256> = obj.proj v0 0.i8;
    obj.store v2 v3;
    return v1;
}

func private %f(v0.i1, v1.objref<@Cell>, v2.objref<@Cell>) -> objref<i256> {
block0:
    v3.objref<@Take> = call %take v1;
    br v0 block1 block2;

block1:
    jump block3;

block2:
    v4.objref<@Take> = call %mystery_take;
    jump block3;

block3:
    v5.objref<@Take> = phi (v3 block1) (v4 block2);
    v6.objref<i256> = obj.proj v2 0.i8;
    v7.objref<objref<i256>> = obj.proj v5 0.i8;
    obj.store v7 v6;
    v8.objref<objref<i256>> = obj.proj v3 0.i8;
    v9.objref<i256> = obj.load v8;
    return v9;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices_with_arg_roots(func, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );
            let loaded = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                        .filter(|&result| {
                            reference_element_ty(func.ctx(), func.dfg.value_ty(result)).is_some()
                        })
                })
                .expect("objref load result should exist");
            let expected = vec![func.arg_values[1], func.arg_values[2]];
            let may = provenance.may();

            assert_eq!(
                sorted_known_roots(may.root_set(loaded).observed()),
                expected
            );
        });
    }

    #[test]
    fn same_root_ambiguous_store_preserves_captured_source_roots() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Cell = { i256 };
type @Pair = { objref<i256>, objref<i256> };

func private %f(v0.i1, v1.objref<@Cell>, v2.objref<@Cell>) -> objref<i256> {
block0:
    v3.objref<@Pair> = obj.alloc @Pair;
    v4.objref<objref<i256>> = obj.proj v3 0.i8;
    v5.objref<i256> = obj.proj v1 0.i8;
    obj.store v4 v5;
    v6.objref<objref<i256>> = obj.proj v3 1.i8;
    v7.objref<i256> = obj.proj v1 0.i8;
    obj.store v6 v7;
    br v0 block1 block2;

block1:
    jump block3;

block2:
    jump block3;

block3:
    v8.objref<objref<i256>> = phi (v4 block1) (v6 block2);
    v9.objref<i256> = obj.proj v2 0.i8;
    obj.store v8 v9;
    v10.objref<objref<i256>> = obj.proj v3 0.i8;
    v11.objref<i256> = obj.load v10;
    return v11;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices_with_arg_roots(func, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );
            let loaded = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                        .filter(|&result| {
                            reference_element_ty(func.ctx(), func.dfg.value_ty(result)).is_some()
                        })
                })
                .expect("objref load result should exist");
            let expected = vec![func.arg_values[1], func.arg_values[2]];
            let may = provenance.may();

            assert_eq!(
                sorted_known_roots(may.root_set(loaded).observed()),
                expected
            );
        });
    }

    #[test]
    fn phi_with_unknown_branch_stays_unknown() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

declare external %mystery() -> objref<[i256; 8]>;

func private %f(v0.i1) -> objref<[i256; 8]> {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    br v0 block1 block2;

block1:
    jump block3;

block2:
    v2.objref<[i256; 8]> = call %mystery;
    jump block3;

block3:
    v3.objref<[i256; 8]> = phi (v1 block1) (v2 block2);
    return v3;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices(func, None, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );

            let phi_result = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .expect("phi result should exist");

            let complete = provenance.complete();
            let may = provenance.may();
            assert_eq!(complete.exact_projection(phi_result), None);
            assert_eq!(complete.root_set(phi_result), None);
            assert_eq!(complete.possible_projections(phi_result), None);
            match may.root_set(phi_result) {
                MayRootSet::KnownAndUnknown(roots) => {
                    assert_eq!(sorted_known_roots(roots).len(), 1);
                }
                MayRootSet::KnownOnly(_) => panic!("phi with unknown branch must stay incomplete"),
            }
        });
    }

    #[test]
    fn unknown_only_uses_known_and_unknown_may_view() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

declare external %mystery() -> objref<[i256; 8]>;

func private %f() -> objref<[i256; 8]> {
block0:
    v0.objref<[i256; 8]> = call %mystery;
    return v0;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices(func, None, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );
            let call_result = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .expect("call result should exist");
            let complete = provenance.complete();
            let may = provenance.may();

            assert_eq!(complete.root_set(call_result), None);
            match may.root_set(call_result) {
                MayRootSet::KnownAndUnknown(roots) => assert!(roots.is_empty()),
                MayRootSet::KnownOnly(_) => panic!("unknown-only value must stay incomplete"),
            }
        });
    }
}
