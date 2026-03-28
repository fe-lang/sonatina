use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, InstId, Type, ValueId,
    inst::{cast, control_flow, data, downcast},
    module::ModuleCtx,
    types::CompoundType,
};

use super::{ObjectEffectSummaryMap, ObjectReturnEffect, shape};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RootCaptureRoot {
    dst_slice: shape::AggregateSlice,
    src_root: ValueId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Projection {
    pub root_value: ValueId,
    pub slice: shape::AggregateSlice,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum RootProvenance {
    Exact(Projection),
    SameRoot(ValueId),
    Maybe(FxHashSet<ValueId>),
    Unknown,
}

#[derive(Default)]
pub(crate) struct RootProvenanceMap {
    exact: SecondaryMap<ValueId, Option<Projection>>,
    possible_roots: SecondaryMap<ValueId, FxHashSet<ValueId>>,
}

impl RootProvenanceMap {
    pub(crate) fn exact_projection(&self, value: ValueId) -> Option<Projection> {
        self.exact[value]
    }

    pub(crate) fn provenance(&self, value: ValueId) -> RootProvenance {
        if let Some(projection) = self.exact[value] {
            return RootProvenance::Exact(projection);
        }

        match self.possible_roots[value].len() {
            0 => RootProvenance::Unknown,
            1 => RootProvenance::SameRoot(
                *self.possible_roots[value]
                    .iter()
                    .next()
                    .expect("singleton root set must have an element"),
            ),
            _ => RootProvenance::Maybe(self.possible_roots[value].clone()),
        }
    }

    pub(crate) fn into_exact_projection(self) -> SecondaryMap<ValueId, Option<Projection>> {
        self.exact
    }

    pub(crate) fn into_possible_roots(self) -> SecondaryMap<ValueId, FxHashSet<ValueId>> {
        self.possible_roots
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExactState {
    Unknown,
    Exact(Projection),
    Blocked,
}

pub(crate) fn collect_root_provenance(
    func: &Function,
    module: &ModuleCtx,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
    layout_cache: &mut shape::AggregateLayoutCache,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> RootProvenanceMap {
    let mut provenance = RootProvenanceMap::default();
    let mut exact_states = SecondaryMap::default();

    for (&root_value, &slice) in root_slices {
        provenance.possible_roots[root_value].insert(root_value);
        exact_states[root_value] = Some(ExactState::Exact(Projection { root_value, slice }));
    }

    compute_possible_roots(func, &mut provenance.possible_roots, object_effects);
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
            ExactState::Exact(projection) => Some(projection),
            ExactState::Unknown | ExactState::Blocked => None,
        };
    }

    refine_possible_roots_from_objref_loads(
        func,
        root_slices,
        &exact_states,
        &mut provenance.possible_roots,
        object_effects,
    );

    provenance
}

fn compute_possible_roots(
    func: &Function,
    possible_roots: &mut SecondaryMap<ValueId, FxHashSet<ValueId>>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) {
    loop {
        let mut changed = false;

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }

                let Some(updated) =
                    possible_root_transfer(func, inst, possible_roots, object_effects)
                else {
                    continue;
                };
                let Some(result) = single_result_value(func, inst) else {
                    continue;
                };

                if updated != possible_roots[result] {
                    possible_roots[result] = updated;
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
    object_effects: Option<&ObjectEffectSummaryMap>,
) {
    let mut root_captures = FxHashMap::<ValueId, Vec<RootCaptureRoot>>::default();

    loop {
        let mut changed = false;

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }

                if let Some(obj_store) =
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst))
                    && reference_element_ty(func.ctx(), func.dfg.value_ty(*obj_store.value()))
                        .is_some()
                {
                    changed |= record_root_capture_sources(
                        &mut root_captures,
                        capture_destinations_for_value(
                            *obj_store.object(),
                            None,
                            exact_states,
                            possible_roots,
                            root_slices,
                        ),
                        &possible_roots[*obj_store.value()],
                    );
                }

                if downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)).is_some() {
                    changed |= merge_call_capture_roots(
                        func,
                        inst,
                        exact_states,
                        possible_roots,
                        root_slices,
                        object_effects,
                        &mut root_captures,
                    );
                }

                if let Some(updated) =
                    possible_root_transfer(func, inst, possible_roots, object_effects)
                    && let Some(result) = single_result_value(func, inst)
                    && union_root_set(&mut possible_roots[result], &updated)
                {
                    changed = true;
                }

                if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                    && reference_element_ty(func.ctx(), func.dfg.value_ty(*obj_load.object()))
                        .is_some()
                    && let Some(result) = single_result_value(func, inst)
                {
                    let loaded_roots = capture_roots_for_value(
                        *obj_load.object(),
                        exact_states,
                        possible_roots,
                        root_slices,
                        &root_captures,
                    );
                    if union_root_set(&mut possible_roots[result], &loaded_roots) {
                        changed = true;
                    }
                }
            }
        }

        if !changed {
            return;
        }
    }
}

fn merge_call_capture_roots(
    func: &Function,
    inst: InstId,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
    object_effects: Option<&ObjectEffectSummaryMap>,
    root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureRoot>>,
) -> bool {
    let call = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
        .expect("merge_call_capture_roots requires a call instruction");
    let Some(summary) = object_effects.and_then(|effects| effects.get(call.callee())) else {
        return false;
    };

    let mut changed = false;
    let call_result = single_result_value(func, inst);
    for capture in &summary.captures {
        let Some(&src_arg) = call.args().get(capture.src_arg) else {
            continue;
        };
        let dsts = match capture.dst {
            super::object_effects::ObjectCaptureDestination::Arg { index, slice } => call
                .args()
                .get(index)
                .map(|&dst_arg| {
                    capture_destinations_for_value(
                        dst_arg,
                        Some(slice),
                        exact_states,
                        possible_roots,
                        root_slices,
                    )
                })
                .unwrap_or_default(),
            super::object_effects::ObjectCaptureDestination::Return { slice } => call_result
                .map(|result| {
                    capture_destinations_for_value(
                        result,
                        Some(slice),
                        exact_states,
                        possible_roots,
                        root_slices,
                    )
                })
                .unwrap_or_default(),
        };
        changed |= record_root_capture_sources(root_captures, dsts, &possible_roots[src_arg]);
    }
    changed
}

fn record_root_capture_sources(
    root_captures: &mut FxHashMap<ValueId, Vec<RootCaptureRoot>>,
    dsts: Vec<(ValueId, shape::AggregateSlice)>,
    src_roots: &FxHashSet<ValueId>,
) -> bool {
    let mut changed = false;
    for (root, dst_slice) in dsts {
        for &src_root in src_roots {
            let entry = root_captures.entry(root).or_default();
            let capture = RootCaptureRoot {
                dst_slice,
                src_root,
            };
            if entry.contains(&capture) {
                continue;
            }
            entry.push(capture);
            changed = true;
        }
    }
    changed
}

fn capture_destinations_for_value(
    value: ValueId,
    relative_slice: Option<shape::AggregateSlice>,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
) -> Vec<(ValueId, shape::AggregateSlice)> {
    if let Some(projection) = exact_projection_of(exact_states, value) {
        return relative_slice
            .map(|slice| offset_projection_slice(projection.slice, slice))
            .unwrap_or(Some(projection.slice))
            .map(|slice| vec![(projection.root_value, slice)])
            .unwrap_or_default();
    }

    possible_roots[value]
        .iter()
        .copied()
        .filter_map(|root| {
            whole_root_projection(root, exact_states, root_slices).map(|slice| (root, slice))
        })
        .collect()
}

fn capture_roots_for_value(
    value: ValueId,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
    root_captures: &FxHashMap<ValueId, Vec<RootCaptureRoot>>,
) -> FxHashSet<ValueId> {
    let mut roots = FxHashSet::default();
    for (root, access_slice) in
        capture_destinations_for_value(value, None, exact_states, possible_roots, root_slices)
    {
        let Some(captures) = root_captures.get(&root) else {
            continue;
        };
        for capture in captures {
            if slices_overlap_relative(access_slice, capture.dst_slice) {
                roots.insert(capture.src_root);
            }
        }
    }
    roots
}

fn whole_root_projection(
    root: ValueId,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
) -> Option<shape::AggregateSlice> {
    root_slices
        .get(&root)
        .copied()
        .or_else(|| exact_projection_of(exact_states, root).map(|projection| projection.slice))
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

fn slices_overlap_relative(lhs: shape::AggregateSlice, rhs: shape::AggregateSlice) -> bool {
    lhs.first_leaf < rhs.first_leaf + rhs.leaf_count
        && rhs.first_leaf < lhs.first_leaf + lhs.leaf_count
}

fn possible_root_transfer(
    func: &Function,
    inst: InstId,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> Option<FxHashSet<ValueId>> {
    if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)) {
        return gep
            .values()
            .first()
            .map(|base| possible_roots[*base].clone());
    }

    if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(possible_roots[*bitcast.from()].clone());
    }

    if let Some(obj_proj) = downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)) {
        return obj_proj
            .values()
            .first()
            .map(|base| possible_roots[*base].clone());
    }

    if let Some(obj_index) = downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(possible_roots[*obj_index.object()].clone());
    }

    if let Some(enum_proj) = downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst)) {
        return Some(possible_roots[*enum_proj.object()].clone());
    }

    if let Some(enum_assert_ref) =
        downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst))
    {
        return Some(possible_roots[*enum_assert_ref.object()].clone());
    }

    if let Some(call) = downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst)) {
        return call_return_root_transfer(func, inst, call, possible_roots, object_effects);
    }

    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).map(|phi| {
        phi.args()
            .iter()
            .flat_map(|(arg, _)| possible_roots[*arg].iter().copied())
            .collect()
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
    value_sccs: &FxHashMap<ValueId, usize>,
    layout_cache: &mut shape::AggregateLayoutCache,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> ExactState {
    if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)) {
        let Some(&base) = gep.values().first() else {
            return exact_state_or_unknown(exact_states, result, possible_roots);
        };
        let Some(base_projection) = exact_projection_of(exact_states, base) else {
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
        let Some(source_projection) = exact_projection_of(exact_states, source) else {
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
            return exact_state_or_unknown(exact_states, result, possible_roots);
        };
        let Some(base_projection) = exact_projection_of(exact_states, base) else {
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
        let Some(base_projection) = exact_projection_of(exact_states, base) else {
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
        let Some(base_projection) = exact_projection_of(exact_states, base) else {
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
        let Some(base_projection) = exact_projection_of(exact_states, base) else {
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
            layout_cache,
            object_effects,
        );
    }

    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst))
        .map_or(ExactState::Unknown, |phi| {
            derive_phi_state(func, result, phi, exact_states, possible_roots, value_sccs)
        })
}

fn derive_phi_state(
    func: &Function,
    result: ValueId,
    phi: &control_flow::Phi,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    value_sccs: &FxHashMap<ValueId, usize>,
) -> ExactState {
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
        let Some(projection) = exact_projection_of(exact_states, arg) else {
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

fn exact_projection_of(
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    value: ValueId,
) -> Option<Projection> {
    match exact_states[value].unwrap_or(ExactState::Unknown) {
        ExactState::Exact(projection) => Some(projection),
        ExactState::Unknown | ExactState::Blocked => None,
    }
}

fn exact_state_or_unknown(
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    value: ValueId,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
) -> ExactState {
    if possible_roots[value].is_empty() {
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
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> Option<FxHashSet<ValueId>> {
    let [result] = func.dfg.inst_results(inst) else {
        return None;
    };
    let summary = object_effects.and_then(|effects| effects.get(call.callee()))?;
    match summary.ret_effect {
        ObjectReturnEffect::SameAsArg { index } | ObjectReturnEffect::DerivedFromArg { index } => {
            call.args()
                .get(index)
                .map(|arg| possible_roots[*arg].clone())
        }
        ObjectReturnEffect::FreshObject => {
            let mut roots = FxHashSet::default();
            roots.insert(*result);
            Some(roots)
        }
        ObjectReturnEffect::None | ObjectReturnEffect::Unknown => None,
    }
}

fn derive_call_exact_state(
    func: &Function,
    inst: InstId,
    call: &control_flow::Call,
    exact_states: &SecondaryMap<ValueId, Option<ExactState>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    layout_cache: &mut shape::AggregateLayoutCache,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> ExactState {
    let Some(result) = single_result_value(func, inst) else {
        return ExactState::Blocked;
    };
    let Some(summary) = object_effects.and_then(|effects| effects.get(call.callee())) else {
        return exact_state_or_unknown(exact_states, result, possible_roots);
    };

    match summary.ret_effect {
        ObjectReturnEffect::SameAsArg { index } => {
            let Some(&arg) = call.args().get(index) else {
                return ExactState::Blocked;
            };
            let Some(projection) = exact_projection_of(exact_states, arg) else {
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
            exact_state_or_unknown(exact_states, arg, possible_roots)
        }
        ObjectReturnEffect::FreshObject => {
            fresh_call_root_projection(func, result, inst, object_effects, layout_cache)
                .map_or(ExactState::Blocked, ExactState::Exact)
        }
        ObjectReturnEffect::None | ObjectReturnEffect::Unknown => {
            exact_state_or_unknown(exact_states, result, possible_roots)
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
        CompoundType::Ptr(elem) | CompoundType::ObjRef(elem) => Some(elem),
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
    use crate::optim::aggregate::{
        compute_object_effect_summaries, object_tracking::collect_root_slices,
    };
    use sonatina_ir::{Module, module::FuncRef};
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
            let root_slices = collect_root_slices(func, None, &mut layout_cache);
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

            assert_eq!(
                provenance.provenance(loaded),
                RootProvenance::SameRoot(source_root)
            );
        });
    }
}
