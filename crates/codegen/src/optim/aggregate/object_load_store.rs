use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, Type, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
    module::ModuleCtx,
};

use super::{cleanup::DeadPureInstCleanup, reconstruct::AggregateValueReconstructor, shape};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ObjectSlice {
    root: ValueId,
    ty: Type,
    first_leaf: usize,
    leaf_count: usize,
    total_leaves: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TrackedObject {
    Exact(ObjectSlice),
    RootUnknown { root: ValueId, total_leaves: usize },
}

#[derive(Clone, Copy, Debug)]
struct StoredSlice {
    slice: ObjectSlice,
    value: ValueId,
}

#[derive(Default)]
pub struct ObjectLoadStore {
    changed: bool,
    layout_cache: shape::AggregateLayoutCache,
    dead_pure_cleanup: DeadPureInstCleanup,
}

impl ObjectLoadStore {
    pub fn run(&mut self, func: &mut Function) -> bool {
        self.changed = false;
        self.layout_cache.clear();

        loop {
            func.rebuild_users();
            let tracked = self.collect_tracked_objects(func);
            let possible_roots = self.collect_possible_roots(func);

            let mut iter_changed = self.run_forward(func, &tracked, &possible_roots);
            iter_changed |= self.run_backward(func, &tracked, &possible_roots);

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

    fn collect_tracked_objects(
        &mut self,
        func: &Function,
    ) -> SecondaryMap<ValueId, Option<TrackedObject>> {
        let mut tracked = SecondaryMap::default();

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if let Some(obj_alloc) =
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                    && let Some(result) = func.dfg.inst_result(inst)
                    && let Some(slice) =
                        self.whole_object_slice(func.ctx(), result, *obj_alloc.ty())
                {
                    tracked[result] = Some(TrackedObject::Exact(slice));
                }
            }
        }

        loop {
            let mut changed = false;

            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }

                    let updated = if let Some(obj_proj) =
                        downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst))
                    {
                        if func.dfg.inst_result(inst).is_none() {
                            continue;
                        }
                        let Some((&base, indices)) = obj_proj.values().split_first() else {
                            continue;
                        };
                        self.project_tracked_object(func, tracked[base].as_ref().copied(), indices)
                    } else if let Some(obj_index) =
                        downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst))
                    {
                        if func.dfg.inst_result(inst).is_none() {
                            continue;
                        }
                        self.project_tracked_object(
                            func,
                            tracked[*obj_index.object()].as_ref().copied(),
                            &[*obj_index.index()],
                        )
                    } else if let Some(phi) =
                        downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst))
                    {
                        let Some(result) = func.dfg.inst_result(inst) else {
                            continue;
                        };
                        let merged = merge_phi_tracked(
                            phi.args()
                                .iter()
                                .map(|(arg, _)| tracked[*arg].as_ref().copied()),
                        );
                        if merged != tracked[result] {
                            tracked[result] = merged;
                            changed = true;
                        }
                        continue;
                    } else {
                        continue;
                    };

                    let Some(result) = func.dfg.inst_result(inst) else {
                        continue;
                    };
                    if updated != tracked[result] {
                        tracked[result] = updated;
                        changed = true;
                    }
                }
            }

            if !changed {
                return tracked;
            }
        }
    }

    fn collect_possible_roots(
        &mut self,
        func: &Function,
    ) -> SecondaryMap<ValueId, FxHashSet<ValueId>> {
        let mut possible_roots: SecondaryMap<ValueId, FxHashSet<ValueId>> = SecondaryMap::default();

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if let Some(obj_alloc) =
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                    && let Some(result) = func.dfg.inst_result(inst)
                    && self
                        .whole_object_slice(func.ctx(), result, *obj_alloc.ty())
                        .is_some()
                {
                    possible_roots[result].insert(result);
                }
            }
        }

        loop {
            let mut changed = false;

            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }

                    let updated = if let Some(obj_proj) =
                        downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst))
                    {
                        obj_proj
                            .values()
                            .first()
                            .map_or_else(FxHashSet::default, |base| possible_roots[*base].clone())
                    } else if let Some(obj_index) =
                        downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst))
                    {
                        possible_roots[*obj_index.object()].clone()
                    } else if let Some(phi) =
                        downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst))
                    {
                        phi.args()
                            .iter()
                            .flat_map(|(arg, _)| possible_roots[*arg].iter().copied())
                            .collect()
                    } else {
                        continue;
                    };

                    let Some(result) = func.dfg.inst_result(inst) else {
                        continue;
                    };
                    if updated != possible_roots[result] {
                        possible_roots[result] = updated;
                        changed = true;
                    }
                }
            }

            if !changed {
                return possible_roots;
            }
        }
    }

    fn whole_object_slice(
        &mut self,
        ctx: &ModuleCtx,
        root: ValueId,
        pointee_ty: Type,
    ) -> Option<ObjectSlice> {
        let total_leaves = self.root_leaf_count(ctx, pointee_ty);
        Some(ObjectSlice {
            root,
            ty: pointee_ty,
            first_leaf: 0,
            leaf_count: total_leaves,
            total_leaves,
        })
    }

    fn root_leaf_count(&mut self, ctx: &ModuleCtx, ty: Type) -> usize {
        if ty == Type::Unit {
            return 0;
        }
        self.layout_cache
            .shape(ctx, ty)
            .map_or(1, |shape| shape.leaves.len())
    }

    fn project_tracked_object(
        &mut self,
        func: &Function,
        base: Option<TrackedObject>,
        indices: &[ValueId],
    ) -> Option<TrackedObject> {
        let base = base?;
        let Some(exact) = base.exact() else {
            return Some(TrackedObject::RootUnknown {
                root: base.root(),
                total_leaves: base.total_leaves(),
            });
        };
        shape::aggregate_slice_for_object_path(func.ctx(), exact.ty, indices, &func.dfg)
            .map(|sub| {
                TrackedObject::Exact(ObjectSlice {
                    root: exact.root,
                    ty: sub.ty,
                    first_leaf: exact.first_leaf + sub.first_leaf,
                    leaf_count: sub.leaf_count,
                    total_leaves: exact.total_leaves,
                })
            })
            .or(Some(TrackedObject::RootUnknown {
                root: exact.root,
                total_leaves: exact.total_leaves,
            }))
    }

    fn run_forward(
        &mut self,
        func: &mut Function,
        tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
        possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    ) -> bool {
        let mut changed = false;

        for block in func.layout.iter_block().collect::<Vec<_>>() {
            let mut available = Vec::<StoredSlice>::new();
            for inst in func.layout.iter_inst(block).collect::<Vec<_>>() {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }

                if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                {
                    for root in observed_roots(func, inst, possible_roots, &[*obj_load.object()]) {
                        kill_root_available(&mut available, root);
                    }
                    if let Some(slice) = tracked[*obj_load.object()]
                        .as_ref()
                        .copied()
                        .and_then(TrackedObject::exact)
                        && let Some(replacement) =
                            self.replacement_for_load(func, inst, slice, &available)
                        && let Some(result) = func.dfg.inst_result(inst)
                    {
                        func.dfg.change_to_alias(result, replacement);
                        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                        changed = true;
                        continue;
                    }
                }

                if let Some(obj_store) =
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst))
                {
                    for root in observed_roots(func, inst, possible_roots, &[*obj_store.object()]) {
                        kill_root_available(&mut available, root);
                    }

                    let Some(tracked_object) = tracked[*obj_store.object()].as_ref().copied()
                    else {
                        for &root in &possible_roots[*obj_store.object()] {
                            kill_root_available(&mut available, root);
                        }
                        continue;
                    };
                    let Some(slice) = tracked_object.exact() else {
                        for &root in &possible_roots[*obj_store.object()] {
                            kill_root_available(&mut available, root);
                        }
                        continue;
                    };
                    if available
                        .iter()
                        .rev()
                        .find(|entry| entry.slice == slice)
                        .is_some_and(|entry| entry.value == *obj_store.value())
                    {
                        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                        changed = true;
                        continue;
                    }
                    kill_overlapping_available(&mut available, slice);
                    available.push(StoredSlice {
                        slice,
                        value: *obj_store.value(),
                    });
                    continue;
                }

                for root in observed_roots(func, inst, possible_roots, &[]) {
                    kill_root_available(&mut available, root);
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
        available: &[StoredSlice],
    ) -> Option<ValueId> {
        for entry in available.iter().rev() {
            if entry.slice.root != slice.root || !slice_is_covered_by(entry.slice, slice) {
                continue;
            }
            if entry.slice == slice && func.dfg.value_ty(entry.value) == slice.ty {
                return Some(entry.value);
            }

            let source_slice = shape::aggregate_slice_for_leaf_range(
                func.ctx(),
                entry.slice.ty,
                slice.first_leaf - entry.slice.first_leaf,
                slice.leaf_count,
            )?;
            if let Some(rebuilt) = AggregateValueReconstructor::new(&mut self.layout_cache)
                .rebuild_slice(
                    func,
                    inst,
                    entry.value,
                    entry.slice.ty,
                    source_slice,
                    slice.ty,
                )
            {
                return Some(rebuilt);
            }
        }

        None
    }

    fn run_backward(
        &mut self,
        func: &mut Function,
        tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
        possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
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

                let out_state = meet_live(
                    cfg.succs_of(block)
                        .copied()
                        .filter(|succ| reachable[*succ])
                        .map(|succ| in_states[succ].clone()),
                );
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
                    transfer_backward_live(func, inst, tracked, possible_roots, &mut live);
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
                let removed = try_remove_dead_store(func, inst, tracked, possible_roots, &live);
                changed |= removed;
                if removed {
                    continue;
                }
                transfer_backward_live(func, inst, tracked, possible_roots, &mut live);
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
}

fn merge_phi_tracked(values: impl Iterator<Item = Option<TrackedObject>>) -> Option<TrackedObject> {
    let values: Vec<_> = values.collect();
    let first = values.first().copied().flatten()?;
    let same_root = values
        .iter()
        .copied()
        .all(|value| value.is_some_and(|value| value.root() == first.root()));
    if !same_root {
        return None;
    }
    let Some(first_exact) = first.exact() else {
        return Some(TrackedObject::RootUnknown {
            root: first.root(),
            total_leaves: first.total_leaves(),
        });
    };
    if values
        .iter()
        .copied()
        .all(|value| value.and_then(TrackedObject::exact) == Some(first_exact))
    {
        Some(TrackedObject::Exact(first_exact))
    } else {
        Some(TrackedObject::RootUnknown {
            root: first.root(),
            total_leaves: first.total_leaves(),
        })
    }
}

fn observed_roots(
    func: &Function,
    inst: InstId,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    skip: &[ValueId],
) -> Vec<ValueId> {
    if downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_some()
    {
        return Vec::new();
    }

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
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    live: &mut FxHashMap<ValueId, FxHashSet<usize>>,
) {
    if let Some(obj_load) = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)) {
        if let Some(tracked_object) = tracked[*obj_load.object()].as_ref().copied() {
            mark_live(live, tracked_object);
        } else {
            for &root in &possible_roots[*obj_load.object()] {
                mark_root_live(live, root, root_total_leaves(tracked, root));
            }
        }
        for root in observed_roots(func, inst, possible_roots, &[*obj_load.object()]) {
            mark_root_live(live, root, root_total_leaves(tracked, root));
        }
        return;
    }

    if let Some(obj_store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)) {
        for root in observed_roots(func, inst, possible_roots, &[*obj_store.object()]) {
            mark_root_live(live, root, root_total_leaves(tracked, root));
        }

        let Some(tracked_object) = tracked[*obj_store.object()].as_ref().copied() else {
            for &root in &possible_roots[*obj_store.object()] {
                mark_root_live(live, root, root_total_leaves(tracked, root));
            }
            return;
        };
        if let Some(slice) = tracked_object.exact() {
            clear_live_slice(live, slice);
        } else {
            for &root in &possible_roots[*obj_store.object()] {
                mark_root_live(live, root, root_total_leaves(tracked, root));
            }
        }
        return;
    }

    for root in observed_roots(func, inst, possible_roots, &[]) {
        mark_root_live(live, root, root_total_leaves(tracked, root));
    }
}

fn try_remove_dead_store(
    func: &mut Function,
    inst: InstId,
    tracked: &SecondaryMap<ValueId, Option<TrackedObject>>,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    live: &FxHashMap<ValueId, FxHashSet<usize>>,
) -> bool {
    let Some(obj_store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)) else {
        return false;
    };
    let Some(tracked_object) = tracked[*obj_store.object()].as_ref().copied() else {
        return false;
    };
    let needed = if let Some(slice) = tracked_object.exact() {
        slice_has_live_leaf(live, slice)
    } else {
        possible_roots[*obj_store.object()]
            .iter()
            .copied()
            .any(|root| root_has_live(live, root))
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

fn kill_overlapping_available(available: &mut Vec<StoredSlice>, slice: ObjectSlice) {
    available.retain(|entry| entry.slice.root != slice.root || !slices_overlap(entry.slice, slice));
}

fn kill_root_available(available: &mut Vec<StoredSlice>, root: ValueId) {
    available.retain(|entry| entry.slice.root != root);
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

fn slices_overlap(lhs: ObjectSlice, rhs: ObjectSlice) -> bool {
    lhs.root == rhs.root
        && lhs.first_leaf < rhs.first_leaf + rhs.leaf_count
        && rhs.first_leaf < lhs.first_leaf + lhs.leaf_count
}

fn slice_is_covered_by(lhs: ObjectSlice, rhs: ObjectSlice) -> bool {
    lhs.root == rhs.root
        && lhs.first_leaf <= rhs.first_leaf
        && rhs.first_leaf + rhs.leaf_count <= lhs.first_leaf + lhs.leaf_count
}

impl TrackedObject {
    fn exact(self) -> Option<ObjectSlice> {
        match self {
            Self::Exact(slice) => Some(slice),
            Self::RootUnknown { .. } => None,
        }
    }

    fn root(self) -> ValueId {
        match self {
            Self::Exact(slice) => slice.root,
            Self::RootUnknown { root, .. } => root,
        }
    }

    fn total_leaves(self) -> usize {
        match self {
            Self::Exact(slice) => slice.total_leaves,
            Self::RootUnknown { total_leaves, .. } => total_leaves,
        }
    }
}
