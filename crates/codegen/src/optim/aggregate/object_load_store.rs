use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, Type, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, control_flow, data, downcast},
    module::{FuncRef, ModuleCtx},
};

use super::{
    LocalObjectArgInfo, LocalObjectArgMap, RootProvenance, cleanup::DeadPureInstCleanup,
    collect_root_provenance, reconstruct::AggregateValueReconstructor, shape,
};

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
        self.run_with_local_object_args(func, None)
    }

    // `local_object_args` must be computed before entering `func_store.modify(...)`.
    pub(crate) fn run_for_func(
        &mut self,
        func_ref: FuncRef,
        func: &mut Function,
        local_object_args: &LocalObjectArgMap,
    ) -> bool {
        self.run_with_local_object_args(func, local_object_args.get(&func_ref))
    }

    fn run_with_local_object_args(
        &mut self,
        func: &mut Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
    ) -> bool {
        self.changed = false;
        self.layout_cache.clear();

        loop {
            func.rebuild_users();
            let root_slices = self.collect_root_slices(func, local_object_args);
            let provenance =
                collect_root_provenance(func, func.ctx(), &root_slices, &mut self.layout_cache);
            let tracked = self.collect_tracked_objects(func, &provenance);
            let possible_roots = provenance.into_possible_roots();
            let live_out_roots = self.collect_live_out_roots(&tracked, func, local_object_args);

            let mut iter_changed = self.run_forward(func, &tracked, &possible_roots);
            iter_changed |= self.run_backward(func, &tracked, &possible_roots, &live_out_roots);

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
        provenance: &super::provenance::RootProvenanceMap,
    ) -> SecondaryMap<ValueId, Option<TrackedObject>> {
        let mut tracked = SecondaryMap::default();

        for value in func.dfg.value_ids() {
            if objref_element_ty(func.ctx(), func.dfg.value_ty(value)).is_none() {
                continue;
            }
            tracked[value] =
                self.tracked_object_from_provenance(func, provenance.provenance(value));
        }

        tracked
    }

    fn collect_root_slices(
        &mut self,
        func: &Function,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
    ) -> FxHashMap<ValueId, shape::AggregateSlice> {
        let mut root_slices = FxHashMap::default();

        if let Some(local_object_args) = local_object_args {
            for &idx in local_object_args.keys() {
                if let Some(&root) = func.arg_values.get(idx)
                    && let Some(root_ty) = objref_element_ty(func.ctx(), func.dfg.value_ty(root))
                {
                    root_slices.insert(root, self.whole_root_slice(func.ctx(), root_ty));
                }
            }
        }

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if let Some(obj_alloc) =
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                    && let Some(result) = func.dfg.inst_result(inst)
                    && objref_element_ty(func.ctx(), func.dfg.value_ty(result)).is_some()
                {
                    root_slices.insert(result, self.whole_root_slice(func.ctx(), *obj_alloc.ty()));
                }
            }
        }

        root_slices
    }

    fn tracked_object_from_provenance(
        &mut self,
        func: &Function,
        provenance: RootProvenance,
    ) -> Option<TrackedObject> {
        match provenance {
            RootProvenance::Exact(projection) => Some(TrackedObject::Exact(ObjectSlice {
                root: projection.root_value,
                ty: projection.slice.ty,
                first_leaf: projection.slice.first_leaf,
                leaf_count: projection.slice.leaf_count,
                total_leaves: self.root_total_leaves_for_value(func, projection.root_value)?,
            })),
            RootProvenance::SameRoot(root) => Some(TrackedObject::RootUnknown {
                root,
                total_leaves: self.root_total_leaves_for_value(func, root)?,
            }),
            RootProvenance::Maybe(_) | RootProvenance::Unknown => None,
        }
    }

    fn whole_root_slice(&mut self, ctx: &ModuleCtx, pointee_ty: Type) -> shape::AggregateSlice {
        shape::AggregateSlice {
            ty: pointee_ty,
            first_leaf: 0,
            leaf_count: self.root_leaf_count(ctx, pointee_ty),
        }
    }

    fn root_total_leaves_for_value(&mut self, func: &Function, root: ValueId) -> Option<usize> {
        Some(self.root_leaf_count(
            func.ctx(),
            objref_element_ty(func.ctx(), func.dfg.value_ty(root))?,
        ))
    }

    fn root_leaf_count(&mut self, ctx: &ModuleCtx, ty: Type) -> usize {
        if ty == Type::Unit {
            return 0;
        }
        self.layout_cache
            .shape(ctx, ty)
            .map_or(1, |shape| shape.leaves.len())
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
        live_out_roots: &FxHashMap<ValueId, usize>,
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

fn observed_roots(
    func: &Function,
    inst: InstId,
    possible_roots: &SecondaryMap<ValueId, FxHashSet<ValueId>>,
    skip: &[ValueId],
) -> Vec<ValueId> {
    if downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)).is_some()
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

    fn total_leaves(self) -> usize {
        match self {
            Self::Exact(slice) => slice.total_leaves,
            Self::RootUnknown { total_leaves, .. } => total_leaves,
        }
    }
}

fn objref_element_ty(ctx: &ModuleCtx, ty: Type) -> Option<Type> {
    let sonatina_ir::types::CompoundType::ObjRef(elem) = ty.resolve_compound(ctx)? else {
        return None;
    };
    Some(elem)
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
        let local_object_args = crate::optim::aggregate::collect_local_object_arg_info(&module);
        module.func_store.modify(func_ref, |func| {
            ObjectLoadStore::default().run_for_func(func_ref, func, &local_object_args);
        });

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
}
