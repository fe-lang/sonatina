use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, I256, Immediate, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, cmp, control_flow, data, downcast},
    module::FuncRef,
};

use crate::cfg_edit::{CfgEditor, CleanupMode};

use super::{
    LocalObjectArgInfo, LocalObjectArgMap, Projection, RootInit, RootProvenance,
    cleanup::DeadPureInstCleanup, collect_root_provenance, promotion::SsaBuilder,
    reconstruct::bitcast_before_inst, shape,
};

type LeafValues = SmallVec<[ValueId; 4]>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum RootKind {
    Alloca { inst: InstId },
    ObjAlloc { inst: InstId },
    Arg { index: usize },
    SyntheticOutArg { index: usize },
}

#[derive(Clone)]
struct PromotableRoot {
    root_value: ValueId,
    root_kind: RootKind,
    seed_block: BlockId,
    shape: shape::AggregateShape,
    leaf_vars: SmallVec<[sonatina_ir::builder::Variable; 4]>,
    init: RootInit,
}

#[derive(Default)]
pub struct AggregateScalarize {
    changed: bool,
    dead_pure_cleanup: DeadPureInstCleanup,
    layout_cache: shape::AggregateLayoutCache,
}

impl AggregateScalarize {
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
        let module = func.ctx().clone();
        func.rebuild_users();
        self.assert_cfg_cleaned_up(func);

        let (mut promoted_roots, mut projection_of) =
            self.find_promotable_roots(func, &module, local_object_args);
        let scalarizable = loop {
            let scalarizable = self.compute_scalarizable_aggregates(func, &module, &projection_of);
            let removed = self.filter_promotable_roots(
                func,
                &module,
                &mut promoted_roots,
                &mut projection_of,
                &scalarizable,
            );
            if !removed {
                break scalarizable;
            }
        };
        if !promoted_roots.is_empty() || scalarizable.values().any(|v| *v) {
            self.changed = true;
        } else {
            return false;
        }

        self.canonicalize_promotable_roots(func, &mut promoted_roots);

        let mut ssa = SsaBuilder::new();
        self.append_block_preds(func, &mut ssa);
        self.setup_promoted_leaf_vars(func, &module, &mut ssa, &mut promoted_roots);

        let mut scalarized_agg: SecondaryMap<ValueId, Option<LeafValues>> = SecondaryMap::default();
        let mut scalar_phi_results: SecondaryMap<ValueId, Option<LeafValues>> =
            SecondaryMap::default();
        let mut modified_leaves = FxHashMap::<ValueId, FxHashSet<usize>>::default();

        let agg_phi_insts = self.create_scalar_phi_placeholders(
            func,
            &module,
            &scalarizable,
            &mut scalarized_agg,
            &mut scalar_phi_results,
        );

        let promoted_by_root: FxHashMap<ValueId, PromotableRoot> = promoted_roots
            .into_iter()
            .map(|root| (root.root_value, root))
            .collect();

        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                self.rewrite_promoted_load_store(
                    func,
                    &module,
                    block,
                    inst,
                    &projection_of,
                    &promoted_by_root,
                    &scalarizable,
                    &mut scalarized_agg,
                    &mut ssa,
                    &mut modified_leaves,
                );
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                self.rewrite_scalarizable_bitcast(
                    func,
                    &module,
                    inst,
                    &scalarizable,
                    &mut scalarized_agg,
                );
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                self.rewrite_scalarizable_insert_extract(
                    func,
                    &module,
                    block,
                    inst,
                    &scalarizable,
                    &mut scalarized_agg,
                );
                if !func.layout.is_inst_inserted(inst) {
                    continue;
                }
                self.rewrite_scalarizable_enum_ops(
                    func,
                    &module,
                    inst,
                    &scalarizable,
                    &mut scalarized_agg,
                );
            }
        }

        self.fill_scalar_phi_args(
            func,
            &module,
            &agg_phi_insts,
            &scalar_phi_results,
            &mut scalarized_agg,
        );
        ssa.seal_all(func);
        self.write_back_promoted_arg_roots(
            func,
            &module,
            &promoted_by_root,
            &modified_leaves,
            &mut ssa,
        );
        self.simplify_scalar_phi_results(func, &mut scalar_phi_results);
        self.changed |= self.cleanup_scalarized_artifacts(func, &projection_of, &promoted_by_root);

        if self.changed {
            func.rebuild_users();
        }
        self.changed
    }

    fn assert_cfg_cleaned_up(&self, func: &Function) {
        let Some(entry) = func.layout.entry_block() else {
            return;
        };

        let mut reachable = FxHashSet::default();
        let mut worklist = vec![entry];
        while let Some(block) = worklist.pop() {
            if !reachable.insert(block) {
                continue;
            }
            let Some(term) = func.layout.last_inst_of(block) else {
                continue;
            };
            let Some(branch) = func.dfg.branch_info(term) else {
                continue;
            };
            worklist.extend(branch.dests());
        }

        if let Some(block) = func
            .layout
            .iter_block()
            .find(|block| !reachable.contains(block))
        {
            panic!(
                "AggregateScalarize requires CfgCleanup to remove unreachable blocks first (found unreachable block {})",
                block.as_u32()
            );
        }
    }

    fn append_block_preds(&self, func: &Function, ssa: &mut SsaBuilder) {
        for block in func.layout.iter_block() {
            let Some(term) = func.layout.last_inst_of(block) else {
                continue;
            };
            let Some(branch) = func.dfg.branch_info(term) else {
                continue;
            };
            let mut seen = FxHashSet::default();
            for dest in branch.dests() {
                if seen.insert(dest) {
                    ssa.append_pred(dest, block);
                }
            }
        }
    }

    fn setup_promoted_leaf_vars(
        &self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        ssa: &mut SsaBuilder,
        promoted_roots: &mut [PromotableRoot],
    ) {
        for promoted in promoted_roots {
            self.assert_promotable_root_seed_block(func, promoted);
            for (leaf_idx, leaf) in promoted.shape.leaves.iter().enumerate() {
                let var = ssa.declare_var(leaf.ty);
                promoted.leaf_vars.push(var);
                let init = match promoted.init {
                    RootInit::UndefFresh => func.dfg.make_undef_value(leaf.ty),
                    RootInit::LoadLiveIn => {
                        self.insert_live_in_leaf_load(func, module, promoted, leaf_idx)
                    }
                };
                ssa.def_var(var, init, promoted.seed_block);
            }
        }
    }

    fn canonicalize_promotable_roots(
        &self,
        func: &mut Function,
        promoted_roots: &mut Vec<PromotableRoot>,
    ) {
        if promoted_roots.is_empty() {
            return;
        }

        let mut inst_order = FxHashMap::default();
        for (idx, inst) in func
            .layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .enumerate()
        {
            inst_order.insert(inst, idx);
        }
        promoted_roots.sort_by_key(|promoted| {
            promoted
                .root_inst()
                .and_then(|inst| inst_order.get(&inst).copied())
                .unwrap_or(usize::MAX)
        });

        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        for promoted in promoted_roots {
            let Some(inst) = promoted.root_inst() else {
                continue;
            };
            let block = editor.func().layout.inst_block(inst);
            promoted.seed_block = if first_non_phi_inst(editor.func(), block) == Some(inst) {
                block
            } else {
                editor.split_block_at(inst).1
            };
        }
    }

    fn assert_promotable_root_seed_block(&self, func: &Function, promoted: &PromotableRoot) {
        let Some(inst) = promoted.root_inst() else {
            assert_eq!(
                promoted.seed_block,
                func.layout
                    .entry_block()
                    .expect("function with promoted arg root must have an entry block"),
                "promoted arg root should seed in the entry block"
            );
            return;
        };
        assert_eq!(
            func.layout.inst_block(inst),
            promoted.seed_block,
            "promoted root {:?} should live in its seed block {}",
            promoted.root_kind,
            promoted.seed_block.as_u32()
        );
        assert_eq!(
            first_non_phi_inst(func, promoted.seed_block),
            Some(inst),
            "promoted root {:?} should be first non-phi in seed block {}",
            promoted.root_kind,
            promoted.seed_block.as_u32()
        );
    }

    fn find_promotable_roots(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
    ) -> (
        Vec<PromotableRoot>,
        SecondaryMap<ValueId, Option<Projection>>,
    ) {
        let mut promoted = Vec::new();

        let mut roots: Vec<(ValueId, RootKind, Type, shape::AggregateShape)> = Vec::new();
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                let Some((ptr_value, root_kind, ty)) =
                    downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst))
                        .map(|alloca| {
                            (
                                func.dfg.inst_result(inst),
                                RootKind::Alloca { inst },
                                *alloca.ty(),
                            )
                        })
                        .or_else(|| {
                            downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).map(
                                |obj_alloc| {
                                    (
                                        func.dfg.inst_result(inst),
                                        RootKind::ObjAlloc { inst },
                                        *obj_alloc.ty(),
                                    )
                                },
                            )
                        })
                else {
                    continue;
                };
                let Some(ptr_value) = ptr_value else {
                    continue;
                };
                let Some(shape) = self.aggregate_shape(module, ty) else {
                    continue;
                };
                if shape.leaves.len() > 4 {
                    continue;
                }
                roots.push((ptr_value, root_kind, ty, shape));
            }
        }

        if let Some(local_object_args) = local_object_args {
            for (&idx, &info) in local_object_args {
                let Some(&root_value) = func.arg_values.get(idx) else {
                    continue;
                };
                let Some(root_ty) = objref_element_ty(module, func.dfg.value_ty(root_value)) else {
                    continue;
                };
                let Some(shape) = self.aggregate_shape(module, root_ty) else {
                    continue;
                };
                if shape.leaves.len() > 4 {
                    continue;
                }
                let kind = if info.fresh_result_out {
                    RootKind::SyntheticOutArg { index: idx }
                } else {
                    RootKind::Arg { index: idx }
                };
                roots.push((root_value, kind, root_ty, shape));
            }
        }

        let mut candidate_roots = Vec::new();
        let mut root_slices = FxHashMap::default();
        for (root_value, root_kind, root_ty, shape_data) in roots {
            if root_kind.is_arg_like() && shape_contains_enum(&shape_data) {
                continue;
            }
            // Mutated live-in args are semantically scalarizable, but the current
            // writeback strategy inflates EVM gas by adding entry loads, phis, and
            // return-path stores. Keep the profitability guard here until writeback
            // becomes path-sensitive or these locals can stay expanded in SSA.
            if matches!(root_kind, RootKind::Arg { .. })
                && self.live_in_arg_root_is_mutated(func, root_value)
            {
                continue;
            }
            let whole_slice = shape::AggregateSlice {
                ty: root_ty,
                first_leaf: 0,
                leaf_count: shape_data.leaves.len(),
            };
            root_slices.insert(root_value, whole_slice);
            candidate_roots.push((root_value, root_kind, shape_data));
        }

        let provenance =
            collect_root_provenance(func, module, &root_slices, &mut self.layout_cache, None);
        for (root_value, root_kind, shape_data) in candidate_roots {
            if !self.root_use_chain_is_promotable(func, module, root_value, &provenance) {
                continue;
            }
            promoted.push(PromotableRoot {
                root_value,
                root_kind,
                seed_block: root_kind.inst().map_or_else(
                    || {
                        func.layout
                            .entry_block()
                            .expect("promoted arg root requires an entry block")
                    },
                    |inst| func.layout.inst_block(inst),
                ),
                shape: shape_data,
                leaf_vars: SmallVec::new(),
                init: root_kind.default_init(),
            });
        }

        (promoted, provenance.into_exact_projection())
    }

    fn root_use_chain_is_promotable(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        root_value: ValueId,
        provenance: &super::provenance::RootProvenanceMap,
    ) -> bool {
        let mut dead_use_cache = FxHashMap::default();

        for ptr in func.dfg.value_ids() {
            let Some(projection) = provenance.exact_projection(ptr) else {
                continue;
            };
            if projection.root_value != root_value {
                continue;
            }

            for &user in func.dfg.users(ptr) {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }

                if let Some(gep) = downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(user))
                    && gep.values().first() == Some(&ptr)
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if matches!(
                        provenance.provenance(result),
                        RootProvenance::Exact(next) if next.root_value == root_value
                    ) {
                        continue;
                    }
                }

                if let Some(bitcast) =
                    downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(user))
                    && *bitcast.from() == ptr
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if matches!(
                        provenance.provenance(result),
                        RootProvenance::Exact(next) if next.root_value == root_value
                    ) {
                        continue;
                    }
                }

                if let Some(obj_proj) =
                    downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(user))
                    && obj_proj.values().first() == Some(&ptr)
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if matches!(
                        provenance.provenance(result),
                        RootProvenance::Exact(next) if next.root_value == root_value
                    ) {
                        continue;
                    }
                }

                if let Some(obj_index) =
                    downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(user))
                    && *obj_index.object() == ptr
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if matches!(
                        provenance.provenance(result),
                        RootProvenance::Exact(next) if next.root_value == root_value
                    ) {
                        continue;
                    }
                }

                if let Some(enum_proj) =
                    downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(user))
                    && *enum_proj.object() == ptr
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if matches!(
                        provenance.provenance(result),
                        RootProvenance::Exact(next) if next.root_value == root_value
                    ) {
                        continue;
                    }
                }

                if let Some(phi) =
                    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(user))
                    && phi.args().iter().any(|(arg, _)| *arg == ptr)
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if provenance.exact_projection(result) == Some(projection) {
                        continue;
                    }
                }

                if let Some(mload) = downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(user))
                    && *mload.addr() == ptr
                {
                    if self.projection_slice_can_view_as(module, projection.slice, *mload.ty()) {
                        continue;
                    }
                    return false;
                }

                if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(user))
                    && *obj_load.object() == ptr
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if self.projection_slice_can_view_as(
                        module,
                        projection.slice,
                        func.dfg.value_ty(result),
                    ) {
                        continue;
                    }
                    return false;
                }

                if let Some(enum_get_tag) =
                    downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(user))
                    && *enum_get_tag.object() == ptr
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if self.projection_slice_can_view_as(
                        module,
                        projection.slice,
                        func.dfg.value_ty(result),
                    ) {
                        continue;
                    }
                    return false;
                }

                if let Some(mstore) =
                    downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(user))
                    && *mstore.addr() == ptr
                {
                    if self.projection_slice_can_view_as(module, projection.slice, *mstore.ty()) {
                        continue;
                    }
                    return false;
                }

                if let Some(obj_store) =
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(user))
                    && *obj_store.object() == ptr
                {
                    if self.projection_slice_can_view_as(
                        module,
                        projection.slice,
                        func.dfg.value_ty(*obj_store.value()),
                    ) {
                        continue;
                    }
                    return false;
                }

                if let Some(enum_assert_ref) =
                    downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(user))
                    && *enum_assert_ref.object() == ptr
                {
                    if matches!(
                        projection.slice.ty.resolve_compound(module),
                        Some(sonatina_ir::types::CompoundType::Enum(_))
                    ) {
                        continue;
                    }
                    return false;
                }

                if let Some(enum_set_tag) =
                    downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(user))
                    && *enum_set_tag.object() == ptr
                {
                    if matches!(
                        projection.slice.ty.resolve_compound(module),
                        Some(sonatina_ir::types::CompoundType::Enum(_))
                    ) {
                        continue;
                    }
                    return false;
                }

                if let Some(enum_write_variant) =
                    downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(user))
                    && *enum_write_variant.object() == ptr
                {
                    if matches!(
                        projection.slice.ty.resolve_compound(module),
                        Some(sonatina_ir::types::CompoundType::Enum(_))
                    ) {
                        continue;
                    }
                    return false;
                }

                if is_dead_inst_tree(func, user, &mut dead_use_cache, &mut FxHashSet::default()) {
                    continue;
                }

                return false;
            }
        }

        true
    }

    fn live_in_arg_root_is_mutated(&self, func: &Function, root_value: ValueId) -> bool {
        let mut worklist = vec![root_value];
        let mut seen = FxHashSet::default();

        while let Some(value) = worklist.pop() {
            if !seen.insert(value) {
                continue;
            }

            for &user in func.dfg.users(value) {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }

                if let Some(proj) = downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(user))
                    && proj.values().first() == Some(&value)
                {
                    if let Some(result) = func.dfg.inst_result(user) {
                        worklist.push(result);
                    }
                    continue;
                }

                if let Some(index) =
                    downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(user))
                    && *index.object() == value
                {
                    if let Some(result) = func.dfg.inst_result(user) {
                        worklist.push(result);
                    }
                    continue;
                }

                if let Some(enum_proj) =
                    downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(user))
                    && *enum_proj.object() == value
                {
                    if let Some(result) = func.dfg.inst_result(user) {
                        worklist.push(result);
                    }
                    continue;
                }

                if let Some(phi) =
                    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(user))
                    && phi.args().iter().any(|(arg, _)| *arg == value)
                {
                    if let Some(result) = func.dfg.inst_result(user) {
                        worklist.push(result);
                    }
                    continue;
                }

                if downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(user))
                    .is_some_and(|obj_store| *obj_store.object() == value)
                    || downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(user))
                        .is_some_and(|mstore| *mstore.addr() == value)
                    || downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(user))
                        .is_some_and(|enum_set_tag| *enum_set_tag.object() == value)
                    || downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(user))
                        .is_some_and(|enum_write_variant| *enum_write_variant.object() == value)
                {
                    return true;
                }
            }
        }

        false
    }

    fn filter_promotable_roots(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        promoted_roots: &mut Vec<PromotableRoot>,
        projection_of: &mut SecondaryMap<ValueId, Option<Projection>>,
        scalarizable: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        let before = promoted_roots.len();
        promoted_roots.retain(|promoted| {
            self.promotable_root_can_scalarize(
                func,
                module,
                promoted.root_value,
                projection_of,
                scalarizable,
            )
        });

        let kept: FxHashSet<ValueId> = promoted_roots
            .iter()
            .map(|promoted| promoted.root_value)
            .collect();
        for value in func.dfg.value_ids() {
            if let Some(projection) = projection_of[value]
                && !kept.contains(&projection.root_value)
            {
                projection_of[value] = None;
            }
        }
        promoted_roots.len() != before
    }

    fn promotable_root_can_scalarize(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        root_value: ValueId,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        scalarizable: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        for ptr in func.dfg.value_ids() {
            let Some(projection) = projection_of[ptr] else {
                continue;
            };
            if projection.root_value != root_value {
                continue;
            }

            for &user in func.dfg.users(ptr) {
                if !func.layout.is_inst_inserted(user) {
                    continue;
                }
                if let Some(mload) = downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(user))
                    && *mload.addr() == ptr
                    && shape::is_supported_scalar_shape_ty(module, *mload.ty())
                {
                    let Some(result) = func.dfg.inst_result(user) else {
                        return false;
                    };
                    if !scalarizable[result] {
                        return false;
                    }
                }
                if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(user))
                    && *obj_load.object() == ptr
                    && let Some(result) = func.dfg.inst_result(user)
                    && shape::is_supported_scalar_shape_ty(module, func.dfg.value_ty(result))
                    && !scalarizable[result]
                {
                    return false;
                }
                if let Some(mstore) =
                    downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(user))
                    && *mstore.addr() == ptr
                    && shape::is_supported_scalar_shape_ty(module, *mstore.ty())
                    && (!scalarizable[*mstore.value()]
                        || func.dfg.value_ty(*mstore.value()) != *mstore.ty())
                {
                    return false;
                }
                if let Some(obj_store) =
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(user))
                    && *obj_store.object() == ptr
                {
                    let value_ty = func.dfg.value_ty(*obj_store.value());
                    if shape::is_supported_scalar_shape_ty(module, value_ty)
                        && !scalarizable[*obj_store.value()]
                    {
                        return false;
                    }
                }
                if let Some(enum_get_tag) =
                    downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(user))
                    && *enum_get_tag.object() == ptr
                {
                    continue;
                }
                if let Some(enum_assert_ref) =
                    downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(user))
                    && *enum_assert_ref.object() == ptr
                {
                    continue;
                }
                if let Some(enum_set_tag) =
                    downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(user))
                    && *enum_set_tag.object() == ptr
                {
                    continue;
                }
                if let Some(enum_write_variant) =
                    downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(user))
                    && *enum_write_variant.object() == ptr
                {
                    for &payload in enum_write_variant.values() {
                        let payload_ty = func.dfg.value_ty(payload);
                        if shape::is_supported_scalar_shape_ty(module, payload_ty)
                            && !scalarizable[payload]
                        {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }

    fn compute_scalarizable_aggregates(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
    ) -> SecondaryMap<ValueId, bool> {
        let mut scalarizable: SecondaryMap<ValueId, bool> = SecondaryMap::default();

        for value in func.dfg.value_ids() {
            let ty = func.dfg.value_ty(value);
            if !shape::is_supported_scalar_shape_ty(module, ty) {
                continue;
            }
            let ok = match func.dfg.value(value) {
                Value::Undef { .. } => true,
                Value::Arg { .. } => false,
                Value::Immediate { .. } | Value::Global { .. } => false,
                Value::Inst { inst, .. } => {
                    if func.dfg.call_info(*inst).is_some() {
                        false
                    } else if downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(*inst))
                        .is_some()
                        || downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(*inst))
                            .is_some()
                        || downcast::<&data::EnumMake>(func.inst_set(), func.dfg.inst(*inst))
                            .is_some()
                        || downcast::<&data::EnumExtract>(func.inst_set(), func.dfg.inst(*inst))
                            .is_some()
                        || downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(*inst))
                            .is_some()
                    {
                        true
                    } else if let Some(bitcast) =
                        downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(*inst))
                    {
                        self.aggregate_bitcast_is_scalarizable(
                            module,
                            func.dfg.value_ty(*bitcast.from()),
                            ty,
                        )
                    } else if let Some(mload) =
                        downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(*inst))
                    {
                        projection_of[*mload.addr()].is_some()
                    } else if let Some(obj_load) =
                        downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(*inst))
                    {
                        projection_of[*obj_load.object()].is_some()
                    } else {
                        false
                    }
                }
            };
            scalarizable[value] = ok;
        }

        loop {
            let mut changed = false;
            for value in func.dfg.value_ids() {
                if !scalarizable[value] {
                    continue;
                }
                if !self.scalarizable_definition_is_closed(
                    func,
                    module,
                    projection_of,
                    &scalarizable,
                    value,
                ) || !self.scalarizable_uses_are_closed(
                    func,
                    module,
                    projection_of,
                    &scalarizable,
                    value,
                ) {
                    scalarizable[value] = false;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        scalarizable
    }

    fn scalarizable_definition_is_closed(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        scalarizable: &SecondaryMap<ValueId, bool>,
        value: ValueId,
    ) -> bool {
        match func.dfg.value(value) {
            Value::Undef { .. } => true,
            Value::Arg { .. } | Value::Immediate { .. } | Value::Global { .. } => false,
            Value::Inst { inst, .. } => {
                if let Some(insert) =
                    downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let agg_ty = func.dfg.value_ty(value);
                    let Some(idx) = shape::const_u32(&func.dfg, *insert.idx()) else {
                        return false;
                    };
                    let Some(slice) = shape::aggregate_slice_for_index(module, agg_ty, idx) else {
                        return false;
                    };
                    if func.dfg.value_ty(*insert.dest()) != agg_ty || !scalarizable[*insert.dest()]
                    {
                        return false;
                    }
                    if func.dfg.value_ty(*insert.value()) != slice.ty {
                        return false;
                    }
                    if shape::is_supported_scalar_shape_ty(module, slice.ty)
                        && !scalarizable[*insert.value()]
                    {
                        return false;
                    }
                    true
                } else if let Some(enum_make) =
                    downcast::<&data::EnumMake>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let result_ty = func.dfg.value_ty(value);
                    if result_ty != *enum_make.ty() {
                        return false;
                    }
                    let Type::Compound(enum_ty) = result_ty else {
                        return false;
                    };
                    if enum_ty != enum_make.variant().enum_ty() {
                        return false;
                    }
                    let variant_data = func.ctx().with_ty_store(|store| {
                        store.enum_variant_data(*enum_make.variant()).cloned()
                    });
                    let Some(variant_data) = variant_data else {
                        return false;
                    };
                    if variant_data.fields.len() != enum_make.values().len() {
                        return false;
                    }
                    for (&field_ty, &payload) in variant_data.fields.iter().zip(enum_make.values())
                    {
                        if func.dfg.value_ty(payload) != field_ty {
                            return false;
                        }
                        if shape::is_supported_scalar_shape_ty(module, field_ty)
                            && !scalarizable[payload]
                        {
                            return false;
                        }
                    }
                    true
                } else if let Some(extract) =
                    downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let src_ty = func.dfg.value_ty(*extract.dest());
                    if !shape::is_supported_scalar_shape_ty(module, src_ty)
                        || !scalarizable[*extract.dest()]
                    {
                        return false;
                    }
                    let Some(idx) = shape::const_u32(&func.dfg, *extract.idx()) else {
                        return false;
                    };
                    let Some(slice) = shape::aggregate_slice_for_index(module, src_ty, idx) else {
                        return false;
                    };
                    slice.ty == func.dfg.value_ty(value)
                } else if let Some(enum_extract) =
                    downcast::<&data::EnumExtract>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let src_ty = func.dfg.value_ty(*enum_extract.value());
                    if !matches!(
                        src_ty.resolve_compound(module),
                        Some(sonatina_ir::types::CompoundType::Enum(_))
                    ) || !scalarizable[*enum_extract.value()]
                    {
                        return false;
                    }
                    let Some(field_idx) = shape::const_u32(&func.dfg, *enum_extract.field()) else {
                        return false;
                    };
                    let Some(slice) = shape::enum_variant_field_slice(
                        module,
                        src_ty,
                        *enum_extract.variant(),
                        field_idx,
                    ) else {
                        return false;
                    };
                    slice.ty == func.dfg.value_ty(value)
                } else if let Some(phi) =
                    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let value_ty = func.dfg.value_ty(value);
                    phi.args()
                        .iter()
                        .all(|&(arg, _)| scalarizable[arg] && func.dfg.value_ty(arg) == value_ty)
                } else if let Some(mload) =
                    downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(*inst))
                {
                    shape::is_supported_scalar_shape_ty(module, *mload.ty())
                        && projection_of[*mload.addr()].is_some()
                        && *mload.ty() == func.dfg.value_ty(value)
                } else if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let value_ty = func.dfg.value_ty(value);
                    shape::is_supported_scalar_shape_ty(module, value_ty)
                        && projection_of[*obj_load.object()].is_some()
                } else if let Some(bitcast) =
                    downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(*inst))
                {
                    let from_ty = func.dfg.value_ty(*bitcast.from());
                    if !self.aggregate_bitcast_is_scalarizable(
                        module,
                        from_ty,
                        func.dfg.value_ty(value),
                    ) {
                        return false;
                    }
                    if shape::is_supported_scalar_shape_ty(module, from_ty) {
                        scalarizable[*bitcast.from()]
                    } else {
                        true
                    }
                } else {
                    false
                }
            }
        }
    }

    fn scalarizable_uses_are_closed(
        &mut self,
        func: &Function,
        module: &sonatina_ir::module::ModuleCtx,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        scalarizable: &SecondaryMap<ValueId, bool>,
        value: ValueId,
    ) -> bool {
        for &user in func.dfg.users(value) {
            if !func.layout.is_inst_inserted(user) {
                continue;
            }

            if let Some(insert) =
                downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(user))
                && (*insert.dest() == value || *insert.value() == value)
            {
                let Some(res) = func.dfg.inst_result(user) else {
                    return false;
                };
                if !scalarizable[res] {
                    return false;
                }
                continue;
            }

            if let Some(extract) =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(user))
                && *extract.dest() == value
            {
                let Some(res) = func.dfg.inst_result(user) else {
                    return false;
                };
                let res_ty = func.dfg.value_ty(res);
                if shape::is_supported_scalar_shape_ty(module, res_ty) && !scalarizable[res] {
                    return false;
                }
                continue;
            }

            if let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(user))
                && phi.args().iter().any(|(arg, _)| *arg == value)
            {
                let Some(res) = func.dfg.inst_result(user) else {
                    return false;
                };
                if !scalarizable[res] {
                    return false;
                }
                continue;
            }

            if let Some(enum_tag) = downcast::<&data::EnumTag>(func.inst_set(), func.dfg.inst(user))
                && *enum_tag.value() == value
            {
                continue;
            }

            if let Some(enum_is_variant) =
                downcast::<&data::EnumIsVariant>(func.inst_set(), func.dfg.inst(user))
                && *enum_is_variant.value() == value
            {
                continue;
            }

            if let Some(enum_assert) =
                downcast::<&data::EnumAssertVariant>(func.inst_set(), func.dfg.inst(user))
                && *enum_assert.value() == value
            {
                continue;
            }

            if let Some(enum_extract) =
                downcast::<&data::EnumExtract>(func.inst_set(), func.dfg.inst(user))
                && *enum_extract.value() == value
            {
                let Some(res) = func.dfg.inst_result(user) else {
                    return false;
                };
                let res_ty = func.dfg.value_ty(res);
                if shape::is_supported_scalar_shape_ty(module, res_ty) && !scalarizable[res] {
                    return false;
                }
                continue;
            }

            if let Some(mstore) = downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(user))
                && *mstore.value() == value
            {
                if !shape::is_supported_scalar_shape_ty(module, *mstore.ty()) {
                    return false;
                }
                if projection_of[*mstore.addr()].is_none() {
                    return false;
                }
                continue;
            }

            if let Some(obj_store) =
                downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(user))
                && *obj_store.value() == value
            {
                if !shape::is_supported_scalar_shape_ty(module, func.dfg.value_ty(value)) {
                    return false;
                }
                if projection_of[*obj_store.object()].is_none() {
                    return false;
                }
                continue;
            }

            if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(user))
                && *bitcast.from() == value
            {
                let Some(res) = func.dfg.inst_result(user) else {
                    return false;
                };
                let res_ty = func.dfg.value_ty(res);
                if !self.aggregate_bitcast_is_scalarizable(module, func.dfg.value_ty(value), res_ty)
                {
                    return false;
                }
                if shape::is_supported_scalar_shape_ty(module, res_ty) && !scalarizable[res] {
                    return false;
                }
                continue;
            }

            return false;
        }
        true
    }

    fn create_scalar_phi_placeholders(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        scalarizable: &SecondaryMap<ValueId, bool>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
        scalar_phi_results: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) -> Vec<InstId> {
        let mut phis = Vec::new();
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_none() {
                    continue;
                }
                let Some(result) = func.dfg.inst_result(inst) else {
                    continue;
                };
                if !scalarizable[result] {
                    continue;
                }
                let agg_ty = func.dfg.value_ty(result);
                let shape = self
                    .aggregate_shape(module, agg_ty)
                    .unwrap_or_else(|| panic!("missing aggregate shape for scalarizable phi"));

                let mut leaf_phis: LeafValues = SmallVec::new();
                for leaf in shape.leaves {
                    let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(block));
                    let phi = control_flow::Phi::new_unchecked(func.inst_set(), Vec::new());
                    let phi_inst = cursor.prepend_inst_data(func, phi);
                    let phi_res = func.dfg.make_value(Value::Inst {
                        inst: phi_inst,
                        result_idx: 0,
                        ty: leaf.ty,
                    });
                    cursor.attach_result(func, phi_inst, phi_res);
                    leaf_phis.push(phi_res);
                }
                scalar_phi_results[result] = Some(leaf_phis.clone());
                scalarized_agg[result] = Some(leaf_phis);
                phis.push(inst);
            }
        }
        phis
    }

    #[allow(clippy::too_many_arguments)]
    fn rewrite_promoted_load_store(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        block: BlockId,
        inst: InstId,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        promoted_by_root: &FxHashMap<ValueId, PromotableRoot>,
        scalarizable: &SecondaryMap<ValueId, bool>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
        ssa: &mut SsaBuilder,
        modified_leaves: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    ) {
        if let Some((projection_value, ty, result)) =
            downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
                .map(|mload| (*mload.addr(), *mload.ty(), func.dfg.inst_result(inst)))
                .or_else(|| {
                    downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)).map(
                        |obj_load| {
                            let result = func.dfg.inst_result(inst);
                            let ty = result
                                .map(|result| func.dfg.value_ty(result))
                                .unwrap_or(Type::Unit);
                            (*obj_load.object(), ty, result)
                        },
                    )
                })
        {
            let Some(projection) = projection_of[projection_value] else {
                return;
            };
            let Some(promoted) = promoted_by_root.get(&projection.root_value) else {
                return;
            };
            let Some(result) = result else {
                return;
            };
            let leaf_range = projection.slice.first_leaf
                ..projection.slice.first_leaf + projection.slice.leaf_count;
            let underlying_leaves = &promoted.shape.leaves[leaf_range.clone()];
            if shape::is_supported_scalar_shape_ty(module, ty) {
                if !scalarizable[result] {
                    return;
                }
                let Some(view_leaf_tys) = self.projection_view_leaf_tys(module, ty) else {
                    return;
                };
                if view_leaf_tys.len() != underlying_leaves.len() {
                    return;
                }
                let mut leaves: LeafValues = SmallVec::new();
                for (i, (underlying_leaf, view_ty)) in
                    underlying_leaves.iter().zip(view_leaf_tys).enumerate()
                {
                    let var = promoted.leaf_vars[projection.slice.first_leaf + i];
                    let value = ssa.use_var(func, var, block);
                    leaves.push(bitcast_before_inst(
                        func,
                        inst,
                        value,
                        underlying_leaf.ty,
                        view_ty,
                    ));
                }
                scalarized_agg[result] = Some(leaves);
                return;
            }

            if projection.slice.leaf_count != 1 {
                return;
            }
            let underlying_leaf = &underlying_leaves[0];
            let var = promoted.leaf_vars[projection.slice.first_leaf];
            let val = ssa.use_var(func, var, block);
            let val = bitcast_before_inst(func, inst, val, underlying_leaf.ty, ty);
            func.dfg.change_to_alias(result, val);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        if let Some(enum_get_tag) =
            downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst))
        {
            let Some(projection) = projection_of[*enum_get_tag.object()] else {
                return;
            };
            let Some(promoted) = promoted_by_root.get(&projection.root_value) else {
                return;
            };
            let Some(tag_slice) = shape::enum_tag_slice(module, projection.slice.ty) else {
                return;
            };
            let leaf_idx = projection.slice.first_leaf + tag_slice.first_leaf;
            let Some(result) = func.dfg.inst_result(inst) else {
                return;
            };
            let underlying_leaf = &promoted.shape.leaves[leaf_idx];
            let value = ssa.use_var(func, promoted.leaf_vars[leaf_idx], block);
            let replacement = bitcast_before_inst(
                func,
                inst,
                value,
                underlying_leaf.ty,
                func.dfg.value_ty(result),
            );
            func.dfg.change_to_alias(result, replacement);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        if let Some(enum_set_tag) =
            downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst))
        {
            let Some(projection) = projection_of[*enum_set_tag.object()] else {
                return;
            };
            let Some(promoted) = promoted_by_root.get(&projection.root_value) else {
                return;
            };
            let Some(tag_slice) = shape::enum_tag_slice(module, projection.slice.ty) else {
                return;
            };
            let leaf_idx = projection.slice.first_leaf + tag_slice.first_leaf;
            let leaf = &promoted.shape.leaves[leaf_idx];
            let tag = func
                .dfg
                .make_imm_value(enum_variant_tag_imm(*enum_set_tag.variant(), leaf.ty));
            ssa.def_var(promoted.leaf_vars[leaf_idx], tag, block);
            record_modified_leaves(
                modified_leaves,
                projection.root_value,
                leaf_idx..leaf_idx + tag_slice.leaf_count,
            );
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        if let Some(enum_write_variant) =
            downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let Some(projection) = projection_of[*enum_write_variant.object()] else {
                return;
            };
            let Some(promoted) = promoted_by_root.get(&projection.root_value) else {
                return;
            };
            let enum_ty = projection.slice.ty;
            for (field_idx, &payload) in enum_write_variant.values().iter().enumerate() {
                let field_idx = u32::try_from(field_idx).ok();
                let Some(field_idx) = field_idx else {
                    return;
                };
                let Some(field_slice) = shape::enum_variant_field_slice(
                    module,
                    enum_ty,
                    *enum_write_variant.variant(),
                    field_idx,
                ) else {
                    return;
                };
                let payload_ty = field_slice.ty;
                let Some(payload_leaves) = self.scalarized_leaves_of_value(
                    func,
                    module,
                    payload,
                    payload_ty,
                    scalarized_agg,
                ) else {
                    return;
                };
                let Some(view_leaf_tys) = self.projection_view_leaf_tys(module, payload_ty) else {
                    return;
                };
                let base_leaf = projection.slice.first_leaf + field_slice.first_leaf;
                if payload_leaves.len() != field_slice.leaf_count
                    || view_leaf_tys.len() != field_slice.leaf_count
                {
                    return;
                }
                for (i, ((payload_leaf, view_ty), underlying_leaf)) in payload_leaves
                    .into_iter()
                    .zip(view_leaf_tys)
                    .zip(
                        promoted.shape.leaves[base_leaf..base_leaf + field_slice.leaf_count].iter(),
                    )
                    .enumerate()
                {
                    let leaf_idx = base_leaf + i;
                    let stored =
                        bitcast_before_inst(func, inst, payload_leaf, view_ty, underlying_leaf.ty);
                    ssa.def_var(promoted.leaf_vars[leaf_idx], stored, block);
                }
                record_modified_leaves(
                    modified_leaves,
                    projection.root_value,
                    base_leaf..base_leaf + field_slice.leaf_count,
                );
            }
            let Some(tag_slice) = shape::enum_tag_slice(module, enum_ty) else {
                return;
            };
            let tag_leaf_idx = projection.slice.first_leaf + tag_slice.first_leaf;
            let tag_leaf = &promoted.shape.leaves[tag_leaf_idx];
            let tag = func.dfg.make_imm_value(enum_variant_tag_imm(
                *enum_write_variant.variant(),
                tag_leaf.ty,
            ));
            ssa.def_var(promoted.leaf_vars[tag_leaf_idx], tag, block);
            record_modified_leaves(
                modified_leaves,
                projection.root_value,
                tag_leaf_idx..tag_leaf_idx + tag_slice.leaf_count,
            );
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        let Some((projection_value, value, ty)) =
            downcast::<&data::Mstore>(func.inst_set(), func.dfg.inst(inst))
                .map(|mstore| (*mstore.addr(), *mstore.value(), *mstore.ty()))
                .or_else(|| {
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)).map(
                        |obj_store| {
                            let value = *obj_store.value();
                            (*obj_store.object(), value, func.dfg.value_ty(value))
                        },
                    )
                })
        else {
            return;
        };
        let Some(projection) = projection_of[projection_value] else {
            return;
        };
        let Some(promoted) = promoted_by_root.get(&projection.root_value) else {
            return;
        };
        let leaf_range =
            projection.slice.first_leaf..projection.slice.first_leaf + projection.slice.leaf_count;
        let underlying_leaves = &promoted.shape.leaves[leaf_range.clone()];

        if shape::is_supported_scalar_shape_ty(module, ty) {
            let Some(payload_leaves) =
                self.scalarized_leaves_of_value(func, module, value, ty, scalarized_agg)
            else {
                return;
            };
            let Some(view_leaf_tys) = self.projection_view_leaf_tys(module, ty) else {
                return;
            };
            if payload_leaves.len() != projection.slice.leaf_count
                || view_leaf_tys.len() != underlying_leaves.len()
            {
                return;
            }
            for (i, ((val, view_ty), underlying_leaf)) in payload_leaves
                .into_iter()
                .zip(view_leaf_tys)
                .zip(underlying_leaves.iter())
                .enumerate()
            {
                let var = promoted.leaf_vars[projection.slice.first_leaf + i];
                let stored = bitcast_before_inst(func, inst, val, view_ty, underlying_leaf.ty);
                ssa.def_var(var, stored, block);
            }
            record_modified_leaves(modified_leaves, projection.root_value, leaf_range);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        if projection.slice.leaf_count != 1 {
            return;
        }
        let underlying_leaf = &underlying_leaves[0];
        let var = promoted.leaf_vars[projection.slice.first_leaf];
        let stored = bitcast_before_inst(func, inst, value, ty, underlying_leaf.ty);
        ssa.def_var(var, stored, block);
        record_modified_leaves(modified_leaves, projection.root_value, leaf_range);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn rewrite_scalarizable_bitcast(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        inst: InstId,
        scalarizable: &SecondaryMap<ValueId, bool>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        let Some(bitcast) =
            downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)).cloned()
        else {
            return;
        };
        let Some(result) = func.dfg.inst_result(inst) else {
            return;
        };
        let from = *bitcast.from();
        let from_ty = func.dfg.value_ty(from);
        let result_ty = func.dfg.value_ty(result);
        let from_is_agg = shape::is_supported_scalar_shape_ty(module, from_ty);
        let result_is_agg = shape::is_supported_scalar_shape_ty(module, result_ty);
        if !from_is_agg && !result_is_agg {
            return;
        }

        if from_is_agg && result_is_agg {
            if !scalarizable[result] {
                return;
            }
            let Some((src_leaves, dst_leaves)) =
                self.compatible_aggregate_bitcast_runtime_leaves(module, from_ty, result_ty)
            else {
                return;
            };
            let Some(source_leaves) =
                self.scalarized_leaves_of_value(func, module, from, from_ty, scalarized_agg)
            else {
                return;
            };
            if source_leaves.len() != src_leaves.len() {
                return;
            }

            let mut mapped = LeafValues::new();
            for ((source, src_leaf), dst_leaf) in
                source_leaves.into_iter().zip(src_leaves).zip(dst_leaves)
            {
                let value = bitcast_before_inst(func, inst, source, src_leaf.ty, dst_leaf.ty);
                mapped.push(value);
            }
            scalarized_agg[result] = Some(mapped);
            return;
        }

        if result_is_agg {
            if !scalarizable[result] {
                return;
            }
            let Some(dst_leaf) = self.aggregate_single_runtime_word_leaf(module, result_ty) else {
                return;
            };
            let mut leaves = LeafValues::new();
            let value = bitcast_before_inst(func, inst, from, from_ty, dst_leaf.ty);
            leaves.push(value);
            scalarized_agg[result] = Some(leaves);
            return;
        }

        let Some(src_leaf) = self.aggregate_single_runtime_word_leaf(module, from_ty) else {
            return;
        };
        let Some(source_leaves) =
            self.scalarized_leaves_of_value(func, module, from, from_ty, scalarized_agg)
        else {
            return;
        };
        let [source] = source_leaves.as_slice() else {
            return;
        };
        let replacement = bitcast_before_inst(func, inst, *source, src_leaf.ty, result_ty);
        func.dfg.change_to_alias(result, replacement);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn rewrite_scalarizable_insert_extract(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        _block: BlockId,
        inst: InstId,
        scalarizable: &SecondaryMap<ValueId, bool>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        if let Some(insert) =
            downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let Some(result) = func.dfg.inst_result(inst) else {
                return;
            };
            if !scalarizable[result] {
                return;
            }
            let agg_ty = func.dfg.value_ty(result);
            let Some(idx) = shape::const_u32(&func.dfg, *insert.idx()) else {
                return;
            };
            let Some(slice) = shape::aggregate_slice_for_index(module, agg_ty, idx) else {
                return;
            };

            let Some(mut base_leaves) = self.scalarized_leaves_of_value(
                func,
                module,
                *insert.dest(),
                agg_ty,
                scalarized_agg,
            ) else {
                return;
            };
            let Some(payload_leaves) = self.scalarized_leaves_of_value(
                func,
                module,
                *insert.value(),
                slice.ty,
                scalarized_agg,
            ) else {
                return;
            };
            if payload_leaves.len() != slice.leaf_count {
                return;
            }
            for (i, val) in payload_leaves.into_iter().enumerate() {
                base_leaves[slice.first_leaf + i] = val;
            }
            scalarized_agg[result] = Some(base_leaves);
            return;
        }

        let Some(extract) =
            downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst)).cloned()
        else {
            return;
        };
        let Some(result) = func.dfg.inst_result(inst) else {
            return;
        };
        let dest_ty = func.dfg.value_ty(*extract.dest());
        if !shape::is_supported_scalar_shape_ty(module, dest_ty) {
            return;
        }
        let Some(dest_leaves) =
            self.scalarized_leaves_of_value(func, module, *extract.dest(), dest_ty, scalarized_agg)
        else {
            return;
        };
        let Some(idx) = shape::const_u32(&func.dfg, *extract.idx()) else {
            return;
        };
        let Some(slice) = shape::aggregate_slice_for_index(module, dest_ty, idx) else {
            return;
        };
        let result_ty = func.dfg.value_ty(result);
        if shape::is_supported_scalar_shape_ty(module, result_ty) {
            if !scalarizable[result] {
                return;
            }
            let mut leaves = LeafValues::new();
            for i in 0..slice.leaf_count {
                leaves.push(dest_leaves[slice.first_leaf + i]);
            }
            scalarized_agg[result] = Some(leaves);
            return;
        }

        let replacement = dest_leaves[slice.first_leaf];
        func.dfg.change_to_alias(result, replacement);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn rewrite_scalarizable_enum_ops(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        inst: InstId,
        scalarizable: &SecondaryMap<ValueId, bool>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        if let Some(enum_make) =
            downcast::<&data::EnumMake>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let Some(result) = func.dfg.inst_result(inst) else {
                return;
            };
            if !scalarizable[result] {
                return;
            }
            let enum_ty = func.dfg.value_ty(result);
            let Some(shape) = self.aggregate_shape(module, enum_ty) else {
                return;
            };
            let mut leaves = LeafValues::new();
            for leaf in &shape.leaves {
                leaves.push(func.dfg.make_undef_value(leaf.ty));
            }
            let Some(tag_slice) = shape::enum_tag_slice(module, enum_ty) else {
                return;
            };
            leaves[tag_slice.first_leaf] = func.dfg.make_imm_value(enum_variant_tag_imm(
                *enum_make.variant(),
                shape.leaves[tag_slice.first_leaf].ty,
            ));
            for (field_idx, &payload) in enum_make.values().iter().enumerate() {
                let field_idx = u32::try_from(field_idx).ok();
                let Some(field_idx) = field_idx else {
                    return;
                };
                let Some(field_slice) = shape::enum_variant_field_slice(
                    module,
                    enum_ty,
                    *enum_make.variant(),
                    field_idx,
                ) else {
                    return;
                };
                let Some(payload_leaves) = self.scalarized_leaves_of_value(
                    func,
                    module,
                    payload,
                    field_slice.ty,
                    scalarized_agg,
                ) else {
                    return;
                };
                if payload_leaves.len() != field_slice.leaf_count {
                    return;
                }
                for (i, payload_leaf) in payload_leaves.into_iter().enumerate() {
                    leaves[field_slice.first_leaf + i] = payload_leaf;
                }
            }
            scalarized_agg[result] = Some(leaves);
            return;
        }

        if let Some(enum_tag) = downcast::<&data::EnumTag>(func.inst_set(), func.dfg.inst(inst)) {
            let Some(result) = func.dfg.inst_result(inst) else {
                return;
            };
            let enum_ty = func.dfg.value_ty(*enum_tag.value());
            let Some(enum_leaves) = self.scalarized_leaves_of_value(
                func,
                module,
                *enum_tag.value(),
                enum_ty,
                scalarized_agg,
            ) else {
                return;
            };
            let Some(tag_slice) = shape::enum_tag_slice(module, enum_ty) else {
                return;
            };
            let replacement = bitcast_before_inst(
                func,
                inst,
                enum_leaves[tag_slice.first_leaf],
                shape::enum_tag_ty(enum_ty).unwrap_or(func.dfg.value_ty(result)),
                func.dfg.value_ty(result),
            );
            func.dfg.change_to_alias(result, replacement);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        if let Some(enum_is_variant) =
            downcast::<&data::EnumIsVariant>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let Some(result) = func.dfg.inst_result(inst) else {
                return;
            };
            let enum_ty = func.dfg.value_ty(*enum_is_variant.value());
            let Some(enum_leaves) = self.scalarized_leaves_of_value(
                func,
                module,
                *enum_is_variant.value(),
                enum_ty,
                scalarized_agg,
            ) else {
                return;
            };
            let Some(tag_slice) = shape::enum_tag_slice(module, enum_ty) else {
                return;
            };
            let tag = enum_leaves[tag_slice.first_leaf];
            let tag_match = func.dfg.make_imm_value(enum_variant_tag_imm(
                *enum_is_variant.variant(),
                func.dfg.value_ty(tag),
            ));
            let eq = eq_before_inst(func, inst, tag, tag_match);
            func.dfg.change_to_alias(result, eq);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return;
        }

        let Some(enum_extract) =
            downcast::<&data::EnumExtract>(func.inst_set(), func.dfg.inst(inst)).cloned()
        else {
            return;
        };
        let Some(result) = func.dfg.inst_result(inst) else {
            return;
        };
        let enum_ty = func.dfg.value_ty(*enum_extract.value());
        let Some(enum_leaves) = self.scalarized_leaves_of_value(
            func,
            module,
            *enum_extract.value(),
            enum_ty,
            scalarized_agg,
        ) else {
            return;
        };
        let Some(field_idx) = shape::const_u32(&func.dfg, *enum_extract.field()) else {
            return;
        };
        let Some(field_slice) =
            shape::enum_variant_field_slice(module, enum_ty, *enum_extract.variant(), field_idx)
        else {
            return;
        };
        if shape::is_supported_scalar_shape_ty(module, func.dfg.value_ty(result)) {
            if !scalarizable[result] || field_slice.leaf_count == 0 {
                return;
            }
            let mut leaves = LeafValues::new();
            for i in 0..field_slice.leaf_count {
                leaves.push(enum_leaves[field_slice.first_leaf + i]);
            }
            scalarized_agg[result] = Some(leaves);
            return;
        }
        if field_slice.leaf_count != 1 {
            return;
        }
        let replacement = enum_leaves[field_slice.first_leaf];
        func.dfg.change_to_alias(result, replacement);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
    }

    fn fill_scalar_phi_args(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        agg_phi_insts: &[InstId],
        scalar_phi_results: &SecondaryMap<ValueId, Option<LeafValues>>,
        scalarized_agg: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        for &inst in agg_phi_insts {
            if !func.layout.is_inst_inserted(inst) {
                continue;
            }
            let Some(result) = func.dfg.inst_result(inst) else {
                continue;
            };
            let agg_ty = func.dfg.value_ty(result);
            let Some(phi) =
                downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).cloned()
            else {
                continue;
            };
            let Some(leaf_phis) = scalar_phi_results[result].clone() else {
                continue;
            };

            for &(incoming, pred) in phi.args() {
                let Some(incoming_leaves) =
                    self.scalarized_leaves_of_value(func, module, incoming, agg_ty, scalarized_agg)
                else {
                    panic!("aggregate phi incoming value is not scalarized");
                };
                if incoming_leaves.len() != leaf_phis.len() {
                    panic!("aggregate phi scalar leaf mismatch");
                }
                for (leaf_phi, leaf_val) in leaf_phis.iter().zip(incoming_leaves.iter()) {
                    let phi_inst = func
                        .dfg
                        .value_inst(*leaf_phi)
                        .unwrap_or_else(|| panic!("scalar phi value has no defining inst"));
                    func.dfg.append_phi_arg(phi_inst, *leaf_val, pred);
                }
            }

            scalarized_agg[result] = Some(leaf_phis);
        }
    }

    fn simplify_scalar_phi_results(
        &mut self,
        func: &mut Function,
        scalar_phi_results: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        let values: Vec<_> = func.dfg.value_ids().collect();
        for value in values {
            let Some(mut leaf_phis) = scalar_phi_results[value].take() else {
                continue;
            };
            self.simplify_scalar_leaf_phis(func, &mut leaf_phis, scalar_phi_results);
            scalar_phi_results[value] = Some(leaf_phis);
        }
    }

    fn simplify_scalar_leaf_phis(
        &mut self,
        func: &mut Function,
        leaf_phis: &mut LeafValues,
        scalar_phi_results: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    ) {
        let mut worklist: Vec<_> = leaf_phis.iter().copied().collect();
        let mut queued = FxHashSet::default();
        while let Some(leaf_phi) = worklist.pop() {
            let Some(phi_inst) = func.dfg.value_inst(leaf_phi) else {
                continue;
            };
            if !func.layout.is_inst_inserted(phi_inst) {
                continue;
            }
            let Some(replacement) = trivial_phi_replacement(func, phi_inst) else {
                continue;
            };
            let phi_users: Vec<_> = func
                .dfg
                .users(leaf_phi)
                .copied()
                .filter(|user| func.layout.is_inst_inserted(*user) && func.dfg.is_phi(*user))
                .collect();
            func.dfg.change_to_alias(leaf_phi, replacement);
            for current in leaf_phis.iter_mut() {
                if *current == leaf_phi {
                    *current = replacement;
                }
            }
            replace_scalar_phi_value(scalar_phi_results, leaf_phi, replacement);
            InstInserter::at_location(CursorLocation::At(phi_inst)).remove_inst(func);
            for user in phi_users {
                let Some(user_value) = func.dfg.inst_result(user) else {
                    continue;
                };
                if queued.insert(user_value) {
                    worklist.push(user_value);
                }
            }
            self.changed = true;
        }
    }

    fn cleanup_scalarized_artifacts(
        &mut self,
        func: &mut Function,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        promoted_by_root: &FxHashMap<ValueId, PromotableRoot>,
    ) -> bool {
        let mut changed = false;
        loop {
            func.rebuild_users();
            let removed_mloads = self.cleanup_dead_aggregate_mloads_with_current_users(func);
            let removed_promoted_paths = self.cleanup_dead_promoted_paths_with_current_users(
                func,
                projection_of,
                promoted_by_root,
            );
            let removed_pure = self.dead_pure_cleanup.run_with_current_users(func);
            if !removed_mloads && !removed_promoted_paths && !removed_pure {
                return changed;
            }
            changed = true;
        }
    }

    fn cleanup_dead_aggregate_mloads_with_current_users(&self, func: &mut Function) -> bool {
        let mut changed = false;
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                let Some((result, load_ty)) =
                    downcast::<&data::Mload>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|mload| {
                            func.dfg
                                .inst_result(inst)
                                .map(|result| (result, *mload.ty()))
                        })
                        .or_else(|| {
                            downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                                .and_then(|_| {
                                    func.dfg
                                        .inst_result(inst)
                                        .map(|result| (result, func.dfg.value_ty(result)))
                                })
                        })
                else {
                    continue;
                };
                if !shape::is_supported_scalar_shape_ty(func.ctx(), load_ty) {
                    continue;
                }
                if func
                    .dfg
                    .users(result)
                    .copied()
                    .any(|user| func.layout.is_inst_inserted(user))
                {
                    continue;
                }

                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                changed = true;
            }
        }
        changed
    }

    fn cleanup_dead_promoted_paths_with_current_users(
        &self,
        func: &mut Function,
        projection_of: &SecondaryMap<ValueId, Option<Projection>>,
        promoted_by_root: &FxHashMap<ValueId, PromotableRoot>,
    ) -> bool {
        if promoted_by_root.is_empty() {
            return false;
        }
        let mut candidate_insts = FxHashSet::default();
        let mut candidate_results = FxHashMap::default();

        for value in func.dfg.value_ids() {
            let Some(projection) = projection_of[value] else {
                continue;
            };
            if !promoted_by_root.contains_key(&projection.root_value) {
                continue;
            }
            let Some(inst) = func.dfg.value_inst(value) else {
                continue;
            };
            if !func.layout.is_inst_inserted(inst) || !is_promoted_path_inst(func, inst) {
                continue;
            }

            candidate_insts.insert(inst);
            candidate_results.insert(value, inst);
        }

        if candidate_insts.is_empty() {
            return false;
        }

        let mut live = FxHashSet::default();
        let mut worklist = Vec::new();
        for (&value, &inst) in &candidate_results {
            if func
                .dfg
                .users(value)
                .copied()
                .any(|user| func.layout.is_inst_inserted(user) && !candidate_insts.contains(&user))
                && live.insert(inst)
            {
                worklist.push(inst);
            }
        }

        while let Some(inst) = worklist.pop() {
            func.dfg.inst(inst).for_each_value(&mut |value| {
                let Some(&def_inst) = candidate_results.get(&value) else {
                    return;
                };
                if live.insert(def_inst) {
                    worklist.push(def_inst);
                }
            });
        }

        let dead_insts: Vec<_> = candidate_insts
            .iter()
            .copied()
            .filter(|inst| !live.contains(inst))
            .collect();
        if dead_insts.is_empty() {
            return false;
        }

        for inst in &dead_insts {
            if let Some(result) = func.dfg.inst_result(*inst) {
                let undef = func.dfg.make_undef_value(func.dfg.value_ty(result));
                func.dfg.change_to_alias(result, undef);
            }
        }
        func.rebuild_users();

        for block in func.layout.iter_block().collect::<Vec<_>>() {
            for inst in func.layout.iter_inst(block).collect::<Vec<_>>() {
                if dead_insts.contains(&inst) {
                    InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                }
            }
        }

        true
    }

    fn aggregate_shape(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        ty: Type,
    ) -> Option<shape::AggregateShape> {
        self.layout_cache.shape(module, ty)
    }

    fn aggregate_single_runtime_word_leaf(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        ty: Type,
    ) -> Option<shape::AggregateLeaf> {
        self.layout_cache.single_runtime_word_leaf(module, ty)
    }

    fn compatible_aggregate_bitcast_runtime_leaves(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        from_ty: Type,
        to_ty: Type,
    ) -> Option<(shape::RuntimeLeaves, shape::RuntimeLeaves)> {
        self.layout_cache
            .compatible_bitcast_runtime_leaves(module, from_ty, to_ty)
    }

    fn projection_view_leaf_tys(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        ty: Type,
    ) -> Option<SmallVec<[Type; 4]>> {
        if shape::is_supported_scalar_shape_ty(module, ty) {
            return Some(
                self.aggregate_shape(module, ty)?
                    .leaves
                    .into_iter()
                    .map(|leaf| leaf.ty)
                    .collect(),
            );
        }
        Some(smallvec![ty])
    }

    fn projection_slice_can_view_as(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        slice: shape::AggregateSlice,
        view_ty: Type,
    ) -> bool {
        let Some(from_leaf_tys) = self.projection_view_leaf_tys(module, slice.ty) else {
            return false;
        };
        let Some(to_leaf_tys) = self.projection_view_leaf_tys(module, view_ty) else {
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
                    && self
                        .compatible_aggregate_bitcast_runtime_leaves(module, slice.ty, view_ty)
                        .is_some())
    }

    fn aggregate_bitcast_is_scalarizable(
        &mut self,
        module: &sonatina_ir::module::ModuleCtx,
        from_ty: Type,
        to_ty: Type,
    ) -> bool {
        if shape::runtime_size_bytes(module, from_ty) != shape::runtime_size_bytes(module, to_ty) {
            return false;
        }
        let from_is_agg = shape::is_supported_scalar_shape_ty(module, from_ty);
        let to_is_agg = shape::is_supported_scalar_shape_ty(module, to_ty);
        if from_is_agg && to_is_agg {
            return self
                .compatible_aggregate_bitcast_runtime_leaves(module, from_ty, to_ty)
                .is_some();
        }
        if to_is_agg {
            return self
                .aggregate_single_runtime_word_leaf(module, to_ty)
                .is_some();
        }
        if from_is_agg {
            return self
                .aggregate_single_runtime_word_leaf(module, from_ty)
                .is_some();
        }
        false
    }

    fn scalarized_leaves_of_value(
        &mut self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        value: ValueId,
        ty: Type,
        scalarized_agg: &SecondaryMap<ValueId, Option<LeafValues>>,
    ) -> Option<LeafValues> {
        if !shape::is_supported_scalar_shape_ty(module, ty) {
            return (func.dfg.value_ty(value) == ty).then(|| smallvec![value]);
        }

        if is_explicit_undef(func, value) {
            let agg_shape = self.aggregate_shape(module, ty)?;
            let mut leaves = LeafValues::new();
            for leaf in agg_shape.leaves {
                leaves.push(func.dfg.make_undef_value(leaf.ty));
            }
            return Some(leaves);
        }

        scalarized_agg[value].clone()
    }

    fn insert_live_in_leaf_load(
        &self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        promoted: &PromotableRoot,
        leaf_idx: usize,
    ) -> ValueId {
        let leaf = &promoted.shape.leaves[leaf_idx];
        let before = first_non_phi_inst(func, promoted.seed_block);
        let loc = before
            .and_then(|inst| func.layout.prev_inst_of(inst))
            .map_or(
                CursorLocation::BlockTop(promoted.seed_block),
                CursorLocation::At,
            );
        let mut cursor = InstInserter::at_location(loc);
        let mut object = promoted.root_value;
        let mut current_ty = promoted.shape.root_ty;

        for &idx in leaf.path.as_slice() {
            let idx_value = func.dfg.make_imm_value(i64::from(idx));
            let next_ty = shape::aggregate_slice_for_index(module, current_ty, idx)
                .map(|slice| slice.ty)
                .unwrap_or_else(|| panic!("missing aggregate slice for promoted live-in leaf"));
            let result_ty = func
                .ctx()
                .with_ty_store_mut(|store| store.make_obj_ref(next_ty));
            let proj = cursor.insert_inst_data(
                func,
                data::ObjProj::new_unchecked(func.inst_set(), smallvec![object, idx_value]),
            );
            let result = cursor.make_result(func, proj, result_ty);
            cursor.attach_result(func, proj, result);
            cursor.set_location(CursorLocation::At(proj));
            object = result;
            current_ty = next_ty;
        }

        let load =
            cursor.insert_inst_data(func, data::ObjLoad::new_unchecked(func.inst_set(), object));
        let result = cursor.make_result(func, load, leaf.ty);
        cursor.attach_result(func, load, result);
        result
    }

    fn write_back_promoted_arg_roots(
        &self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        promoted_by_root: &FxHashMap<ValueId, PromotableRoot>,
        modified_leaves: &FxHashMap<ValueId, FxHashSet<usize>>,
        ssa: &mut SsaBuilder,
    ) {
        let mut roots: Vec<_> = promoted_by_root
            .values()
            .filter(|promoted| {
                promoted.root_kind.is_arg_like()
                    && modified_leaves
                        .get(&promoted.root_value)
                        .is_some_and(|leaves| !leaves.is_empty())
            })
            .cloned()
            .collect();
        if roots.is_empty() {
            return;
        }
        roots.sort_by_key(|promoted| promoted.root_value);

        for block in func.layout.iter_block().collect::<Vec<_>>() {
            let Some(ret_inst) = func.layout.last_inst_of(block) else {
                continue;
            };
            if downcast::<&control_flow::Return>(func.inst_set(), func.dfg.inst(ret_inst)).is_none()
            {
                continue;
            }

            for promoted in &roots {
                let Some(leaves) = modified_leaves.get(&promoted.root_value) else {
                    continue;
                };
                let mut leaf_indices: Vec<_> = leaves.iter().copied().collect();
                leaf_indices.sort_unstable();
                for leaf_idx in leaf_indices {
                    let value = ssa.use_var(func, promoted.leaf_vars[leaf_idx], block);
                    let loc = func
                        .layout
                        .prev_inst_of(ret_inst)
                        .map_or(CursorLocation::BlockTop(block), CursorLocation::At);
                    self.insert_leaf_write_back(func, module, promoted, leaf_idx, value, loc);
                }
            }
        }
    }

    fn insert_leaf_write_back(
        &self,
        func: &mut Function,
        module: &sonatina_ir::module::ModuleCtx,
        promoted: &PromotableRoot,
        leaf_idx: usize,
        value: ValueId,
        loc: CursorLocation,
    ) {
        let leaf = &promoted.shape.leaves[leaf_idx];
        let mut cursor = InstInserter::at_location(loc);
        let mut object = promoted.root_value;
        let mut current_ty = promoted.shape.root_ty;

        for &idx in leaf.path.as_slice() {
            let idx_value = func.dfg.make_imm_value(i64::from(idx));
            let next_ty = shape::aggregate_slice_for_index(module, current_ty, idx)
                .map(|slice| slice.ty)
                .unwrap_or_else(|| panic!("missing aggregate slice for promoted write-back leaf"));
            let result_ty = func
                .ctx()
                .with_ty_store_mut(|store| store.make_obj_ref(next_ty));
            let proj = cursor.insert_inst_data(
                func,
                data::ObjProj::new_unchecked(func.inst_set(), smallvec![object, idx_value]),
            );
            let result = cursor.make_result(func, proj, result_ty);
            cursor.attach_result(func, proj, result);
            cursor.set_location(CursorLocation::At(proj));
            object = result;
            current_ty = next_ty;
        }

        let store = cursor.insert_inst_data(
            func,
            data::ObjStore::new_unchecked(func.inst_set(), object, value),
        );
        cursor.set_location(CursorLocation::At(store));
    }
}

impl RootKind {
    fn inst(self) -> Option<InstId> {
        match self {
            Self::Alloca { inst } | Self::ObjAlloc { inst } => Some(inst),
            Self::Arg { .. } | Self::SyntheticOutArg { .. } => None,
        }
    }

    fn default_init(self) -> RootInit {
        match self {
            Self::Alloca { .. } | Self::ObjAlloc { .. } | Self::SyntheticOutArg { .. } => {
                RootInit::UndefFresh
            }
            Self::Arg { .. } => RootInit::LoadLiveIn,
        }
    }

    fn is_arg_like(self) -> bool {
        matches!(self, Self::Arg { .. } | Self::SyntheticOutArg { .. })
    }
}

impl PromotableRoot {
    fn root_inst(&self) -> Option<InstId> {
        self.root_kind.inst()
    }
}

fn objref_element_ty(ctx: &sonatina_ir::module::ModuleCtx, ty: Type) -> Option<Type> {
    let sonatina_ir::types::CompoundType::ObjRef(elem) = ty.resolve_compound(ctx)? else {
        return None;
    };
    Some(elem)
}

fn record_modified_leaves(
    modified_leaves: &mut FxHashMap<ValueId, FxHashSet<usize>>,
    root_value: ValueId,
    leaf_range: std::ops::Range<usize>,
) {
    modified_leaves
        .entry(root_value)
        .or_default()
        .extend(leaf_range);
}

fn shape_contains_enum(shape: &shape::AggregateShape) -> bool {
    shape.leaves.iter().any(|leaf| leaf.ty.is_enum_tag())
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

fn eq_before_inst(func: &mut Function, inst: InstId, lhs: ValueId, rhs: ValueId) -> ValueId {
    let loc = func.layout.prev_inst_of(inst).map_or(
        CursorLocation::BlockTop(func.layout.inst_block(inst)),
        CursorLocation::At,
    );
    let mut cursor = InstInserter::at_location(loc);
    let eq_inst = cursor.insert_inst_data(func, cmp::Eq::new_unchecked(func.inst_set(), lhs, rhs));
    let eq_value = func.dfg.make_value(Value::Inst {
        inst: eq_inst,
        result_idx: 0,
        ty: Type::I1,
    });
    cursor.attach_result(func, eq_inst, eq_value);
    eq_value
}

fn is_explicit_undef(func: &Function, value: ValueId) -> bool {
    matches!(func.dfg.value(value), Value::Undef { .. })
}

fn trivial_phi_replacement(func: &mut Function, phi_inst: InstId) -> Option<ValueId> {
    let phi_value = func.dfg.inst_result(phi_inst)?;
    let ty = func.dfg.value_ty(phi_value);
    let phi = func.dfg.cast_phi(phi_inst)?;

    let replacement = match phi.args().first() {
        None => func.dfg.make_undef_value(ty),
        Some(&(first, _)) if phi.args().iter().all(|(value, _)| *value == first) => {
            if first == phi_value {
                func.dfg.make_undef_value(ty)
            } else {
                first
            }
        }
        Some(_) => {
            let mut non_self = None;
            for &(value, _) in phi.args() {
                if value == phi_value {
                    continue;
                }

                match non_self {
                    Some(existing) if existing != value => return None,
                    Some(_) => {}
                    None => non_self = Some(value),
                }
            }

            non_self.unwrap_or_else(|| func.dfg.make_undef_value(ty))
        }
    };

    Some(replacement)
}

fn replace_scalar_phi_value(
    scalar_phi_results: &mut SecondaryMap<ValueId, Option<LeafValues>>,
    from: ValueId,
    to: ValueId,
) {
    for value in scalar_phi_results.keys() {
        let Some(leaf_phis) = scalar_phi_results[value].as_mut() else {
            continue;
        };
        for leaf_phi in leaf_phis {
            if *leaf_phi == from {
                *leaf_phi = to;
            }
        }
    }
}

fn is_dead_inst_tree(
    func: &Function,
    inst: InstId,
    memo: &mut FxHashMap<InstId, bool>,
    visiting: &mut FxHashSet<InstId>,
) -> bool {
    if let Some(&cached) = memo.get(&inst) {
        return cached;
    }
    if !visiting.insert(inst)
        || func.dfg.side_effect(inst).has_effect()
        || func.dfg.is_terminator(inst)
    {
        memo.insert(inst, false);
        return false;
    }

    let dead = func.dfg.inst_result(inst).is_some_and(|result| {
        func.dfg
            .users(result)
            .copied()
            .filter(|user| func.layout.is_inst_inserted(*user))
            .all(|user| is_dead_inst_tree(func, user, memo, visiting))
    });
    visiting.remove(&inst);
    memo.insert(inst, dead);
    dead
}

fn first_non_phi_inst(func: &Function, block: BlockId) -> Option<InstId> {
    func.layout
        .iter_inst(block)
        .find(|inst| !func.dfg.is_phi(*inst))
}

fn is_promoted_path_inst(func: &Function, inst: InstId) -> bool {
    let inst_data = func.dfg.inst(inst);
    downcast::<&data::Alloca>(func.inst_set(), inst_data).is_some()
        || downcast::<&data::Gep>(func.inst_set(), inst_data).is_some()
        || downcast::<&data::ObjAlloc>(func.inst_set(), inst_data).is_some()
        || downcast::<&data::ObjProj>(func.inst_set(), inst_data).is_some()
        || downcast::<&data::ObjIndex>(func.inst_set(), inst_data).is_some()
        || downcast::<&data::EnumProj>(func.inst_set(), inst_data).is_some()
        || downcast::<&cast::Bitcast>(func.inst_set(), inst_data).is_some()
        || downcast::<&control_flow::Phi>(func.inst_set(), inst_data).is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{InstDowncast, Module, inst::cast, ir_writer::FuncWriter, module::FuncRef};
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

    fn run_scalarize_with_local_args(module: &Module, func_ref: FuncRef) {
        let local_object_args = crate::optim::aggregate::collect_local_object_arg_info(module);
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run_for_func(func_ref, func, &local_object_args);
        });
    }

    fn assert_no_promoted_aggregate_artifacts(
        func: &Function,
        ctx: &sonatina_ir::module::ModuleCtx,
    ) {
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                assert!(
                    downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                    "promoted alloca should be removed"
                );
                assert!(
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                    "promoted object root should be removed"
                );
                assert!(
                    downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                    "promoted object projection should be removed"
                );
                assert!(
                    downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                    "promoted object index should be removed"
                );
                if let Some(mload) =
                    <&data::Mload as InstDowncast>::downcast(func.inst_set(), func.dfg.inst(inst))
                {
                    assert!(
                        !shape::is_supported_scalar_shape_ty(ctx, *mload.ty()),
                        "aggregate mload should be gone after scalarization"
                    );
                }
                if let Some(_obj_load) =
                    <&data::ObjLoad as InstDowncast>::downcast(func.inst_set(), func.dfg.inst(inst))
                    && let Some(result) = func.dfg.inst_result(inst)
                {
                    assert!(
                        !shape::is_supported_scalar_shape_ty(ctx, func.dfg.value_ty(result)),
                        "aggregate obj.load should be gone after scalarization"
                    );
                }
                if let Some(mstore) =
                    <&data::Mstore as InstDowncast>::downcast(func.inst_set(), func.dfg.inst(inst))
                {
                    assert!(
                        !shape::is_supported_scalar_shape_ty(ctx, *mstore.ty()),
                        "aggregate mstore should be gone after scalarization"
                    );
                }
                if let Some(obj_store) = <&data::ObjStore as InstDowncast>::downcast(
                    func.inst_set(),
                    func.dfg.inst(inst),
                ) {
                    assert!(
                        !shape::is_supported_scalar_shape_ty(
                            ctx,
                            func.dfg.value_ty(*obj_store.value())
                        ),
                        "aggregate obj.store should be gone after scalarization"
                    );
                }
            }
        }
    }

    #[test]
    fn scalarize_does_not_leave_removed_leaf_phi_uses() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i1, v1.i1, v2.i256) -> i256 {
    block0:
        v3.*@slice = alloca @slice;
        br v0 block1 block2;

    block1:
        v4.@slice = insert_value undef.@slice 0.i8 v2;
        v5.@slice = insert_value v4 1.i8 11.i256;
        jump block3;

    block2:
        v6.@slice = insert_value undef.@slice 0.i8 v2;
        v7.@slice = insert_value v6 1.i8 22.i256;
        jump block3;

    block3:
        v8.@slice = phi (v5 block1) (v7 block2);
        mstore v3 v8 @slice;
        br v1 block4 block5;

    block4:
        v9.@slice = insert_value undef.@slice 0.i8 99.i256;
        v10.@slice = insert_value v9 1.i8 33.i256;
        mstore v3 v10 @slice;
        jump block5;

    block5:
        v11.@slice = mload v3 @slice;
        v12.i256 = extract_value v11 0.i8;
        return v12;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    func.dfg.inst(inst).for_each_value(&mut |value| {
                        if let Some(def_inst) = func.dfg.value_inst(value) {
                            assert!(
                                func.layout.is_inst_inserted(def_inst),
                                "inst {} uses value v{} from removed inst {}",
                                inst.as_u32(),
                                value.as_u32(),
                                def_inst.as_u32()
                            );
                        }
                    });
                }
            }
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    #[should_panic(
        expected = "AggregateScalarize requires CfgCleanup to remove unreachable blocks first"
    )]
    fn scalarize_requires_cfg_cleanup_for_unreachable_blocks() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f() -> i256 {
    block0:
        v0.*@slice = alloca @slice;
        return 0.i256;

    block1:
        v1.@slice = mload v0 @slice;
        v2.i256 = extract_value v1 0.i8;
        return v2;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });
    }

    #[test]
    fn scalarize_cleans_up_dead_promoted_pointer_trees() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f() -> i256 {
    block0:
        v0.*@slice = alloca @slice;
        v1.*i256 = gep v0 0.i8 0.i8;
        v2.*i256 = bitcast v1 *i256;
        return 0.i256;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    assert!(
                        downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                        "dead promoted alloca should be removed"
                    );
                    assert!(
                        downcast::<&data::Gep>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                        "dead promoted gep should be removed"
                    );
                    assert!(
                        downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)).is_none(),
                        "dead promoted bitcast should be removed"
                    );
                }
            }
        });
    }

    #[test]
    fn scalarize_promotes_non_entry_alloca() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i1, v1.i256, v2.i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        v3.*@slice = alloca @slice;
        v4.*i256 = gep v3 0.i8 0.i8;
        v5.*i256 = gep v3 0.i8 1.i8;
        mstore v4 v1 i256;
        mstore v5 v2 i256;
        v6.i256 = mload v4 i256;
        v7.i256 = mload v5 i256;
        v8.i256 = add v6 v7;
        return v8;

    block2:
        return 0.i256;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_promotes_obj_alloc_root() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        v2.objref<@slice> = obj.alloc @slice;
        v3.@slice = insert_value undef.@slice 0.i8 v0;
        v4.@slice = insert_value v3 1.i8 v1;
        obj.store v2 v4;
        v5.@slice = obj.load v2;
        v6.i256 = extract_value v5 1.i8;
        return v6;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_promotes_local_object_arg_with_live_in_loads() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.objref<@one>) -> i256 {
    block0:
        v1.@one = obj.load v0;
        v2.i256 = extract_value v1 0.i8;
        return v2;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        run_scalarize_with_local_args(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("extract_value"),
                "local object arg aggregate extract should be scalarized:\n{dumped}"
            );
            assert!(
                dumped.contains("obj.load"),
                "live-in local object arg should seed scalar state with entry loads:\n{dumped}"
            );
        });
    }

    #[test]
    fn scalarize_skips_mutated_local_object_arg_to_avoid_unprofitable_writeback() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.objref<@one>, v1.i256) -> i256 {
    block0:
        v2.objref<i256> = obj.proj v0 0.i8;
        obj.store v2 v1;
        v3.i256 = obj.load v2;
        return v3;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        run_scalarize_with_local_args(&module, func_ref);

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("obj.load v2"),
                "mutated local object arg should stay in object form until writeback is profitability-aware:\n{dumped}"
            );
            assert!(
                dumped.contains("obj.store v2 v1;"),
                "mutated local object arg store should remain explicit:\n{dumped}"
            );
            assert!(
                dumped.contains("return v3;"),
                "without scalarization the explicit object load should remain the returned value:\n{dumped}"
            );
        });
    }

    #[test]
    fn scalarize_promotes_synthetic_out_arg_with_undef_init() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %make(v0.i256) -> objref<@one> {
    block0:
        v1.objref<@one> = obj.alloc @one;
        v2.objref<i256> = obj.proj v1 0.i8;
        obj.store v2 v0;
        return v1;
}
"#,
        );
        let func_ref = lookup_func(&module, "make");
        let mut local_object_args = crate::optim::aggregate::collect_local_object_arg_info(&module);
        let synthetic_out_args =
            crate::optim::aggregate::ObjectReturnOutParam.run_with_synthetic_out_args(&module);
        crate::optim::aggregate::merge_local_object_arg_info(
            &mut local_object_args,
            &synthetic_out_args,
        );
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run_for_func(func_ref, func, &local_object_args);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.alloc"),
                "synthetic out-arg scalarization should remove the original alloc:\n{dumped}"
            );
            assert!(
                dumped.contains("obj.store"),
                "synthetic out-arg leaves must be written back before return:\n{dumped}"
            );
            assert!(
                !dumped.contains("obj.load"),
                "fresh synthetic out-arg should not seed from entry loads:\n{dumped}"
            );
        });
    }

    #[test]
    fn scalarize_promotes_fresh_equivalent_synthetic_out_arg() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %choose_pair(v0.i1, v1.i256, v2.i256) -> objref<@pair> {
    block0:
        br v0 block1 block2;

    block1:
        v3.objref<@pair> = obj.alloc @pair;
        v4.objref<i256> = obj.proj v3 0.i8;
        obj.store v4 v1;
        jump block3;

    block2:
        v5.objref<@pair> = obj.alloc @pair;
        v6.objref<i256> = obj.proj v5 0.i8;
        obj.store v6 v2;
        jump block3;

    block3:
        v7.objref<@pair> = phi (v3 block1) (v5 block2);
        return v7;
}
"#,
        );
        let func_ref = lookup_func(&module, "choose_pair");
        let mut local_object_args = crate::optim::aggregate::collect_local_object_arg_info(&module);
        let synthetic_out_args =
            crate::optim::aggregate::ObjectReturnOutParam.run_with_synthetic_out_args(&module);
        crate::optim::aggregate::merge_local_object_arg_info(
            &mut local_object_args,
            &synthetic_out_args,
        );
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run_for_func(func_ref, func, &local_object_args);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.alloc"),
                "fresh-equivalent synthetic out-arg scalarization should remove both branch allocs:\n{dumped}"
            );
            assert!(
                dumped.contains("obj.store"),
                "fresh-equivalent synthetic out-arg should still write back leaves:\n{dumped}"
            );
            assert!(
                !dumped.contains("obj.load"),
                "fresh-equivalent synthetic out-arg should not seed from entry loads:\n{dumped}"
            );
        });
    }

    #[test]
    fn aggregate_object_passes_use_precomputed_local_args_inside_modify() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.objref<@one>, v1.i256) -> i256 {
    block0:
        v2.objref<i256> = obj.proj v0 0.i8;
        obj.store v2 v1;
        v3.i256 = obj.load v2;
        return v3;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        let object_effects = crate::optim::aggregate::compute_object_effect_summaries(&module);
        let local_object_args = crate::optim::aggregate::collect_local_object_arg_info(&module);

        module.func_store.modify(func_ref, |func| {
            crate::optim::aggregate::ObjectLoadStore::default().run_for_func(
                func_ref,
                func,
                &local_object_args,
                &object_effects,
            );
            AggregateScalarize::default().run_for_func(func_ref, func, &local_object_args);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.load"),
                "precomputed local-arg analysis should let aggregate passes run under modify without reloading from the store:\n{dumped}"
            );
            assert!(
                dumped.contains("obj.store v2 v1;"),
                "caller-visible local object arg mutation must stay explicit:\n{dumped}"
            );
            assert!(
                dumped.contains("return v1;"),
                "combined aggregate passes should preserve the forwarded scalar result:\n{dumped}"
            );
        });
    }

    #[test]
    fn scalarize_promotes_obj_proj_and_index_paths() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, [i256; 2] };

func private %f(v0.i256, v1.i256, v2.i256) -> i256 {
    block0:
        v3.objref<@pair> = obj.alloc @pair;
        v4.objref<i256> = obj.proj v3 0.i8;
        v5.objref<[i256; 2]> = obj.proj v3 1.i8;
        v6.objref<i256> = obj.index v5 0.i8;
        v7.objref<i256> = obj.index v5 1.i8;
        obj.store v4 v0;
        obj.store v6 v1;
        obj.store v7 v2;
        v8.i256 = obj.load v4;
        v9.i256 = obj.load v6;
        v10.i256 = obj.load v7;
        v11.i256 = add v8 v9;
        v12.i256 = add v11 v10;
        return v12;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_promotes_same_root_whole_object_phi_web() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.i1) -> i256 {
    block0:
        v1.objref<@pair> = obj.alloc @pair;
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v2.objref<@pair> = phi (v1 block1) (v1 block2);
        v3.objref<i256> = obj.proj v2 0.i8;
        obj.store v3 7.i256;
        v4.i256 = obj.load v3;
        return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.alloc")
                    && !dumped.contains("obj.proj")
                    && !dumped.contains("obj.load")
                    && !dumped.contains("obj.store"),
                "same-root whole-object phi web should scalarize through the phi:\n{dumped}"
            );
            assert!(
                dumped.contains("return 7.i256;"),
                "scalarized whole-object phi should fold to the stored scalar:\n{dumped}"
            );
        });
    }

    #[test]
    fn scalarize_promotes_same_root_projected_field_phi_web() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %f(v0.i1) -> i256 {
    block0:
        v1.objref<@pair> = obj.alloc @pair;
        v2.objref<i256> = obj.proj v1 1.i8;
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v3.objref<i256> = phi (v2 block1) (v2 block2);
        obj.store v3 9.i256;
        v4.i256 = obj.load v3;
        return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.alloc")
                    && !dumped.contains("obj.proj")
                    && !dumped.contains("obj.load")
                    && !dumped.contains("obj.store"),
                "same-root projected-field phi web should scalarize through the phi:\n{dumped}"
            );
            assert!(
                dumped.contains("return 9.i256;"),
                "scalarized projected-field phi should fold to the stored scalar:\n{dumped}"
            );
        });
    }

    #[test]
    fn scalarize_promotes_loop_carried_object_phi_web() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i1, v1.i256) -> i256 {
    block0:
        v2.objref<@one> = obj.alloc @one;
        jump block1;

    block1:
        v3.objref<@one> = phi (v2 block0) (v5 block2);
        v4.objref<i256> = obj.proj v3 0.i8;
        obj.store v4 v1;
        br v0 block3 block2;

    block2:
        v5.objref<@one> = bitcast v3 objref<@one>;
        jump block1;

    block3:
        v6.i256 = obj.load v4;
        return v6;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("obj.alloc")
                    && !dumped.contains("obj.proj")
                    && !dumped.contains("obj.load")
                    && !dumped.contains("obj.store"),
                "loop-carried same-root object phi should scalarize through the backedge:\n{dumped}"
            );
            assert!(
                dumped.contains("return v1;"),
                "loop-carried same-root object phi should forward the stored scalar:\n{dumped}"
            );
        });
    }

    #[test]
    fn scalarize_rejects_multi_root_object_phi_web() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i1) -> i256 {
    block0:
        v1.objref<@one> = obj.alloc @one;
        v2.objref<@one> = obj.alloc @one;
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v3.objref<@one> = phi (v1 block1) (v2 block2);
        v4.objref<i256> = obj.proj v3 0.i8;
        obj.store v4 5.i256;
        v5.i256 = obj.load v4;
        return v5;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("obj.alloc")
                    && dumped.contains("obj.proj")
                    && dumped.contains("obj.load")
                    && dumped.contains("obj.store"),
                "multi-root phi should stay in object form:\n{dumped}"
            );
        });
    }

    #[test]
    fn scalarize_splits_block_to_seed_non_entry_alloca_at_its_location() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i1, v1.i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        v2.i256 = add v1 1.i256;
        v3.*@one = alloca @one;
        mstore v3 v2 i256;
        v4.i256 = mload v3 i256;
        return v4;

    block2:
        return 0.i256;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_eq!(
                func.layout.iter_block().count(),
                4,
                "non-entry alloca with leading instructions should split its block"
            );
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_splits_each_promoted_alloca_to_its_own_seed_point() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = add v0 1.i256;
        v3.*@one = alloca @one;
        mstore v3 v2 i256;
        v4.i256 = mload v3 i256;
        v5.*@one = alloca @one;
        mstore v5 v1 i256;
        v6.i256 = mload v5 i256;
        v7.i256 = add v4 v6;
        return v7;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_eq!(
                func.layout.iter_block().count(),
                3,
                "each promoted alloca in the original block should get its own seed point"
            );
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_non_entry_alloca_merges_store_and_undef_paths() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f(v0.i1) -> i256 {
    block0:
        jump block1;

    block1:
        v1.*@one = alloca @one;
        v2.*i256 = gep v1 0.i8 0.i8;
        br v0 block2 block3;

    block2:
        mstore v2 7.i256 i256;
        jump block4;

    block3:
        jump block4;

    block4:
        v3.i256 = mload v2 i256;
        return v3;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);

            let mut found = false;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    let Some(phi) = <&control_flow::Phi as InstDowncast>::downcast(
                        func.inst_set(),
                        func.dfg.inst(inst),
                    ) else {
                        continue;
                    };
                    if func
                        .dfg
                        .inst_result(inst)
                        .is_none_or(|result| func.dfg.value_ty(result) != Type::I256)
                    {
                        continue;
                    }

                    let has_undef = phi
                        .args()
                        .iter()
                        .any(|(value, _)| matches!(func.dfg.value(*value), Value::Undef { .. }));
                    let has_non_undef = phi
                        .args()
                        .iter()
                        .any(|(value, _)| !matches!(func.dfg.value(*value), Value::Undef { .. }));
                    if has_undef && has_non_undef {
                        found = true;
                    }
                }
            }

            assert!(found, "expected scalar phi merging stored and undef paths");
        });
    }

    #[test]
    fn scalarize_loop_local_alloca_reseeds_at_its_location() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @one = { i256 };

func private %f() -> i256 {
    block0:
        jump block1;

    block1:
        v0.i1 = phi (1.i1 block0) (0.i1 block4);
        v1.i256 = add 5.i256 6.i256;
        v2.*@one = alloca @one;
        v3.*i256 = gep v2 0.i8 0.i8;
        br v0 block2 block3;

    block2:
        mstore v3 9.i256 i256;
        jump block3;

    block3:
        v4.i256 = mload v3 i256;
        br v0 block4 block5;

    block4:
        jump block1;

    block5:
        return v4;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_eq!(
                func.layout.iter_block().count(),
                7,
                "loop-local alloca with leading instructions should split its seed point"
            );
            assert_no_promoted_aggregate_artifacts(func, &ctx);

            let mut found = false;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    let Some(phi) = <&control_flow::Phi as InstDowncast>::downcast(
                        func.inst_set(),
                        func.dfg.inst(inst),
                    ) else {
                        continue;
                    };
                    if func
                        .dfg
                        .inst_result(inst)
                        .is_none_or(|result| func.dfg.value_ty(result) != Type::I256)
                    {
                        continue;
                    }

                    let has_undef = phi
                        .args()
                        .iter()
                        .any(|(value, _)| matches!(func.dfg.value(*value), Value::Undef { .. }));
                    let has_non_undef = phi
                        .args()
                        .iter()
                        .any(|(value, _)| !matches!(func.dfg.value(*value), Value::Undef { .. }));
                    if has_undef && has_non_undef {
                        found = true;
                    }
                }
            }

            assert!(
                found,
                "loop-local promoted alloca should re-seed to undef at its alloca point"
            );
        });
    }

    #[test]
    fn scalarize_simplifies_transitive_scalar_phi_users_without_stale_entries() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i1, v1.i1, v2.i256, v3.i256) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        jump block3;

    block2:
        jump block3;

    block3:
        v4.@slice = insert_value undef.@slice 0.i8 v2;
        v5.@slice = insert_value v4 1.i8 v3;
        v6.@slice = phi (v5 block1) (v5 block2);
        br v1 block4 block5;

    block4:
        jump block6;

    block5:
        jump block6;

    block6:
        v7.@slice = phi (v6 block4) (v6 block5);
        v8.i256 = extract_value v7 0.i8;
        return v8;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    func.dfg.inst(inst).for_each_value(&mut |value| {
                        if let Some(def_inst) = func.dfg.value_inst(value) {
                            assert!(
                                func.layout.is_inst_inserted(def_inst),
                                "inst {} uses value v{} from removed inst {}",
                                inst.as_u32(),
                                value.as_u32(),
                                def_inst.as_u32()
                            );
                        }
                    });
                }
            }
            assert_no_promoted_aggregate_artifacts(func, &ctx);
        });
    }

    #[test]
    fn scalarize_deduplicates_duplicate_successor_edges() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @slice = { i256, i256 };

func private %f(v0.i1) -> i256 {
    block0:
        v1.*@slice = alloca @slice;
        br v0 block1 block1;

    block1:
        v2.@slice = mload v1 @slice;
        v3.i256 = extract_value v2 0.i8;
        return v3;
}
"#,
        );
        let ctx = module.ctx.clone();
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateScalarize::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            assert_no_promoted_aggregate_artifacts(func, &ctx);
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(phi) = <&control_flow::Phi as InstDowncast>::downcast(
                        func.inst_set(),
                        func.dfg.inst(inst),
                    ) {
                        let mut preds = FxHashSet::default();
                        for &(_, pred) in phi.args() {
                            assert!(preds.insert(pred), "phi should not retain duplicate preds");
                        }
                    }
                }
            }
        });
    }
}
