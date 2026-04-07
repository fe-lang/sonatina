use std::cmp::Reverse;

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, Module, Type, Value, ValueId,
    cfg::ControlFlowGraph,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{control_flow, data, downcast},
    module::{FuncRef, ModuleCtx},
    types::CompoundType,
};

use crate::liveness::{InstLiveness, Liveness};

use super::{
    LocalObjectArgInfo, ObjectEffectSummaryMap, ObjectMemoryAnalysis, RootProvenance,
    abi::abi_leaf_count,
    collect_local_object_arg_info_with_effects, collect_root_provenance,
    compute_object_effect_summaries, object_locality,
    object_tracking::{
        ObjectSlice, TrackedObject, collect_call_planner_root_slices, collect_tracked_objects,
        object_slice_overlaps_effect, slices_overlap,
    },
    private_abi::{self, PrivateAbiPlan},
    shape,
};

#[derive(Clone, Copy)]
pub struct ObjectByValueArgAbiConfig {
    pub inline_leaf_limit: usize,
    pub max_direct_arg_words: usize,
}

impl Default for ObjectByValueArgAbiConfig {
    fn default() -> Self {
        Self {
            inline_leaf_limit: 4,
            max_direct_arg_words: 16,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArgAbiKind {
    Direct,
    ByValueObject,
}

#[derive(Clone)]
struct ArgPlan {
    original_ty: Type,
    new_ty: Type,
    direct_words: usize,
    kind: ArgAbiKind,
}

#[derive(Clone)]
struct FuncPlan {
    args: Vec<ArgPlan>,
    new_arg_tys: SmallVec<[Type; 8]>,
    new_ret_tys: SmallVec<[Type; 4]>,
}

impl PrivateAbiPlan for FuncPlan {
    fn new_arg_tys(&self) -> &[Type] {
        &self.new_arg_tys
    }

    fn new_ret_tys(&self) -> &[Type] {
        &self.new_ret_tys
    }
}

#[derive(Clone, Copy)]
struct RewrittenArg {
    old_arg: ValueId,
    hidden_arg: ValueId,
    original_ty: Type,
}

#[derive(Clone, Copy, Default)]
enum ByValueArgLowering {
    #[default]
    Copy,
    Share {
        source_obj: ValueId,
        source_slice: ObjectSlice,
    },
    Move {
        source_obj: ValueId,
        source_slice: ObjectSlice,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum SourceOwnership {
    BorrowedLiveIn,
    OwnedByValueCopy,
    FreshLocal,
}

struct CallerElisionFacts {
    inst_liveness: InstLiveness,
    provenance: super::provenance::RootProvenanceMap,
    tracked: SecondaryMap<ValueId, Option<TrackedObject>>,
    object_memory: ObjectMemoryAnalysis,
    local_object_args: Option<FxHashMap<usize, LocalObjectArgInfo>>,
    owned_byvalue_args: FxHashSet<usize>,
    root_total_leaves: FxHashMap<ValueId, usize>,
}

#[derive(Clone)]
struct ByValueCandidate {
    arg_index: usize,
    effect: super::object_effects::ObjectArgEffect,
    source_obj: ValueId,
    source_slice: ObjectSlice,
    leaf_count: usize,
    can_share: bool,
    can_move: bool,
}

#[derive(Clone)]
struct CallParticipant {
    effect: super::object_effects::ObjectArgEffect,
    location: ParticipantLocation,
}

#[derive(Clone)]
enum ParticipantLocation {
    Exact(ObjectSlice),
    RootUnknown { root: ValueId },
    MaybeRoots(rustc_hash::FxHashSet<ValueId>),
    Unknown,
}

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
struct Score {
    avoided_leaves: usize,
    avoided_args: usize,
    share_count: usize,
}

#[derive(Default)]
pub struct ObjectByValueArgAbi {
    cfg: ObjectByValueArgAbiConfig,
}

impl ObjectByValueArgAbi {
    pub fn new(cfg: ObjectByValueArgAbiConfig) -> Self {
        Self { cfg }
    }

    pub fn run(&mut self, module: &Module) -> bool {
        let mut plans = self.collect_plans(module);
        private_abi::retain_higher_order_safe_plans(module, &mut plans);
        if plans.is_empty() {
            return false;
        }

        let old_sigs = private_abi::rewrite_declared_signatures(module, &plans);

        for (&func, plan) in &plans {
            module.func_store.modify(func, |function| {
                self.rewrite_function(function, plan);
                function.rebuild_users();
            });
        }

        let object_effects = compute_object_effect_summaries(module);
        let local_object_args = collect_local_object_arg_info_with_effects(module, &object_effects);

        for func in module.funcs() {
            module.func_store.modify(func, |function| {
                self.rewrite_calls_with_elision(
                    function,
                    plans.get(&func),
                    &plans,
                    &object_effects,
                    local_object_args.get(&func),
                );
                function.rebuild_users();
            });
        }

        private_abi::propagate_private_abi_types(module, &old_sigs);
        true
    }

    fn collect_plans(&self, module: &Module) -> FxHashMap<FuncRef, FuncPlan> {
        let mut plans = FxHashMap::default();

        for func in module.funcs() {
            let Some(sig) = module.ctx.get_sig(func) else {
                continue;
            };
            if !private_abi::is_owned_private_abi_func(&sig) {
                continue;
            }

            let mut args: Vec<_> = sig
                .args()
                .iter()
                .copied()
                .map(|ty| self.initial_arg_plan(&module.ctx, ty))
                .collect();
            let mut total_direct_words = args
                .iter()
                .map(|arg| self.direct_abi_words(arg))
                .sum::<usize>();

            if total_direct_words > self.cfg.max_direct_arg_words {
                let mut rewrite_order: Vec<_> = args
                    .iter()
                    .enumerate()
                    .filter(|(_, arg)| {
                        arg.kind == ArgAbiKind::Direct
                            && self.can_rewrite_as_object(&module.ctx, arg)
                    })
                    .map(|(idx, arg)| (idx, arg.direct_words - 1))
                    .collect();
                rewrite_order.sort_unstable_by_key(|&(idx, savings)| (Reverse(savings), idx));

                for (idx, savings) in rewrite_order {
                    if total_direct_words <= self.cfg.max_direct_arg_words {
                        break;
                    }
                    args[idx].kind = ArgAbiKind::ByValueObject;
                    args[idx].new_ty = objref_ty(&module.ctx, args[idx].original_ty);
                    total_direct_words -= savings;
                }
            }

            if total_direct_words > self.cfg.max_direct_arg_words {
                continue;
            }

            if !args.iter().any(|arg| arg.kind == ArgAbiKind::ByValueObject) {
                continue;
            }

            let new_arg_tys = args.iter().map(|arg| arg.new_ty).collect();
            let new_ret_tys = SmallVec::from_slice(sig.ret_tys());
            plans.insert(
                func,
                FuncPlan {
                    args,
                    new_arg_tys,
                    new_ret_tys,
                },
            );
        }

        plans
    }

    fn initial_arg_plan(&self, ctx: &ModuleCtx, ty: Type) -> ArgPlan {
        let direct_words = direct_word_count(ctx, ty).unwrap_or(1);
        let kind = if direct_words <= 1
            || shape::runtime_size_bytes(ctx, ty).is_some_and(|size| size == 0)
            || !shape::is_supported_aggregate_ty(ctx, ty)
            || direct_words <= self.cfg.inline_leaf_limit
        {
            ArgAbiKind::Direct
        } else {
            ArgAbiKind::ByValueObject
        };
        let new_ty = if kind == ArgAbiKind::ByValueObject {
            objref_ty(ctx, ty)
        } else {
            ty
        };

        ArgPlan {
            original_ty: ty,
            new_ty,
            direct_words,
            kind,
        }
    }

    fn can_rewrite_as_object(&self, ctx: &ModuleCtx, arg: &ArgPlan) -> bool {
        arg.direct_words > 1
            && shape::runtime_size_bytes(ctx, arg.original_ty).is_some_and(|size| size != 0)
            && shape::is_supported_aggregate_ty(ctx, arg.original_ty)
    }

    fn direct_abi_words(&self, arg: &ArgPlan) -> usize {
        match arg.kind {
            ArgAbiKind::Direct => arg.direct_words,
            ArgAbiKind::ByValueObject => 1,
        }
    }

    fn rewrite_function(&self, function: &mut Function, plan: &FuncPlan) {
        let old_args = function.arg_values.clone();
        let mut new_args = SmallVec::with_capacity(old_args.len());
        let mut rewritten = SmallVec::<[RewrittenArg; 4]>::new();

        for (&old_arg, arg_plan) in old_args.iter().zip(&plan.args) {
            let idx = new_args.len();
            match arg_plan.kind {
                ArgAbiKind::Direct => {
                    function.dfg.values[old_arg] = Value::Arg {
                        ty: arg_plan.original_ty,
                        idx,
                    };
                    new_args.push(old_arg);
                }
                ArgAbiKind::ByValueObject => {
                    let hidden_arg = function.dfg.make_value(Value::Arg {
                        ty: arg_plan.new_ty,
                        idx,
                    });
                    new_args.push(hidden_arg);
                    rewritten.push(RewrittenArg {
                        old_arg,
                        hidden_arg,
                        original_ty: arg_plan.original_ty,
                    });
                }
            }
        }

        function.arg_values = new_args;
        for arg in rewritten {
            self.rewrite_byvalue_arg(function, arg);
        }
    }

    fn rewrite_byvalue_arg(&self, function: &mut Function, arg: RewrittenArg) {
        self.try_fold_entry_copy_root(function, arg);
        if function.dfg.users_num(arg.old_arg) != 0 {
            let loaded = self.insert_entry_obj_load(function, arg.hidden_arg, arg.original_ty);
            function.dfg.change_to_alias(arg.old_arg, loaded);
        }
        function.dfg.values[arg.old_arg] = Value::Undef {
            ty: arg.original_ty,
        };
    }

    fn insert_entry_obj_load(&self, function: &mut Function, object: ValueId, ty: Type) -> ValueId {
        let Some(entry) = function.layout.entry_block() else {
            return function.dfg.make_undef_value(ty);
        };
        let loc = CursorLocation::BlockTop(entry);
        let mut cursor = InstInserter::at_location(loc);
        let load_inst = cursor.insert_inst_data(
            function,
            data::ObjLoad::new_unchecked(function.inst_set(), object),
        );
        let loaded = cursor.make_result(function, load_inst, ty);
        cursor.attach_result(function, load_inst, loaded);
        loaded
    }

    fn try_fold_entry_copy_root(&self, function: &mut Function, arg: RewrittenArg) {
        let Some(entry) = function.layout.entry_block() else {
            return;
        };
        let candidates = self.collect_copy_root_candidates(function, entry, arg);
        let [candidate] = candidates.as_slice() else {
            return;
        };

        function.dfg.change_to_alias(candidate.root, arg.hidden_arg);
        function.layout.remove_inst(candidate.store_inst);
        function.erase_inst(candidate.store_inst);
        function.layout.remove_inst(candidate.alloc_inst);
        function.erase_inst(candidate.alloc_inst);
    }

    fn collect_copy_root_candidates(
        &self,
        function: &Function,
        entry: sonatina_ir::BlockId,
        arg: RewrittenArg,
    ) -> SmallVec<[CopyRootCandidate; 2]> {
        let mut candidates = SmallVec::new();
        for &user in function.dfg.users(arg.old_arg) {
            let Some(store) =
                downcast::<&data::ObjStore>(function.inst_set(), function.dfg.inst(user))
            else {
                continue;
            };
            if *store.value() != arg.old_arg {
                continue;
            }
            let root = *store.object();
            let Some(alloc_inst) = function.dfg.value_inst(root) else {
                continue;
            };
            let Some(obj_alloc) =
                downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(alloc_inst))
            else {
                continue;
            };
            if *obj_alloc.ty() != arg.original_ty
                || function.layout.inst_block(alloc_inst) != entry
                || function.layout.inst_block(user) != entry
                || function.dfg.value_ty(root) != function.dfg.value_ty(arg.hidden_arg)
                || !self.root_has_single_entry_copy_store(function, entry, root, user, arg.old_arg)
            {
                continue;
            }
            candidates.push(CopyRootCandidate {
                alloc_inst,
                store_inst: user,
                root,
            });
        }
        candidates
    }

    fn root_has_single_entry_copy_store(
        &self,
        function: &Function,
        entry: sonatina_ir::BlockId,
        root: ValueId,
        store_inst: InstId,
        old_arg: ValueId,
    ) -> bool {
        let mut first_user = None;
        let mut whole_store_count = 0usize;
        for inst in function.layout.iter_inst(entry) {
            if !inst_uses_value(function, inst, root) {
                continue;
            }
            if first_user.is_none() {
                first_user = Some(inst);
            }
            if let Some(store) =
                downcast::<&data::ObjStore>(function.inst_set(), function.dfg.inst(inst))
                && *store.object() == root
            {
                whole_store_count += 1;
                if inst != store_inst || *store.value() != old_arg {
                    return false;
                }
            }
        }
        for &user in function.dfg.users(root) {
            if function.layout.inst_block(user) == entry {
                continue;
            }
            if let Some(store) =
                downcast::<&data::ObjStore>(function.inst_set(), function.dfg.inst(user))
                && *store.object() == root
            {
                return false;
            }
        }
        first_user == Some(store_inst) && whole_store_count == 1
    }

    fn rewrite_calls_with_elision(
        &self,
        function: &mut Function,
        current_plan: Option<&FuncPlan>,
        plans: &FxHashMap<FuncRef, FuncPlan>,
        object_effects: &ObjectEffectSummaryMap,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
    ) {
        if !function_has_planned_call(function, plans) {
            return;
        }

        let facts = self.collect_caller_elision_facts(
            function,
            current_plan,
            object_effects,
            local_object_args,
        );
        let blocks: Vec<_> = function.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = function.layout.iter_inst(block).collect();
            for inst in insts {
                if !function.layout.is_inst_inserted(inst) {
                    continue;
                }
                let Some(call) =
                    downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst))
                        .cloned()
                else {
                    continue;
                };
                let Some(plan) = plans.get(call.callee()) else {
                    continue;
                };
                self.rewrite_call_with_elision(function, inst, &call, plan, object_effects, &facts);
            }
        }
    }

    fn collect_caller_elision_facts(
        &self,
        function: &Function,
        current_plan: Option<&FuncPlan>,
        object_effects: &ObjectEffectSummaryMap,
        local_object_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
    ) -> CallerElisionFacts {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);
        let mut liveness = Liveness::new();
        liveness.compute(function, &cfg);
        let mut inst_liveness = InstLiveness::new();
        inst_liveness.compute(function, &cfg, &liveness);

        let mut layout_cache = shape::AggregateLayoutCache::default();
        let root_slices =
            collect_call_planner_root_slices(function, object_effects, &mut layout_cache);
        let root_total_leaves = root_slices
            .iter()
            .map(|(&root, slice)| (root, slice.leaf_count))
            .collect();
        let provenance = collect_root_provenance(
            function,
            function.ctx(),
            &root_slices,
            &mut layout_cache,
            Some(object_effects),
        );
        let tracked = collect_tracked_objects(function, &provenance, &mut layout_cache);

        let mut object_memory = ObjectMemoryAnalysis::default();
        object_memory.compute_for_call_planner(function, local_object_args, object_effects);

        CallerElisionFacts {
            inst_liveness,
            provenance,
            tracked,
            object_memory,
            local_object_args: local_object_args.cloned(),
            owned_byvalue_args: current_plan
                .map(|plan| {
                    plan.args
                        .iter()
                        .enumerate()
                        .filter(|(_, arg)| arg.kind == ArgAbiKind::ByValueObject)
                        .map(|(idx, _)| idx)
                        .collect()
                })
                .unwrap_or_default(),
            root_total_leaves,
        }
    }

    fn rewrite_call_with_elision(
        &self,
        function: &mut Function,
        inst: InstId,
        call: &control_flow::Call,
        plan: &FuncPlan,
        object_effects: &ObjectEffectSummaryMap,
        facts: &CallerElisionFacts,
    ) {
        let lowerings = self.plan_call_lowerings(function, inst, call, plan, object_effects, facts);
        let summary = object_effects.get(call.callee());
        let loc = function.layout.prev_inst_of(inst).map_or(
            CursorLocation::BlockTop(function.layout.inst_block(inst)),
            CursorLocation::At,
        );
        let mut cursor = InstInserter::at_location(loc);
        let mut new_args = SmallVec::<[ValueId; 8]>::new();
        let mut readonly_copy_cache = FxHashMap::<ValueId, ValueId>::default();

        for (idx, (&arg, arg_plan)) in call.args().iter().zip(&plan.args).enumerate() {
            match arg_plan.kind {
                ArgAbiKind::Direct => new_args.push(arg),
                ArgAbiKind::ByValueObject => match lowerings[idx] {
                    ByValueArgLowering::Copy => {
                        let can_reuse_copy = summary
                            .and_then(|summary| summary.arg_effects.get(idx))
                            .is_some_and(|effect| effect.writes.is_empty() && effect.local_only);
                        if can_reuse_copy && let Some(&cached_copy) = readonly_copy_cache.get(&arg)
                        {
                            new_args.push(cached_copy);
                            continue;
                        }
                        let alloc_inst = cursor.insert_inst_data(
                            function,
                            data::ObjAlloc::new_unchecked(
                                function.inst_set(),
                                arg_plan.original_ty,
                            ),
                        );
                        let object = cursor.make_result(function, alloc_inst, arg_plan.new_ty);
                        cursor.attach_result(function, alloc_inst, object);
                        cursor.set_location(CursorLocation::At(alloc_inst));
                        cursor.insert_inst_data(
                            function,
                            data::ObjStore::new_unchecked(function.inst_set(), object, arg),
                        );
                        if can_reuse_copy {
                            readonly_copy_cache.insert(arg, object);
                        }
                        new_args.push(object);
                    }
                    ByValueArgLowering::Share { source_obj, .. }
                    | ByValueArgLowering::Move { source_obj, .. } => new_args.push(source_obj),
                },
            }
        }

        function.dfg.replace_inst(
            inst,
            Box::new(control_flow::Call::new(
                function
                    .inst_set()
                    .has_call()
                    .expect("target ISA must support `call`"),
                *call.callee(),
                new_args,
            )),
        );
    }

    fn plan_call_lowerings(
        &self,
        function: &Function,
        inst: InstId,
        call: &control_flow::Call,
        plan: &FuncPlan,
        object_effects: &ObjectEffectSummaryMap,
        facts: &CallerElisionFacts,
    ) -> Vec<ByValueArgLowering> {
        let mut lowerings = vec![ByValueArgLowering::Copy; plan.args.len()];
        let Some(summary) = object_effects.get(call.callee()) else {
            return lowerings;
        };
        if self.call_has_indirect_objref_arg(function, call, plan) {
            return lowerings;
        }

        let fixed = self.collect_fixed_participants(function, call, plan, summary, facts);
        let candidates =
            self.collect_byvalue_candidates(function, inst, call, plan, object_effects, facts);
        let chosen = self.choose_candidate_lowerings(&candidates, &fixed);
        for (candidate, lowering) in candidates.iter().zip(chosen) {
            lowerings[candidate.arg_index] = lowering;
        }
        lowerings
    }

    fn call_has_indirect_objref_arg(
        &self,
        function: &Function,
        call: &control_flow::Call,
        plan: &FuncPlan,
    ) -> bool {
        call.args().iter().zip(&plan.args).any(|(&arg, arg_plan)| {
            arg_plan.kind == ArgAbiKind::Direct
                && !function.dfg.value_ty(arg).is_obj_ref(function.ctx())
                && has_nested_objref(function.ctx(), function.dfg.value_ty(arg))
        })
    }

    fn collect_fixed_participants(
        &self,
        function: &Function,
        call: &control_flow::Call,
        plan: &FuncPlan,
        summary: &super::object_effects::ObjectEffectSummary,
        facts: &CallerElisionFacts,
    ) -> Vec<CallParticipant> {
        let mut fixed = Vec::new();
        for (idx, (&arg, arg_plan)) in call.args().iter().zip(&plan.args).enumerate() {
            if arg_plan.kind != ArgAbiKind::Direct
                || !function.dfg.value_ty(arg).is_obj_ref(function.ctx())
            {
                continue;
            }
            let Some(effect) = summary.arg_effects.get(idx).cloned() else {
                continue;
            };
            fixed.push(CallParticipant {
                effect,
                location: self.participant_location(arg, facts),
            });
        }
        fixed
    }

    fn collect_byvalue_candidates(
        &self,
        function: &Function,
        inst: InstId,
        call: &control_flow::Call,
        plan: &FuncPlan,
        object_effects: &ObjectEffectSummaryMap,
        facts: &CallerElisionFacts,
    ) -> Vec<ByValueCandidate> {
        let Some(summary) = object_effects.get(call.callee()) else {
            return Vec::new();
        };
        let mut candidates = Vec::new();
        for (idx, (&arg, arg_plan)) in call.args().iter().zip(&plan.args).enumerate() {
            if arg_plan.kind != ArgAbiKind::ByValueObject {
                continue;
            }
            let Some((source_obj, source_slice)) =
                self.direct_byval_source(function, inst, arg, arg_plan.new_ty, facts)
            else {
                continue;
            };
            let Some(effect) = summary.arg_effects.get(idx).cloned() else {
                continue;
            };
            let can_share = effect.writes.is_empty() && effect.local_only;
            let can_move = self
                .source_ownership_kind(function, source_slice, facts)
                .is_some_and(|ownership| ownership != SourceOwnership::BorrowedLiveIn)
                && self.source_can_move(function, source_slice, object_effects)
                && !self.move_has_live_alias_after_call(function, inst, source_slice, facts);
            if !can_share && !can_move {
                continue;
            }
            candidates.push(ByValueCandidate {
                arg_index: idx,
                effect,
                source_obj,
                source_slice,
                leaf_count: source_slice.leaf_count,
                can_share,
                can_move,
            });
        }
        candidates
    }

    fn direct_byval_source(
        &self,
        function: &Function,
        call_inst: InstId,
        actual: ValueId,
        expected_objref_ty: Type,
        facts: &CallerElisionFacts,
    ) -> Option<(ValueId, ObjectSlice)> {
        let load_inst = function.dfg.value_inst(actual)?;
        let obj_load =
            downcast::<&data::ObjLoad>(function.inst_set(), function.dfg.inst(load_inst))?;
        let source_obj = *obj_load.object();
        if function.dfg.value_ty(source_obj) != expected_objref_ty {
            return None;
        }
        let source_slice = facts.tracked[source_obj].and_then(TrackedObject::exact)?;
        facts
            .object_memory
            .value_matches_current_object_slice_before_inst(call_inst, actual, source_slice)
            .then_some((source_obj, source_slice))
    }

    fn source_ownership_kind(
        &self,
        function: &Function,
        source_slice: ObjectSlice,
        facts: &CallerElisionFacts,
    ) -> Option<SourceOwnership> {
        let root = source_slice.root;
        if let Some(arg_index) = function.arg_values.iter().position(|&arg| arg == root) {
            if facts.owned_byvalue_args.contains(&arg_index) {
                return Some(SourceOwnership::OwnedByValueCopy);
            }
            if facts
                .local_object_args
                .as_ref()
                .and_then(|args| args.get(&arg_index))
                .is_some_and(|info| info.init == super::RootInit::UndefFresh)
            {
                return Some(SourceOwnership::FreshLocal);
            }
            return Some(SourceOwnership::BorrowedLiveIn);
        }

        let def_inst = function.dfg.value_inst(root)?;
        if downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(def_inst)).is_some() {
            return Some(SourceOwnership::FreshLocal);
        }

        downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(def_inst))
            .filter(|_| facts.root_total_leaves.contains_key(&root))
            .map(|_| SourceOwnership::FreshLocal)
    }

    fn source_can_move(
        &self,
        function: &Function,
        source_slice: ObjectSlice,
        object_effects: &ObjectEffectSummaryMap,
    ) -> bool {
        let root = source_slice.root;
        object_locality::object_root_stays_local_with_effects(
            function,
            root,
            function.dfg.value_ty(root),
            object_effects,
            |value| value == root,
            false,
        )
    }

    fn move_has_live_alias_after_call(
        &self,
        function: &Function,
        inst: InstId,
        source_slice: ObjectSlice,
        facts: &CallerElisionFacts,
    ) -> bool {
        facts.inst_liveness.live_out(inst).iter().any(|value| {
            let ty = function.dfg.value_ty(value);
            (ty.is_obj_ref(function.ctx())
                && self
                    .participant_location(value, facts)
                    .may_overlap_move_source(source_slice))
                || (!ty.is_obj_ref(function.ctx()) && has_nested_objref(function.ctx(), ty))
        })
    }

    fn participant_location(
        &self,
        value: ValueId,
        facts: &CallerElisionFacts,
    ) -> ParticipantLocation {
        if let Some(tracked) = facts.tracked[value] {
            return match tracked {
                TrackedObject::Exact(slice) => ParticipantLocation::Exact(slice),
                TrackedObject::RootUnknown { root, .. } => {
                    ParticipantLocation::RootUnknown { root }
                }
            };
        }

        match facts.provenance.provenance(value) {
            RootProvenance::Exact(projection) => facts
                .root_total_leaves
                .get(&projection.root_value)
                .copied()
                .map_or(
                    ParticipantLocation::RootUnknown {
                        root: projection.root_value,
                    },
                    |total_leaves| {
                        ParticipantLocation::Exact(ObjectSlice {
                            root: projection.root_value,
                            ty: projection.slice.ty,
                            first_leaf: projection.slice.first_leaf,
                            leaf_count: projection.slice.leaf_count,
                            total_leaves,
                        })
                    },
                ),
            RootProvenance::SameRoot(root) => ParticipantLocation::RootUnknown { root },
            RootProvenance::Maybe(roots) => ParticipantLocation::MaybeRoots(roots),
            RootProvenance::Unknown => ParticipantLocation::Unknown,
        }
    }

    fn choose_candidate_lowerings(
        &self,
        candidates: &[ByValueCandidate],
        fixed: &[CallParticipant],
    ) -> Vec<ByValueArgLowering> {
        if candidates.len() <= 8 {
            self.choose_candidate_lowerings_exhaustive(candidates, fixed)
        } else {
            self.choose_candidate_lowerings_greedy(candidates, fixed)
        }
    }

    fn choose_candidate_lowerings_exhaustive(
        &self,
        candidates: &[ByValueCandidate],
        fixed: &[CallParticipant],
    ) -> Vec<ByValueArgLowering> {
        let mut best = vec![ByValueArgLowering::Copy; candidates.len()];
        let mut best_score = Score::default();
        let mut current = vec![ByValueArgLowering::Copy; candidates.len()];
        self.search_candidate_lowerings(
            candidates,
            fixed,
            0,
            &mut current,
            &mut best,
            &mut best_score,
        );
        best
    }

    fn search_candidate_lowerings(
        &self,
        candidates: &[ByValueCandidate],
        fixed: &[CallParticipant],
        idx: usize,
        current: &mut [ByValueArgLowering],
        best: &mut Vec<ByValueArgLowering>,
        best_score: &mut Score,
    ) {
        if idx == candidates.len() {
            let score = self.score_candidate_lowerings(candidates, current);
            if score > *best_score {
                *best_score = score;
                best.clear();
                best.extend_from_slice(current);
            }
            return;
        }

        for mode in self.candidate_modes(&candidates[idx]) {
            if !self.lowering_is_compatible(candidates, fixed, current, idx, mode) {
                continue;
            }
            current[idx] = mode;
            self.search_candidate_lowerings(candidates, fixed, idx + 1, current, best, best_score);
        }
        current[idx] = ByValueArgLowering::Copy;
    }

    fn choose_candidate_lowerings_greedy(
        &self,
        candidates: &[ByValueCandidate],
        fixed: &[CallParticipant],
    ) -> Vec<ByValueArgLowering> {
        let mut chosen = vec![ByValueArgLowering::Copy; candidates.len()];
        let mut order: Vec<_> = (0..candidates.len()).collect();
        order.sort_unstable_by_key(|&idx| {
            (
                Reverse(candidates[idx].leaf_count),
                candidates[idx].arg_index,
            )
        });
        for idx in order {
            for mode in self.candidate_modes(&candidates[idx]) {
                if self.lowering_is_compatible(candidates, fixed, &chosen, idx, mode) {
                    chosen[idx] = mode;
                    break;
                }
            }
        }
        chosen
    }

    fn score_candidate_lowerings(
        &self,
        candidates: &[ByValueCandidate],
        lowerings: &[ByValueArgLowering],
    ) -> Score {
        let mut score = Score::default();
        for (candidate, lowering) in candidates.iter().zip(lowerings) {
            match lowering {
                ByValueArgLowering::Copy => {}
                ByValueArgLowering::Share { .. } => {
                    score.avoided_leaves += candidate.leaf_count;
                    score.avoided_args += 1;
                    score.share_count += 1;
                }
                ByValueArgLowering::Move { .. } => {
                    score.avoided_leaves += candidate.leaf_count;
                    score.avoided_args += 1;
                }
            }
        }
        score
    }

    fn candidate_modes(&self, candidate: &ByValueCandidate) -> SmallVec<[ByValueArgLowering; 3]> {
        let mut modes = SmallVec::new();
        if candidate.can_share {
            modes.push(ByValueArgLowering::Share {
                source_obj: candidate.source_obj,
                source_slice: candidate.source_slice,
            });
        }
        if candidate.can_move {
            modes.push(ByValueArgLowering::Move {
                source_obj: candidate.source_obj,
                source_slice: candidate.source_slice,
            });
        }
        modes.push(ByValueArgLowering::Copy);
        modes
    }

    fn lowering_is_compatible(
        &self,
        candidates: &[ByValueCandidate],
        fixed: &[CallParticipant],
        current: &[ByValueArgLowering],
        new_idx: usize,
        new_mode: ByValueArgLowering,
    ) -> bool {
        let Some(new_source_slice) = new_mode.source_slice() else {
            return true;
        };
        let new_participant = candidates[new_idx].participant();

        if fixed
            .iter()
            .any(|participant| self.lowering_conflicts(new_mode, new_source_slice, participant))
        {
            return false;
        }

        for (other_idx, &other_mode) in current.iter().enumerate() {
            if other_idx == new_idx || matches!(other_mode, ByValueArgLowering::Copy) {
                continue;
            }
            let other_source_slice = candidates[other_idx].source_slice;
            let other_participant = candidates[other_idx].participant();
            if self.lowering_conflicts(new_mode, new_source_slice, &other_participant)
                || self.lowering_conflicts(other_mode, other_source_slice, &new_participant)
            {
                return false;
            }
        }

        true
    }

    fn lowering_conflicts(
        &self,
        lowering: ByValueArgLowering,
        source_slice: ObjectSlice,
        participant: &CallParticipant,
    ) -> bool {
        match lowering {
            ByValueArgLowering::Copy => false,
            ByValueArgLowering::Share { .. } => {
                participant.location.may_overlap(source_slice)
                    && effect_may_overlap_slice(
                        source_slice,
                        &participant.location,
                        &participant.effect.writes,
                    )
            }
            ByValueArgLowering::Move { .. } => {
                participant.location.may_overlap(source_slice)
                    && (!participant.effect.local_only
                        || effect_may_overlap_slice(
                            source_slice,
                            &participant.location,
                            &participant.effect.reads,
                        )
                        || effect_may_overlap_slice(
                            source_slice,
                            &participant.location,
                            &participant.effect.writes,
                        ))
            }
        }
    }
}

impl ByValueArgLowering {
    fn source_slice(self) -> Option<ObjectSlice> {
        match self {
            Self::Copy => None,
            Self::Share { source_slice, .. } | Self::Move { source_slice, .. } => {
                Some(source_slice)
            }
        }
    }
}

impl ByValueCandidate {
    fn participant(&self) -> CallParticipant {
        CallParticipant {
            effect: self.effect.clone(),
            location: ParticipantLocation::Exact(self.source_slice),
        }
    }
}

impl ParticipantLocation {
    fn may_overlap(&self, source_slice: ObjectSlice) -> bool {
        match self {
            Self::Exact(slice) => slices_overlap(*slice, source_slice),
            Self::RootUnknown { root } => *root == source_slice.root,
            Self::MaybeRoots(roots) => roots.contains(&source_slice.root),
            Self::Unknown => true,
        }
    }

    fn may_overlap_move_source(&self, source_slice: ObjectSlice) -> bool {
        self.may_overlap(source_slice)
    }
}

fn effect_may_overlap_slice(
    source_slice: ObjectSlice,
    location: &ParticipantLocation,
    effect: &super::SliceSet,
) -> bool {
    match location {
        ParticipantLocation::Exact(base_slice) => {
            slice_set_may_overlap(source_slice, *base_slice, effect)
        }
        ParticipantLocation::RootUnknown { root } => {
            *root == source_slice.root && !effect.is_empty()
        }
        ParticipantLocation::MaybeRoots(roots) => {
            roots.contains(&source_slice.root) && !effect.is_empty()
        }
        ParticipantLocation::Unknown => !effect.is_empty(),
    }
}

fn slice_set_may_overlap(
    source_slice: ObjectSlice,
    base_slice: ObjectSlice,
    effect: &super::SliceSet,
) -> bool {
    if effect.is_empty() || !slices_overlap(source_slice, base_slice) {
        return false;
    }
    if effect.is_whole_root() {
        return true;
    }
    effect
        .exact_leaves()
        .is_none_or(|leaves| object_slice_overlaps_effect(source_slice, base_slice, leaves))
}

fn function_has_planned_call(function: &Function, plans: &FxHashMap<FuncRef, FuncPlan>) -> bool {
    function.layout.iter_block().any(|block| {
        function.layout.iter_inst(block).any(|inst| {
            downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst))
                .is_some_and(|call| plans.contains_key(call.callee()))
        })
    })
}

fn has_nested_objref(ctx: &ModuleCtx, ty: Type) -> bool {
    let mut seen = rustc_hash::FxHashSet::default();
    let mut worklist = vec![ty];

    while let Some(current) = worklist.pop() {
        let Type::Compound(compound) = current else {
            continue;
        };
        if !seen.insert(compound) {
            continue;
        }

        match ctx.with_ty_store(|store| store.resolve_compound(compound).clone()) {
            CompoundType::Array { elem, .. }
            | CompoundType::Ptr(elem)
            | CompoundType::ConstRef(elem) => worklist.push(elem),
            CompoundType::ObjRef(_) => return true,
            CompoundType::Struct(data) => worklist.extend(data.fields),
            CompoundType::Enum(data) => {
                for variant in data.variants {
                    worklist.extend(variant.fields);
                }
            }
            CompoundType::Func { args, ret_tys } => {
                worklist.extend(args);
                worklist.extend(ret_tys);
            }
        }
    }

    false
}

#[derive(Clone, Copy)]
struct CopyRootCandidate {
    alloc_inst: InstId,
    store_inst: InstId,
    root: ValueId,
}

fn direct_word_count(ctx: &ModuleCtx, ty: Type) -> Option<usize> {
    if shape::runtime_size_bytes(ctx, ty)? == 0 {
        return Some(0);
    }
    if !shape::is_supported_aggregate_ty(ctx, ty) {
        return Some(1);
    }
    abi_leaf_count(ctx, ty)
}

fn inst_uses_value(function: &Function, inst: InstId, value: ValueId) -> bool {
    let mut used = false;
    function.dfg.inst(inst).for_each_value(&mut |inst_value| {
        if inst_value == value {
            used = true;
        }
    });
    used
}

fn objref_ty(ctx: &ModuleCtx, ty: Type) -> Type {
    ctx.with_ty_store_mut(|store| store.make_obj_ref(ty))
}

#[allow(dead_code)]
fn objref_element_ty(ctx: &ModuleCtx, ty: Type) -> Option<Type> {
    let CompoundType::ObjRef(elem) = ty.resolve_compound(ctx)? else {
        return None;
    };
    Some(elem)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::{EvmBackend, PushWidthPolicy, test_util::prepare_root},
        object::{CompileOptions, compile_all_objects},
    };
    use sonatina_ir::{
        Function, Module, ValueId,
        inst::{control_flow, data, downcast},
        ir_writer::FuncWriter,
        isa::evm::Evm,
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

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

    fn run_byvalue_arg_abi(module: &Module) {
        ObjectByValueArgAbi::default().run(module);
        let report = verify_module(
            module,
            &VerifierConfig::for_level(VerificationLevel::Standard),
        );
        assert!(
            !report.has_errors(),
            "module should verify after rewrite:\n{report}"
        );
    }

    fn dump_func(module: &Module, name: &str) -> String {
        let func_ref = lookup_func(module, name);
        module.func_store.view(func_ref, |func| {
            FuncWriter::new(func_ref, func).dump_string()
        })
    }

    fn count_obj_allocs(module: &Module, name: &str) -> usize {
        let func_ref = lookup_func(module, name);
        module.func_store.view(func_ref, count_func_obj_allocs)
    }

    fn count_func_obj_allocs(func: &Function) -> usize {
        let mut count = 0;
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_some() {
                    count += 1;
                }
            }
        }
        count
    }

    fn first_call_args(module: &Module, caller: &str, callee: &str) -> Vec<ValueId> {
        let caller_ref = lookup_func(module, caller);
        let callee_ref = lookup_func(module, callee);
        module.func_store.view(caller_ref, |func| {
            let mut found = None;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    let Some(call) =
                        downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                    else {
                        continue;
                    };
                    if *call.callee() != callee_ref {
                        continue;
                    }
                    assert!(found.is_none(), "expected a single call to {callee}");
                    found = Some(call.args().to_vec());
                }
            }
            found.expect("call should exist")
        })
    }

    fn first_obj_alloc_result(module: &Module, func_name: &str) -> ValueId {
        let func_ref = lookup_func(module, func_name);
        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_none() {
                        continue;
                    }
                    return func
                        .dfg
                        .inst_result(inst)
                        .expect("obj.alloc should have a result");
                }
            }
            panic!("expected an obj.alloc in {func_name}");
        })
    }

    fn value_is_obj_alloc(func: &Function, value: ValueId) -> bool {
        func.dfg.value_inst(value).is_some_and(|inst| {
            downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)).is_some()
        })
    }

    fn value_is_arg(func: &Function, value: ValueId) -> bool {
        matches!(func.dfg.values[value], Value::Arg { .. })
    }

    fn test_backend() -> EvmBackend {
        let triple = TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        );
        EvmBackend::new(Evm::new(triple))
    }

    #[test]
    fn rewrites_large_byvalue_array_args_to_objrefs() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %sum(v0.[i256; 20]) -> i256 {
block0:
    v1.i256 = extract_value v0 0.i8;
    return v1;
}

func public %entry() -> i256 {
block0:
    v0.[i256; 20] = insert_value undef.[i256; 20] 0.i8 1.i256;
    v1.i256 = call %sum v0;
    return v1;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );

        ObjectByValueArgAbi::default().run(&module);

        let sum = lookup_func(&module, "sum");
        let sig = module.ctx.get_sig(sum).expect("signature should exist");
        assert!(matches!(sig.args(), [Type::Compound(_)]));
        let arg_ty = sig.args()[0];
        assert!(objref_element_ty(&module.ctx, arg_ty).is_some());

        let report = verify_module(
            &module,
            &VerifierConfig::for_level(VerificationLevel::Standard),
        );
        assert!(
            !report.has_errors(),
            "module should verify after rewrite:\n{report}"
        );
    }

    #[test]
    fn keeps_small_aggregates_direct() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @pair = { i256, i256 };

func private %swap(v0.@pair) -> @pair {
block0:
    return v0;
}
"#,
        );

        ObjectByValueArgAbi::default().run(&module);

        let swap = lookup_func(&module, "swap");
        let sig = module.ctx.get_sig(swap).expect("signature should exist");
        let Type::Compound(pair_ty) = sig.args()[0] else {
            panic!("pair arg should stay direct");
        };
        let compound = module
            .ctx
            .with_ty_store(|store| store.resolve_compound(pair_ty).clone());
        assert!(matches!(compound, CompoundType::Struct(_)));
    }

    #[test]
    fn readonly_byvalue_call_shares_direct_loaded_root() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @holder = { objref<[i256; 8]> };

func private %readonly(v0.[i256; 8]) -> i256 {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v1 v0;
    v2.[i256; 8] = obj.load v1;
    v3.i256 = extract_value v2 0.i8;
    return v3;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.[i256; 8] = insert_value undef.[i256; 8] 0.i8 1.i256;
    obj.store v0 v1;
    v2.[i256; 8] = obj.load v0;
    v3.i256 = call %readonly v2;
    return v3;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let source_root = first_obj_alloc_result(&module, "caller");
        let call_args = first_call_args(&module, "caller", "readonly");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            1,
            "unexpected caller IR:\n{dumped}"
        );
        assert_eq!(
            call_args,
            vec![source_root],
            "readonly path should share:\n{dumped}"
        );
    }

    #[test]
    fn mutating_byvalue_call_moves_fresh_dead_root() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %mutate(v0.[i256; 8]) -> i256 {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v1 v0;
    v2.objref<i256> = obj.index v1 0.i8;
    obj.store v2 9.i256;
    v3.[i256; 8] = obj.load v1;
    v4.i256 = extract_value v3 0.i8;
    return v4;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.[i256; 8] = insert_value undef.[i256; 8] 0.i8 1.i256;
    obj.store v0 v1;
    v2.[i256; 8] = obj.load v0;
    v3.i256 = call %mutate v2;
    return v3;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let source_root = first_obj_alloc_result(&module, "caller");
        let call_args = first_call_args(&module, "caller", "mutate");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            1,
            "unexpected caller IR:\n{dumped}"
        );
        assert_eq!(
            call_args,
            vec![source_root],
            "mutating dead-root path should move:\n{dumped}"
        );
    }

    #[test]
    fn same_source_two_readonly_byvalue_args_share_both() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %pair_read(v0.[i256; 8], v1.[i256; 8]) -> i256 {
block0:
    v2.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v2 v0;
    v3.[i256; 8] = obj.load v2;
    v4.i256 = extract_value v3 0.i8;
    v5.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v5 v1;
    v6.[i256; 8] = obj.load v5;
    v7.i256 = extract_value v6 1.i8;
    v8.i256 = add v4 v7;
    return v8;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.[i256; 8] = insert_value undef.[i256; 8] 1.i8 2.i256;
    obj.store v0 v1;
    v2.[i256; 8] = obj.load v0;
    v3.i256 = call %pair_read v2 v2;
    return v3;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let source_root = first_obj_alloc_result(&module, "caller");
        let call_args = first_call_args(&module, "caller", "pair_read");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            1,
            "unexpected caller IR:\n{dumped}"
        );
        assert_eq!(
            call_args,
            vec![source_root, source_root],
            "both readonly args should share the same source:\n{dumped}"
        );
    }

    #[test]
    fn writer_and_readonly_same_source_choose_one_copy() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %mix(v0.[i256; 8], v1.[i256; 8]) -> i256 {
block0:
    v2.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v2 v0;
    v3.objref<i256> = obj.index v2 0.i8;
    obj.store v3 9.i256;
    v4.[i256; 8] = obj.load v2;
    v5.i256 = extract_value v4 0.i8;
    v6.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v6 v1;
    v7.[i256; 8] = obj.load v6;
    v8.i256 = extract_value v7 0.i8;
    v9.i256 = add v5 v8;
    return v9;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.[i256; 8] = insert_value undef.[i256; 8] 0.i8 1.i256;
    obj.store v0 v1;
    v2.[i256; 8] = obj.load v0;
    v3.i256 = call %mix v2 v2;
    return v3;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let source_root = first_obj_alloc_result(&module, "caller");
        let call_args = first_call_args(&module, "caller", "mix");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            2,
            "unexpected caller IR:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_obj_alloc(func, call_args[0]) && call_args[0] != source_root,
                "writer arg should copy:\n{dumped}"
            );
            assert_eq!(
                call_args[1], source_root,
                "readonly arg should share:\n{dumped}"
            );
        });
    }

    #[test]
    fn explicit_objref_writer_forces_byvalue_copy() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %mix(v0.[i256; 8], v1.objref<[i256; 8]>) -> i256 {
block0:
    v2.objref<i256> = obj.index v1 0.i8;
    obj.store v2 7.i256;
    v3.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v3 v0;
    v4.[i256; 8] = obj.load v3;
    v5.i256 = extract_value v4 0.i8;
    return v5;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.[i256; 8] = insert_value undef.[i256; 8] 0.i8 1.i256;
    obj.store v0 v1;
    v2.[i256; 8] = obj.load v0;
    v3.i256 = call %mix v2 v0;
    return v3;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let source_root = first_obj_alloc_result(&module, "caller");
        let call_args = first_call_args(&module, "caller", "mix");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            2,
            "unexpected caller IR:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_obj_alloc(func, call_args[0]) && call_args[0] != source_root,
                "by-value arg should copy when explicit objref writes overlap:\n{dumped}"
            );
            assert_eq!(
                call_args[1], source_root,
                "explicit objref arg should stay direct:\n{dumped}"
            );
        });
    }

    #[test]
    fn stale_loaded_value_never_direct_passes_root() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @holder = { objref<[i256; 8]> };

func private %readonly(v0.[i256; 8]) -> i256 {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v1 v0;
    v2.[i256; 8] = obj.load v1;
    v3.i256 = extract_value v2 0.i8;
    return v3;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.[i256; 8] = insert_value undef.[i256; 8] 0.i8 1.i256;
    obj.store v0 v1;
    v2.[i256; 8] = obj.load v0;
    v3.objref<i256> = obj.index v0 0.i8;
    obj.store v3 9.i256;
    v4.i256 = call %readonly v2;
    return v4;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let source_root = first_obj_alloc_result(&module, "caller");
        let call_args = first_call_args(&module, "caller", "readonly");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            2,
            "unexpected caller IR:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_obj_alloc(func, call_args[0]) && call_args[0] != source_root,
                "stale load must copy instead of direct-passing the root:\n{dumped}"
            );
        });
    }

    #[test]
    fn hidden_byvalue_forwarding_chain_reuses_hidden_objref_arg() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @holder = { objref<[i256; 8]> };

func private %readonly(v0.[i256; 8]) -> i256 {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v1 v0;
    v2.[i256; 8] = obj.load v1;
    v3.i256 = extract_value v2 0.i8;
    return v3;
}

func private %forward(v0.[i256; 8]) -> i256 {
block0:
    v1.i256 = call %readonly v0;
    return v1;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let forward_ref = lookup_func(&module, "forward");
        let call_args = first_call_args(&module, "forward", "readonly");
        let dumped = dump_func(&module, "forward");
        module.func_store.view(forward_ref, |func| {
            assert_eq!(
                count_func_obj_allocs(func),
                0,
                "forwarder should not allocate a temp:\n{dumped}"
            );
            assert!(
                value_is_arg(func, call_args[0])
                    && func.dfg.value_ty(call_args[0]).is_obj_ref(func.ctx()),
                "forwarder should pass its hidden objref arg directly:\n{dumped}"
            );
        });
    }

    #[test]
    fn disjoint_sibling_writer_allows_zero_copy_share() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %disjoint(v0.[i256; 8], v1.objref<[i256; 8]>) -> i256 {
block0:
    v2.objref<i256> = obj.index v1 0.i8;
    obj.store v2 5.i256;
    v3.i256 = extract_value v0 0.i8;
    return v3;
}

func private %caller() -> i256 {
block0:
    v0.objref<[[i256; 8]; 2]> = obj.alloc [[i256; 8]; 2];
    v1.[i256; 8] = insert_value undef.[i256; 8] 0.i8 1.i256;
    v2.[i256; 8] = insert_value undef.[i256; 8] 0.i8 2.i256;
    v3.[[i256; 8]; 2] = insert_value undef.[[i256; 8]; 2] 0.i8 v1;
    v4.[[i256; 8]; 2] = insert_value v3 1.i8 v2;
    obj.store v0 v4;
    v5.objref<[i256; 8]> = obj.index v0 0.i8;
    v6.objref<[i256; 8]> = obj.index v0 1.i8;
    v7.[i256; 8] = obj.load v5;
    v8.i256 = call %disjoint v7 v6;
    return v8;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let object_effects = compute_object_effect_summaries(&module);
        let disjoint_ref = lookup_func(&module, "disjoint");
        let disjoint_summary = object_effects
            .get(&disjoint_ref)
            .expect("disjoint summary should exist");
        assert!(
            disjoint_summary.arg_effects[0].local_only
                && disjoint_summary.arg_effects[0].writes.is_empty(),
            "readonly by-value arg should stay share-eligible"
        );
        assert!(
            !disjoint_summary.arg_effects[1].writes.is_empty(),
            "sibling objref arg should record its write"
        );

        let caller_ref = lookup_func(&module, "caller");
        let local_object_args =
            collect_local_object_arg_info_with_effects(&module, &object_effects);
        let pass = ObjectByValueArgAbi::default();
        module.func_store.view(caller_ref, |func| {
            let facts = pass.collect_caller_elision_facts(
                func,
                None,
                &object_effects,
                local_object_args.get(&caller_ref),
            );
            let mut indexed = Vec::new();
            let mut loaded = None;
            let mut call_inst = None;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if let Some(obj_index) =
                        downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst))
                    {
                        indexed.push(
                            func.dfg
                                .inst_result(inst)
                                .expect("obj.index should have a result"),
                        );
                        assert!(
                            func.dfg
                                .value_ty(*obj_index.object())
                                .is_obj_ref(func.ctx()),
                            "obj.index base should stay an objref"
                        );
                    }
                    if let Some(obj_load) =
                        downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                        && func.dfg.value_ty(*obj_load.object()).is_obj_ref(func.ctx())
                    {
                        loaded = func.dfg.inst_result(inst);
                    }
                    if downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                        .is_some()
                    {
                        call_inst = Some(inst);
                    }
                }
            }
            let [src_obj, sibling_obj] = indexed.as_slice() else {
                panic!("expected exactly two obj.index values in caller");
            };
            let ParticipantLocation::Exact(_source_slice) =
                pass.participant_location(*src_obj, &facts)
            else {
                panic!("source projection should stay exact");
            };
            assert!(
                matches!(
                    pass.participant_location(*sibling_obj, &facts),
                    ParticipantLocation::Exact(_)
                ),
                "sibling projection should stay exact"
            );
            let loaded = loaded.expect("caller should load the projected slice");
            let call_inst = call_inst.expect("caller should contain a call");
            assert!(
                pass.direct_byval_source(
                    func,
                    call_inst,
                    loaded,
                    func.dfg.value_ty(*src_obj),
                    &facts
                )
                .is_some(),
                "projected load should remain a valid direct by-value source"
            );
        });
        let call_args = first_call_args(&module, "caller", "disjoint");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            1,
            "unexpected caller IR:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                !value_is_obj_alloc(func, call_args[0]) && !value_is_obj_alloc(func, call_args[1]),
                "disjoint sibling write should not force a copy:\n{dumped}"
            );
        });
    }

    #[test]
    fn borrowed_livein_arg_must_not_move_even_if_dead_after_call() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %mutate(v0.[i256; 8]) -> i256 {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v1 v0;
    v2.objref<i256> = obj.index v1 0.i8;
    obj.store v2 9.i256;
    v3.[i256; 8] = obj.load v1;
    v4.i256 = extract_value v3 0.i8;
    return v4;
}

func private %caller(v0.objref<[i256; 8]>) -> i256 {
block0:
    v1.[i256; 8] = obj.load v0;
    v2.i256 = call %mutate v1;
    return v2;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let call_args = first_call_args(&module, "caller", "mutate");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            1,
            "unexpected caller IR:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_obj_alloc(func, call_args[0]),
                "borrowed live-in root should not be movable:\n{dumped}"
            );
        });
    }

    #[test]
    fn readonly_borrowed_arg_can_share_without_copy() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %readonly(v0.[i256; 8]) -> i256 {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v1 v0;
    v2.[i256; 8] = obj.load v1;
    v3.i256 = extract_value v2 0.i8;
    return v3;
}

func private %caller(v0.objref<[i256; 8]>) -> i256 {
block0:
    v1.[i256; 8] = obj.load v0;
    v2.i256 = call %readonly v1;
    return v2;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let call_args = first_call_args(&module, "caller", "readonly");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            0,
            "readonly borrowed path should not copy:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_arg(func, call_args[0]),
                "readonly borrowed path should share the live-in objref:\n{dumped}"
            );
        });
    }

    #[test]
    fn projected_source_move_rejected_when_same_root_alias_escaped_before_call() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %escape(v0.objref<[i256; 8]>) -> objref<[i256; 8]> {
block0:
    return v0;
}

func private %mutate(v0.[i256; 8]) -> i256 {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v1 v0;
    v2.objref<i256> = obj.index v1 0.i8;
    obj.store v2 9.i256;
    v3.[i256; 8] = obj.load v1;
    v4.i256 = extract_value v3 0.i8;
    return v4;
}

func private %caller() -> i256 {
block0:
    v0.objref<[[i256; 8]; 2]> = obj.alloc [[i256; 8]; 2];
    v1.[i256; 8] = insert_value undef.[i256; 8] 0.i8 1.i256;
    v2.[[i256; 8]; 2] = insert_value undef.[[i256; 8]; 2] 0.i8 v1;
    obj.store v0 v2;
    v3.objref<[i256; 8]> = obj.index v0 0.i8;
    v4.objref<[i256; 8]> = obj.index v0 0.i8;
    v5.objref<[i256; 8]> = call %escape v4;
    v6.[i256; 8] = obj.load v3;
    v7.i256 = call %mutate v6;
    return v7;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let call_args = first_call_args(&module, "caller", "mutate");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            2,
            "escaped same-root alias should force a copy:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_obj_alloc(func, call_args[0]),
                "escaped sibling alias should block move:\n{dumped}"
            );
        });
    }

    #[test]
    fn move_rejected_when_live_out_holder_contains_nested_objref_alias() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @holder = { objref<[i256; 8]> };

func private %mutate(v0.[i256; 8]) -> i256 {
block0:
    v1.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v1 v0;
    v2.objref<i256> = obj.index v1 0.i8;
    obj.store v2 9.i256;
    v3.[i256; 8] = obj.load v1;
    v4.i256 = extract_value v3 0.i8;
    return v4;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.[i256; 8] = insert_value undef.[i256; 8] 0.i8 1.i256;
    obj.store v0 v1;
    v2.@holder = insert_value undef.@holder 0.i8 v0;
    v3.[i256; 8] = obj.load v0;
    v4.i256 = call %mutate v3;
    v5.objref<[i256; 8]> = extract_value v2 0.i8;
    v6.[i256; 8] = obj.load v5;
    v7.i256 = extract_value v6 0.i8;
    v8.i256 = add v4 v7;
    return v8;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let call_args = first_call_args(&module, "caller", "mutate");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            2,
            "live-out nested objref alias should force a copy:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_obj_alloc(func, call_args[0]),
                "nested live-out objref should block move:\n{dumped}"
            );
        });
    }

    #[test]
    fn readonly_copy_args_from_same_actual_reuse_one_temp() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @holder = { objref<[i256; 8]> };

func private %pair_read(v0.[i256; 8], v1.[i256; 8], v2.@holder) -> i256 {
block0:
    v3.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v3 v0;
    v4.[i256; 8] = obj.load v3;
    v5.i256 = extract_value v4 0.i8;
    v6.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v6 v1;
    v7.[i256; 8] = obj.load v6;
    v8.i256 = extract_value v7 1.i8;
    v9.i256 = add v5 v8;
    return v9;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.[i256; 8] = insert_value undef.[i256; 8] 1.i8 2.i256;
    obj.store v0 v1;
    v2.[i256; 8] = obj.load v0;
    v3.@holder = insert_value undef.@holder 0.i8 v0;
    v4.i256 = call %pair_read v2 v2 v3;
    return v4;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let source_root = first_obj_alloc_result(&module, "caller");
        let call_args = first_call_args(&module, "caller", "pair_read");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            2,
            "readonly copied args should reuse one temp:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                call_args[0] == call_args[1]
                    && value_is_obj_alloc(func, call_args[0])
                    && call_args[0] != source_root,
                "readonly copied args should reuse the same temp:\n{dumped}"
            );
        });
    }

    #[test]
    fn direct_aggregate_arg_with_nested_objref_forces_copy() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @holder = { objref<[i256; 8]> };

func private %mix(v0.[i256; 8], v1.@holder) -> i256 {
block0:
    v2.objref<[i256; 8]> = obj.alloc [i256; 8];
    obj.store v2 v0;
    v3.[i256; 8] = obj.load v2;
    v4.i256 = extract_value v3 0.i8;
    return v4;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 8]> = obj.alloc [i256; 8];
    v1.[i256; 8] = insert_value undef.[i256; 8] 0.i8 1.i256;
    obj.store v0 v1;
    v2.[i256; 8] = obj.load v0;
    v3.@holder = insert_value undef.@holder 0.i8 v0;
    v4.i256 = call %mix v2 v3;
    return v4;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let source_root = first_obj_alloc_result(&module, "caller");
        let call_args = first_call_args(&module, "caller", "mix");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            2,
            "unexpected caller IR:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_obj_alloc(func, call_args[0]) && call_args[0] != source_root,
                "nested objref direct aggregate should force a copy:\n{dumped}"
            );
        });
    }

    #[test]
    fn compile_large_byvalue_arrays_through_evm_pipeline() {
        let module = parse_test_module(include_str!(
            "../../../test_files/evm/fe_large_by_value_array_args.sntn"
        ));

        let backend = test_backend();
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        };
        compile_all_objects(&module, &backend, &opts).expect("compile should succeed");
        prepare_root(
            &module,
            &backend,
            lookup_func(&module, "__fe_contract_runtime_root_C"),
        )
        .expect("prepare should succeed");
    }
}
