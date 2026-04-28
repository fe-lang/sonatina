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
    LocalObjectArgInfo, ObjectEffectSummaryMap, ObjectMemoryAnalysis,
    abi::abi_leaf_count,
    collect_local_object_arg_info_with_effects, compute_object_effect_summaries,
    object_abi::{fresh_root_blocks_are_pairwise_unreachable, whole_object_slice},
    object_locality,
    object_tracking::{
        AggregateFacts, AggregateObjectFacts, ObjectSlice, TrackedObject,
        object_slice_overlaps_effect, slices_overlap,
    },
    private_abi::{self, PrivateAbiPlan},
    provenance::{
        CompleteProvenance, CompleteRootSet, ProvenanceFacts, ProvenanceSnapshot, RootValue,
    },
    shape,
};

#[derive(Clone, Copy)]
pub struct ObjectAggregateAbiConfig {
    pub inline_leaf_limit: usize,
    pub max_direct_arg_words: usize,
    pub max_direct_ret_words: usize,
}

impl Default for ObjectAggregateAbiConfig {
    fn default() -> Self {
        Self {
            inline_leaf_limit: 4,
            max_direct_arg_words: 16,
            max_direct_ret_words: 16,
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
struct RetPlan {
    original_ty: Type,
    direct_words: usize,
    kind: RetAbiKind,
    out_arg_ty: Option<Type>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RetAbiKind {
    Direct,
    OutObject,
}

#[derive(Clone)]
struct FuncPlan {
    hidden_out_tys: SmallVec<[Type; 4]>,
    args: Vec<ArgPlan>,
    rets: Vec<RetPlan>,
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
enum RetLowering {
    #[default]
    Temp,
    ForwardDest {
        dest_obj: ValueId,
        dest_slice: ObjectSlice,
        store_inst: InstId,
    },
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
    provenance: ProvenanceFacts,
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
struct ReturnCandidate {
    out_index: usize,
    effect: super::object_effects::ObjectArgEffect,
    dest_obj: ValueId,
    dest_slice: ObjectSlice,
    store_inst: InstId,
    leaf_count: usize,
}

#[derive(Clone)]
struct PlannerCandidate {
    key: PlannerCandidateKey,
    participant: CallParticipant,
    leaf_count: usize,
    modes: SmallVec<[PlannerMode; 3]>,
}

#[derive(Clone, Copy)]
enum PlannerCandidateKey {
    Arg(usize),
    Ret(usize),
}

#[derive(Clone, Copy)]
enum PlannerMode {
    Arg(ByValueArgLowering),
    Ret(RetLowering),
}

#[derive(Clone)]
struct CallParticipant {
    effect: super::object_effects::ObjectArgEffect,
    location: ParticipantLocation,
}

#[derive(Clone, Copy)]
struct FoldedReturnRoot {
    hidden_out_idx: usize,
    alloc_inst: InstId,
    root: ValueId,
}

struct ReturnRootRewriteCtx<'a> {
    root_slice: shape::AggregateSlice,
    root_slices: &'a FxHashMap<ValueId, shape::AggregateSlice>,
    provenance: CompleteProvenance<'a>,
    object_effects: &'a ObjectEffectSummaryMap,
    allowed_roots: &'a FxHashSet<ValueId>,
}

#[derive(Clone)]
struct ReturnCandidateRequest {
    out_index: usize,
    original_ty: Type,
    effect: super::object_effects::ObjectArgEffect,
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
pub struct ObjectAggregateAbi {
    cfg: ObjectAggregateAbiConfig,
}

pub type ObjectByValueArgAbi = ObjectAggregateAbi;
pub type ObjectByValueArgAbiConfig = ObjectAggregateAbiConfig;

impl ObjectAggregateAbi {
    pub fn new(cfg: ObjectAggregateAbiConfig) -> Self {
        Self { cfg }
    }

    pub fn run(&mut self, module: &Module) -> bool {
        self.run_with_synthetic_out_args(module)
            .expect("object aggregate ABI lowering should succeed")
            .iter()
            .any(|(_, args)| !args.is_empty())
    }

    pub(crate) fn run_with_synthetic_out_args(
        &mut self,
        module: &Module,
    ) -> Result<super::LocalObjectArgMap, String> {
        let mut synthetic_out_args =
            super::object_abi::ObjectReturnOutParam.run_with_synthetic_out_args(module);
        let mut plans = self.collect_plans(module)?;
        private_abi::retain_higher_order_safe_plans(module, &mut plans);
        if plans.is_empty() {
            return Ok(synthetic_out_args);
        }

        let original_object_effects = compute_object_effect_summaries(module);
        let old_sigs = private_abi::rewrite_declared_signatures(module, &plans);
        shift_synthetic_out_args(&mut synthetic_out_args, &plans);
        for (&func, plan) in &plans {
            let args = synthetic_out_args.entry(func).or_default();
            for idx in 0..plan.hidden_out_tys.len() {
                args.insert(
                    idx,
                    LocalObjectArgInfo {
                        init: super::RootInit::UndefFresh,
                        fresh_result_out: true,
                    },
                );
            }
        }

        for (&func, plan) in &plans {
            module.func_store.modify(func, |function| {
                self.rewrite_function(function, plan, &original_object_effects);
                function.rebuild_users();
            });
        }

        let object_effects = compute_object_effect_summaries(module);
        let mut local_object_args =
            collect_local_object_arg_info_with_effects(module, &object_effects);
        super::merge_local_object_arg_info(&mut local_object_args, &synthetic_out_args);

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
        Ok(synthetic_out_args)
    }

    fn collect_plans(&self, module: &Module) -> Result<FxHashMap<FuncRef, FuncPlan>, String> {
        let mut plans = FxHashMap::default();

        for func in module.funcs() {
            let Some(sig) = module.ctx.get_sig(func) else {
                continue;
            };
            if !private_abi::is_owned_private_abi_func(&sig) {
                continue;
            }

            let mut rets: Vec<_> = sig
                .ret_tys()
                .iter()
                .copied()
                .map(|ty| self.initial_ret_plan(&module.ctx, ty))
                .collect();
            let mut total_direct_ret_words = rets
                .iter()
                .filter(|ret| ret.kind == RetAbiKind::Direct)
                .map(|ret| ret.direct_words)
                .sum::<usize>();
            if total_direct_ret_words > self.cfg.max_direct_ret_words {
                let mut rewrite_order: Vec<_> = rets
                    .iter()
                    .enumerate()
                    .filter(|(_, ret)| {
                        ret.kind == RetAbiKind::Direct && self.can_rewrite_ret_as_object(ret)
                    })
                    .map(|(idx, ret)| (idx, ret.direct_words))
                    .collect();
                rewrite_order.sort_unstable_by_key(|&(idx, savings)| (Reverse(savings), idx));
                for (idx, savings) in rewrite_order {
                    if total_direct_ret_words <= self.cfg.max_direct_ret_words {
                        break;
                    }
                    rets[idx].kind = RetAbiKind::OutObject;
                    rets[idx].out_arg_ty = Some(objref_ty(&module.ctx, rets[idx].original_ty));
                    total_direct_ret_words -= savings;
                }
            }
            if total_direct_ret_words > self.cfg.max_direct_ret_words {
                return Err(format!(
                    "cannot lower {} for EVM: {} direct return words remain after rewriting all eligible aggregate returns",
                    sig.name(),
                    total_direct_ret_words
                ));
            }

            let hidden_out_tys: SmallVec<[Type; 4]> = rets
                .iter()
                .filter_map(|ret| {
                    (ret.kind == RetAbiKind::OutObject)
                        .then_some(ret.out_arg_ty)
                        .flatten()
                })
                .collect();
            let mut args: Vec<_> = sig
                .args()
                .iter()
                .copied()
                .map(|ty| self.initial_arg_plan(&module.ctx, ty))
                .collect();
            let mut total_direct_words = hidden_out_tys.len()
                + args
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
                return Err(format!(
                    "cannot lower {} for EVM: aggregate returns require {} hidden out parameters, leaving {} direct call operands",
                    sig.name(),
                    hidden_out_tys.len(),
                    total_direct_words
                ));
            }

            if hidden_out_tys.is_empty()
                && !args.iter().any(|arg| arg.kind == ArgAbiKind::ByValueObject)
            {
                continue;
            }

            let new_arg_tys = hidden_out_tys
                .iter()
                .copied()
                .chain(args.iter().map(|arg| arg.new_ty))
                .collect();
            let new_ret_tys = rets
                .iter()
                .filter(|ret| ret.kind == RetAbiKind::Direct)
                .map(|ret| ret.original_ty)
                .collect();
            plans.insert(
                func,
                FuncPlan {
                    hidden_out_tys,
                    args,
                    rets,
                    new_arg_tys,
                    new_ret_tys,
                },
            );
        }

        Ok(plans)
    }

    fn initial_ret_plan(&self, ctx: &ModuleCtx, ty: Type) -> RetPlan {
        let direct_words = direct_word_count(ctx, ty).unwrap_or(1);
        let kind = if direct_words <= 1
            || shape::runtime_size_bytes(ctx, ty).is_some_and(|size| size == 0)
            || !shape::is_supported_aggregate_ty(ctx, ty)
            || direct_words <= self.cfg.inline_leaf_limit
        {
            RetAbiKind::Direct
        } else {
            RetAbiKind::OutObject
        };
        RetPlan {
            original_ty: ty,
            direct_words,
            kind,
            out_arg_ty: (kind == RetAbiKind::OutObject).then(|| objref_ty(ctx, ty)),
        }
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

    fn can_rewrite_ret_as_object(&self, ret: &RetPlan) -> bool {
        ret.direct_words > 1 && ret.out_arg_ty.is_some()
    }

    fn direct_abi_words(&self, arg: &ArgPlan) -> usize {
        match arg.kind {
            ArgAbiKind::Direct => arg.direct_words,
            ArgAbiKind::ByValueObject => 1,
        }
    }

    fn rewrite_function(
        &self,
        function: &mut Function,
        plan: &FuncPlan,
        object_effects: &ObjectEffectSummaryMap,
    ) {
        let old_args = function.arg_values.clone();
        let mut new_args = SmallVec::with_capacity(plan.hidden_out_tys.len() + old_args.len());
        let mut rewritten = SmallVec::<[RewrittenArg; 4]>::new();

        for &out_ty in &plan.hidden_out_tys {
            let idx = new_args.len();
            new_args.push(function.dfg.make_value(Value::Arg { ty: out_ty, idx }));
        }
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
        self.try_fold_return_roots(function, plan, object_effects);
        self.rewrite_returns(function, plan);
    }

    fn try_fold_return_roots(
        &self,
        function: &mut Function,
        plan: &FuncPlan,
        object_effects: &ObjectEffectSummaryMap,
    ) {
        let mut used_roots = FxHashSet::default();
        let mut folded = SmallVec::<[FoldedReturnRoot; 4]>::new();
        let mut hidden_out_idx = 0usize;
        let mut layout_cache = shape::AggregateLayoutCache::default();
        let mut snapshot = ProvenanceSnapshot::new(function, Some(object_effects));
        for (ret_idx, ret_plan) in plan.rets.iter().enumerate() {
            if ret_plan.kind != RetAbiKind::OutObject {
                continue;
            }
            let Some(roots) = self.collect_foldable_return_roots(
                function,
                plan,
                ret_idx,
                hidden_out_idx,
                object_effects,
                (&mut layout_cache, &mut snapshot),
            ) else {
                hidden_out_idx += 1;
                continue;
            };
            if roots.iter().any(|root| used_roots.contains(&root.root)) {
                hidden_out_idx += 1;
                continue;
            }
            used_roots.extend(roots.iter().map(|root| root.root));
            folded.extend(roots);
            hidden_out_idx += 1;
        }

        for root in folded {
            function
                .dfg
                .change_to_alias(root.root, function.arg_values[root.hidden_out_idx]);
            function.layout.remove_inst(root.alloc_inst);
            function.erase_inst(root.alloc_inst);
        }
    }

    fn collect_foldable_return_roots(
        &self,
        function: &Function,
        plan: &FuncPlan,
        ret_idx: usize,
        hidden_out_idx: usize,
        object_effects: &ObjectEffectSummaryMap,
        analysis: (
            &mut shape::AggregateLayoutCache,
            &mut ProvenanceSnapshot<'_>,
        ),
    ) -> Option<SmallVec<[FoldedReturnRoot; 4]>> {
        let (layout_cache, snapshot) = analysis;
        let ret_ty = plan.rets[ret_idx].original_ty;
        let root_slice = whole_object_slice(layout_cache, function.ctx(), ret_ty);
        let root_slices = self.collect_return_root_slices(function, ret_ty, root_slice);
        if root_slices.is_empty() {
            return None;
        }
        let facts = AggregateFacts::from_root_slices(
            function,
            function.ctx(),
            root_slices,
            layout_cache,
            snapshot,
        );
        let complete_provenance = facts.complete();
        let mut roots = SmallVec::<[ValueId; 4]>::new();
        let mut seen = FxHashSet::default();
        let mut saw_return = false;
        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let Some(ret) =
                    downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(inst))
                else {
                    continue;
                };
                saw_return = true;
                let &value = ret.args().as_slice().get(ret_idx)?;
                for root in self.returned_whole_roots(
                    function,
                    value,
                    root_slice,
                    facts.root_slices(),
                    complete_provenance,
                )? {
                    if seen.insert(root) {
                        roots.push(root);
                    }
                }
            }
        }
        if !saw_return
            || roots.is_empty()
            || !fresh_root_blocks_are_pairwise_unreachable(function, &roots)
        {
            return None;
        }

        roots.sort_unstable_by_key(|root| root.as_u32());
        let allowed_roots: FxHashSet<_> = roots.iter().copied().collect();
        let rewrite_ctx = ReturnRootRewriteCtx {
            root_slice,
            root_slices: facts.root_slices(),
            provenance: complete_provenance,
            object_effects,
            allowed_roots: &allowed_roots,
        };
        let mut folded = SmallVec::with_capacity(roots.len());
        for root in roots {
            let alloc_inst = function.dfg.value_inst(root)?;
            let obj_alloc =
                downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(alloc_inst))?;
            if *obj_alloc.ty() != ret_ty
                || !function.layout.is_inst_inserted(alloc_inst)
                || !self.return_root_is_rewritable(function, root, &rewrite_ctx)
            {
                return None;
            }
            folded.push(FoldedReturnRoot {
                hidden_out_idx,
                alloc_inst,
                root,
            });
        }
        Some(folded)
    }

    fn collect_return_root_slices(
        &self,
        function: &Function,
        ret_ty: Type,
        root_slice: shape::AggregateSlice,
    ) -> FxHashMap<ValueId, shape::AggregateSlice> {
        let mut root_slices = FxHashMap::default();
        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let Some(obj_alloc) =
                    downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(inst))
                else {
                    continue;
                };
                let Some(result) = function.dfg.inst_result(inst) else {
                    continue;
                };
                if *obj_alloc.ty() == ret_ty {
                    root_slices.insert(result, root_slice);
                }
            }
        }
        root_slices
    }

    fn returned_whole_roots(
        &self,
        function: &Function,
        value: ValueId,
        root_slice: shape::AggregateSlice,
        root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
        provenance: CompleteProvenance<'_>,
    ) -> Option<SmallVec<[ValueId; 4]>> {
        if let Some(load_inst) = function.dfg.value_inst(value)
            && let Some(obj_load) =
                downcast::<&data::ObjLoad>(function.inst_set(), function.dfg.inst(load_inst))
            && root_slices.get(obj_load.object()) == Some(&root_slice)
        {
            return Some(smallvec::smallvec![*obj_load.object()]);
        }
        if let Some(projection) = provenance.exact_projection(value) {
            return (root_slices.get(&projection.root_value.value()) == Some(&projection.slice)
                && projection.slice == root_slice)
                .then_some(smallvec::smallvec![projection.root_value.value()]);
        }

        match provenance.complete_roots(value)? {
            CompleteRootSet::Single(root) => (root_slices.get(&root.value()) == Some(&root_slice))
                .then_some(smallvec::smallvec![root.value()]),
            CompleteRootSet::Multiple(roots) => {
                let mut returned_roots = SmallVec::<[ValueId; 4]>::new();
                for root in roots.iter() {
                    if root_slices.get(&root.value()) != Some(&root_slice) {
                        return None;
                    }
                    returned_roots.push(root.value());
                }
                returned_roots.sort_unstable_by_key(|root| root.as_u32());
                (!returned_roots.is_empty()).then_some(returned_roots)
            }
        }
    }

    fn return_root_is_rewritable(
        &self,
        function: &Function,
        root: ValueId,
        rewrite_ctx: &ReturnRootRewriteCtx<'_>,
    ) -> bool {
        object_locality::object_root_stays_local_with_effects(
            function,
            root,
            function.dfg.value_ty(root),
            rewrite_ctx.object_effects,
            |value| self.return_root_value_is_allowed(function, value, root, rewrite_ctx),
            true,
        )
    }

    fn return_root_value_is_allowed(
        &self,
        function: &Function,
        value: ValueId,
        root: ValueId,
        rewrite_ctx: &ReturnRootRewriteCtx<'_>,
    ) -> bool {
        if rewrite_ctx
            .provenance
            .exact_projection(value)
            .is_some_and(|projection| {
                projection.root_value == RootValue::new(root)
                    && projection.slice == rewrite_ctx.root_slice
            })
        {
            return true;
        }
        if function.dfg.value_ty(value) != function.dfg.value_ty(root)
            || rewrite_ctx.root_slices.get(&root) != Some(&rewrite_ctx.root_slice)
        {
            return false;
        }
        match rewrite_ctx.provenance.complete_roots(value) {
            Some(CompleteRootSet::Single(provenance_root)) => {
                provenance_root == RootValue::new(root)
            }
            Some(CompleteRootSet::Multiple(roots)) => {
                roots.contains(RootValue::new(root))
                    && roots
                        .iter()
                        .all(|candidate| rewrite_ctx.allowed_roots.contains(&candidate.value()))
            }
            None => false,
        }
    }

    fn rewrite_returns(&self, function: &mut Function, plan: &FuncPlan) {
        if plan.hidden_out_tys.is_empty() {
            return;
        }
        let local_object_args = hidden_out_local_object_args(plan.hidden_out_tys.len());
        let mut object_memory = ObjectMemoryAnalysis::default();
        object_memory.compute_with_loaded_value_carriers(function, Some(&local_object_args), None);
        let blocks: Vec<_> = function.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = function.layout.iter_inst(block).collect();
            for inst in insts {
                let Some(ret) =
                    downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(inst))
                        .cloned()
                else {
                    continue;
                };
                self.rewrite_return(function, inst, &ret, plan, &object_memory);
            }
        }
    }

    fn rewrite_return(
        &self,
        function: &mut Function,
        inst: InstId,
        ret: &control_flow::Return,
        plan: &FuncPlan,
        object_memory: &ObjectMemoryAnalysis,
    ) {
        let loc = function.layout.prev_inst_of(inst).map_or(
            CursorLocation::BlockTop(function.layout.inst_block(inst)),
            CursorLocation::At,
        );
        let mut cursor = InstInserter::at_location(loc);
        let mut direct_returns = SmallVec::<[ValueId; 2]>::new();
        let mut hidden_out_idx = 0usize;

        for (ret_idx, ret_plan) in plan.rets.iter().enumerate() {
            let Some(&value) = ret.args().as_slice().get(ret_idx) else {
                break;
            };
            match ret_plan.kind {
                RetAbiKind::Direct => direct_returns.push(value),
                RetAbiKind::OutObject => {
                    let out_arg = function.arg_values[hidden_out_idx];
                    hidden_out_idx += 1;
                    let total_leaves =
                        direct_word_count(function.ctx(), ret_plan.original_ty).unwrap_or(1);
                    if !object_memory.value_matches_current_object_slice_before_inst(
                        inst,
                        value,
                        ObjectSlice {
                            root: out_arg,
                            ty: ret_plan.original_ty,
                            first_leaf: 0,
                            leaf_count: total_leaves,
                            total_leaves,
                        },
                    ) {
                        cursor.insert_inst_data(
                            function,
                            data::ObjStore::new_unchecked(function.inst_set(), out_arg, value),
                        );
                    }
                }
            }
        }

        let return_inst = function
            .inst_set()
            .has_return()
            .expect("target ISA must support `return`");
        function.dfg.replace_inst(
            inst,
            Box::new(control_flow::Return::new(
                return_inst,
                direct_returns.into(),
            )),
        );
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
                let facts = self.collect_caller_elision_facts(
                    function,
                    current_plan,
                    object_effects,
                    local_object_args,
                );
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
        let mut snapshot = ProvenanceSnapshot::new(function, Some(object_effects));
        let facts =
            AggregateObjectFacts::for_call_planner(function, &mut layout_cache, &mut snapshot);
        let root_total_leaves = facts
            .root_slices()
            .iter()
            .map(|(&root, slice)| (root, slice.leaf_count))
            .collect();
        let mut object_memory = ObjectMemoryAnalysis::default();
        object_memory.compute_with_facts(
            function,
            local_object_args,
            Some(object_effects),
            &facts,
            true,
        );
        let (provenance, tracked) = facts.into_provenance_and_tracked();

        CallerElisionFacts {
            inst_liveness,
            provenance,
            tracked,
            object_memory,
            local_object_args: local_object_args.cloned(),
            owned_byvalue_args: current_plan
                .map(|plan| {
                    let mut arg_idx = plan.hidden_out_tys.len();
                    plan.args
                        .iter()
                        .filter_map(|arg| {
                            let current_idx = arg_idx;
                            arg_idx += 1;
                            (arg.kind == ArgAbiKind::ByValueObject).then_some(current_idx)
                        })
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
        let (arg_lowerings, ret_lowerings) =
            self.plan_call_lowerings(function, inst, call, plan, object_effects, facts);
        let summary = object_effects.get(call.callee());
        let loc = function.layout.prev_inst_of(inst).map_or(
            CursorLocation::BlockTop(function.layout.inst_block(inst)),
            CursorLocation::At,
        );
        let mut pre_call = InstInserter::at_location(loc);
        let mut new_args = SmallVec::<[ValueId; 8]>::new();
        let mut readonly_copy_cache = FxHashMap::<ValueId, ValueId>::default();
        let old_results = function.dfg.inst_results(inst).to_vec();
        let mut out_roots = SmallVec::<[ValueId; 4]>::new();

        for (&out_ty, &lowering) in plan.hidden_out_tys.iter().zip(&ret_lowerings) {
            match lowering {
                RetLowering::Temp => {
                    let alloc_inst = pre_call.insert_inst_data(
                        function,
                        data::ObjAlloc::new_unchecked(
                            function.inst_set(),
                            objref_element_ty(function.ctx(), out_ty)
                                .expect("hidden out arg should be objref"),
                        ),
                    );
                    let object = pre_call.make_result(function, alloc_inst, out_ty);
                    pre_call.attach_result(function, alloc_inst, object);
                    pre_call.set_location(CursorLocation::At(alloc_inst));
                    out_roots.push(object);
                    new_args.push(object);
                }
                RetLowering::ForwardDest { dest_obj, .. } => {
                    out_roots.push(dest_obj);
                    new_args.push(dest_obj);
                }
            }
        }

        for (idx, (&arg, arg_plan)) in call.args().iter().zip(&plan.args).enumerate() {
            match arg_plan.kind {
                ArgAbiKind::Direct => new_args.push(arg),
                ArgAbiKind::ByValueObject => match arg_lowerings[idx] {
                    ByValueArgLowering::Copy => {
                        let can_reuse_copy = summary
                            .and_then(|summary| {
                                summary.arg_effects.get(plan.hidden_out_tys.len() + idx)
                            })
                            .is_some_and(|effect| effect.writes.is_empty() && effect.local_only);
                        if can_reuse_copy && let Some(&cached_copy) = readonly_copy_cache.get(&arg)
                        {
                            new_args.push(cached_copy);
                            continue;
                        }
                        let alloc_inst = pre_call.insert_inst_data(
                            function,
                            data::ObjAlloc::new_unchecked(
                                function.inst_set(),
                                arg_plan.original_ty,
                            ),
                        );
                        let object = pre_call.make_result(function, alloc_inst, arg_plan.new_ty);
                        pre_call.attach_result(function, alloc_inst, object);
                        pre_call.set_location(CursorLocation::At(alloc_inst));
                        let store_inst = pre_call.insert_inst_data(
                            function,
                            data::ObjStore::new_unchecked(function.inst_set(), object, arg),
                        );
                        pre_call.set_location(CursorLocation::At(store_inst));
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

        let new_call = pre_call.insert_inst_data(
            function,
            control_flow::Call::new(
                function
                    .inst_set()
                    .has_call()
                    .expect("target ISA must support `call`"),
                *call.callee(),
                new_args,
            ),
        );
        let direct_ret_tys: SmallVec<[Type; 4]> = plan
            .rets
            .iter()
            .filter(|ret| ret.kind == RetAbiKind::Direct)
            .map(|ret| ret.original_ty)
            .collect();
        let mut new_direct_results = SmallVec::<[ValueId; 4]>::new();
        for (idx, &ty) in direct_ret_tys.iter().enumerate() {
            let result = function.dfg.make_value(Value::Inst {
                inst: new_call,
                result_idx: idx as u16,
                ty,
            });
            pre_call.attach_result(function, new_call, result);
            new_direct_results.push(result);
        }

        let mut post_call = InstInserter::at_location(CursorLocation::At(new_call));
        let mut direct_idx = 0usize;
        let mut out_idx = 0usize;
        for (&old_result, ret_plan) in old_results.iter().zip(&plan.rets) {
            match ret_plan.kind {
                RetAbiKind::Direct => {
                    function
                        .dfg
                        .change_to_alias(old_result, new_direct_results[direct_idx]);
                    direct_idx += 1;
                }
                RetAbiKind::OutObject => {
                    let out_root = out_roots[out_idx];
                    let ret_lowering = ret_lowerings[out_idx];
                    let remaining_users = function
                        .dfg
                        .users(old_result)
                        .filter(|&&user| {
                            !matches!(
                                ret_lowering,
                                RetLowering::ForwardDest { store_inst, .. } if user == store_inst
                            )
                        })
                        .count();
                    out_idx += 1;
                    if let RetLowering::ForwardDest { store_inst, .. } = ret_lowering {
                        function.layout.remove_inst(store_inst);
                        function.erase_inst(store_inst);
                    }
                    if remaining_users == 0 {
                        function.dfg.values[old_result] = Value::Undef {
                            ty: ret_plan.original_ty,
                        };
                        continue;
                    }
                    let load_inst = post_call.insert_inst_data(
                        function,
                        data::ObjLoad::new_unchecked(function.inst_set(), out_root),
                    );
                    let loaded = post_call.make_result(function, load_inst, ret_plan.original_ty);
                    post_call.attach_result(function, load_inst, loaded);
                    post_call.set_location(CursorLocation::At(load_inst));
                    function.dfg.change_to_alias(old_result, loaded);
                }
            }
        }

        function.layout.remove_inst(inst);
        function.erase_inst(inst);
    }

    fn plan_call_lowerings(
        &self,
        function: &Function,
        inst: InstId,
        call: &control_flow::Call,
        plan: &FuncPlan,
        object_effects: &ObjectEffectSummaryMap,
        facts: &CallerElisionFacts,
    ) -> (Vec<ByValueArgLowering>, Vec<RetLowering>) {
        let mut arg_lowerings = vec![ByValueArgLowering::Copy; plan.args.len()];
        let mut ret_lowerings = vec![RetLowering::Temp; plan.hidden_out_tys.len()];
        let Some(summary) = object_effects.get(call.callee()) else {
            return (arg_lowerings, ret_lowerings);
        };
        if self.call_has_indirect_objref_arg(function, call, plan) {
            return (arg_lowerings, ret_lowerings);
        }

        let fixed = self.collect_fixed_participants(function, call, plan, summary, facts);
        let candidates =
            self.collect_byvalue_candidates(function, inst, call, plan, object_effects, facts);
        let return_candidates =
            self.collect_return_candidates(function, inst, plan, summary, facts);
        let chosen = self.choose_candidate_lowerings(&candidates, &return_candidates, &fixed);
        for (candidate, mode) in chosen {
            match (candidate, mode) {
                (PlannerCandidateKey::Arg(arg_index), PlannerMode::Arg(lowering)) => {
                    arg_lowerings[arg_index] = lowering;
                }
                (PlannerCandidateKey::Ret(out_index), PlannerMode::Ret(lowering)) => {
                    ret_lowerings[out_index] = lowering;
                }
                _ => {}
            }
        }
        (arg_lowerings, ret_lowerings)
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
            let Some(effect) = summary
                .arg_effects
                .get(plan.hidden_out_tys.len() + idx)
                .cloned()
            else {
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
            let Some(effect) = summary
                .arg_effects
                .get(plan.hidden_out_tys.len() + idx)
                .cloned()
            else {
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

    fn collect_return_candidates(
        &self,
        function: &Function,
        inst: InstId,
        plan: &FuncPlan,
        summary: &super::object_effects::ObjectEffectSummary,
        facts: &CallerElisionFacts,
    ) -> Vec<ReturnCandidate> {
        let mut candidates = Vec::new();
        let old_results = function.dfg.inst_results(inst).to_vec();
        let mut out_idx = 0usize;
        for (&old_result, ret_plan) in old_results.iter().zip(&plan.rets) {
            if ret_plan.kind != RetAbiKind::OutObject {
                continue;
            }
            let candidate = summary
                .arg_effects
                .get(out_idx)
                .cloned()
                .and_then(|effect| {
                    self.forwarded_return_candidate(
                        function,
                        inst,
                        old_result,
                        ReturnCandidateRequest {
                            out_index: out_idx,
                            original_ty: ret_plan.original_ty,
                            effect,
                        },
                        facts,
                    )
                });
            if let Some(candidate) = candidate {
                candidates.push(candidate);
            }
            out_idx += 1;
        }
        candidates
    }

    fn forwarded_return_candidate(
        &self,
        function: &Function,
        inst: InstId,
        old_result: ValueId,
        request: ReturnCandidateRequest,
        facts: &CallerElisionFacts,
    ) -> Option<ReturnCandidate> {
        let store_inst = function.layout.next_inst_of(inst)?;
        if function.layout.inst_block(store_inst) != function.layout.inst_block(inst) {
            return None;
        }
        let store =
            downcast::<&data::ObjStore>(function.inst_set(), function.dfg.inst(store_inst))?;
        if *store.value() != old_result {
            return None;
        }
        let dest_obj = *store.object();
        if function.dfg.value_ty(dest_obj) != objref_ty(function.ctx(), request.original_ty) {
            return None;
        }
        let dest_slice = facts.tracked[dest_obj].and_then(TrackedObject::exact)?;
        if dest_slice.ty != request.original_ty
            || dest_slice.leaf_count != direct_word_count(function.ctx(), request.original_ty)?
        {
            return None;
        }
        let whole_store_count = function
            .dfg
            .users(old_result)
            .filter(|&&user| {
                downcast::<&data::ObjStore>(function.inst_set(), function.dfg.inst(user))
                    .is_some_and(|candidate_store| *candidate_store.value() == old_result)
            })
            .count();
        if whole_store_count != 1 {
            return None;
        }
        Some(ReturnCandidate {
            out_index: request.out_index,
            effect: request.effect,
            dest_obj,
            dest_slice,
            store_inst,
            leaf_count: dest_slice.leaf_count,
        })
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

        match facts.provenance.complete().exact_projection(value) {
            Some(projection) => facts
                .root_total_leaves
                .get(&projection.root_value.value())
                .copied()
                .map_or(
                    ParticipantLocation::RootUnknown {
                        root: projection.root_value.value(),
                    },
                    |total_leaves| {
                        ParticipantLocation::Exact(ObjectSlice {
                            root: projection.root_value.value(),
                            ty: projection.slice.ty,
                            first_leaf: projection.slice.first_leaf,
                            leaf_count: projection.slice.leaf_count,
                            total_leaves,
                        })
                    },
                ),
            None => match facts.provenance.complete().complete_roots(value) {
                Some(CompleteRootSet::Single(root)) => {
                    ParticipantLocation::RootUnknown { root: root.value() }
                }
                Some(CompleteRootSet::Multiple(roots)) => {
                    ParticipantLocation::MaybeRoots(roots.iter().map(RootValue::value).collect())
                }
                None => ParticipantLocation::Unknown,
            },
        }
    }

    fn choose_candidate_lowerings(
        &self,
        byvalue_candidates: &[ByValueCandidate],
        return_candidates: &[ReturnCandidate],
        fixed: &[CallParticipant],
    ) -> Vec<(PlannerCandidateKey, PlannerMode)> {
        let candidates = self.planner_candidates(byvalue_candidates, return_candidates);
        if candidates.len() <= 8 {
            self.choose_candidate_lowerings_exhaustive(&candidates, fixed)
        } else {
            self.choose_candidate_lowerings_greedy(&candidates, fixed)
        }
    }

    fn planner_candidates(
        &self,
        byvalue_candidates: &[ByValueCandidate],
        return_candidates: &[ReturnCandidate],
    ) -> Vec<PlannerCandidate> {
        byvalue_candidates
            .iter()
            .map(|candidate| PlannerCandidate {
                key: PlannerCandidateKey::Arg(candidate.arg_index),
                participant: candidate.participant(),
                leaf_count: candidate.leaf_count,
                modes: self
                    .candidate_modes(candidate)
                    .into_iter()
                    .map(PlannerMode::Arg)
                    .collect(),
            })
            .chain(return_candidates.iter().map(|candidate| PlannerCandidate {
                key: PlannerCandidateKey::Ret(candidate.out_index),
                participant: candidate.participant(),
                leaf_count: candidate.leaf_count,
                modes: smallvec::smallvec![
                    PlannerMode::Ret(RetLowering::ForwardDest {
                        dest_obj: candidate.dest_obj,
                        dest_slice: candidate.dest_slice,
                        store_inst: candidate.store_inst,
                    }),
                    PlannerMode::Ret(RetLowering::Temp),
                ],
            }))
            .collect()
    }

    fn choose_candidate_lowerings_exhaustive(
        &self,
        candidates: &[PlannerCandidate],
        fixed: &[CallParticipant],
    ) -> Vec<(PlannerCandidateKey, PlannerMode)> {
        let mut best: Vec<_> = candidates
            .iter()
            .map(PlannerCandidate::default_mode)
            .collect();
        let mut best_score = Score::default();
        let mut current = best.clone();
        self.search_candidate_lowerings(
            candidates,
            fixed,
            0,
            &mut current,
            &mut best,
            &mut best_score,
        );
        candidates
            .iter()
            .zip(best)
            .map(|(candidate, mode)| (candidate.key, mode))
            .collect()
    }

    fn search_candidate_lowerings(
        &self,
        candidates: &[PlannerCandidate],
        fixed: &[CallParticipant],
        idx: usize,
        current: &mut [PlannerMode],
        best: &mut Vec<PlannerMode>,
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

        for &mode in &candidates[idx].modes {
            if !self.lowering_is_compatible(candidates, fixed, current, idx, mode) {
                continue;
            }
            current[idx] = mode;
            self.search_candidate_lowerings(candidates, fixed, idx + 1, current, best, best_score);
        }
        current[idx] = candidates[idx].default_mode();
    }

    fn choose_candidate_lowerings_greedy(
        &self,
        candidates: &[PlannerCandidate],
        fixed: &[CallParticipant],
    ) -> Vec<(PlannerCandidateKey, PlannerMode)> {
        let mut chosen: Vec<_> = candidates
            .iter()
            .map(PlannerCandidate::default_mode)
            .collect();
        let mut order: Vec<_> = (0..candidates.len()).collect();
        order.sort_unstable_by_key(|&idx| (Reverse(candidates[idx].leaf_count), idx));
        for idx in order {
            for &mode in &candidates[idx].modes {
                if self.lowering_is_compatible(candidates, fixed, &chosen, idx, mode) {
                    chosen[idx] = mode;
                    break;
                }
            }
        }
        candidates
            .iter()
            .zip(chosen)
            .map(|(candidate, mode)| (candidate.key, mode))
            .collect()
    }

    fn score_candidate_lowerings(
        &self,
        candidates: &[PlannerCandidate],
        lowerings: &[PlannerMode],
    ) -> Score {
        let mut score = Score::default();
        for (candidate, lowering) in candidates.iter().zip(lowerings) {
            match lowering {
                PlannerMode::Arg(ByValueArgLowering::Copy)
                | PlannerMode::Ret(RetLowering::Temp) => {}
                PlannerMode::Arg(ByValueArgLowering::Share { .. }) => {
                    score.avoided_leaves += candidate.leaf_count;
                    score.avoided_args += 1;
                    score.share_count += 1;
                }
                PlannerMode::Arg(ByValueArgLowering::Move { .. })
                | PlannerMode::Ret(RetLowering::ForwardDest { .. }) => {
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
        candidates: &[PlannerCandidate],
        fixed: &[CallParticipant],
        current: &[PlannerMode],
        new_idx: usize,
        new_mode: PlannerMode,
    ) -> bool {
        let Some(new_source_slice) = new_mode.slice() else {
            return true;
        };
        let new_participant = &candidates[new_idx].participant;

        if fixed
            .iter()
            .any(|participant| self.lowering_conflicts(new_mode, new_source_slice, participant))
        {
            return false;
        }

        for (other_idx, &other_mode) in current.iter().enumerate() {
            if other_idx == new_idx || other_mode.is_default() {
                continue;
            }
            let Some(other_source_slice) = other_mode.slice() else {
                continue;
            };
            let other_participant = &candidates[other_idx].participant;
            if self.lowering_conflicts(new_mode, new_source_slice, other_participant)
                || self.lowering_conflicts(other_mode, other_source_slice, new_participant)
            {
                return false;
            }
        }

        true
    }

    fn lowering_conflicts(
        &self,
        lowering: PlannerMode,
        source_slice: ObjectSlice,
        participant: &CallParticipant,
    ) -> bool {
        match lowering {
            PlannerMode::Arg(ByValueArgLowering::Copy) | PlannerMode::Ret(RetLowering::Temp) => {
                false
            }
            PlannerMode::Arg(ByValueArgLowering::Share { .. }) => {
                participant.location.may_overlap(source_slice)
                    && effect_may_overlap_slice(
                        source_slice,
                        &participant.location,
                        &participant.effect.writes,
                    )
            }
            PlannerMode::Arg(ByValueArgLowering::Move { .. })
            | PlannerMode::Ret(RetLowering::ForwardDest { .. }) => {
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

impl ReturnCandidate {
    fn participant(&self) -> CallParticipant {
        CallParticipant {
            effect: self.effect.clone(),
            location: ParticipantLocation::Exact(self.dest_slice),
        }
    }
}

impl PlannerCandidate {
    fn default_mode(&self) -> PlannerMode {
        self.modes
            .iter()
            .copied()
            .find(|mode| mode.is_default())
            .unwrap_or(self.modes[0])
    }
}

impl PlannerMode {
    fn is_default(self) -> bool {
        matches!(
            self,
            Self::Arg(ByValueArgLowering::Copy) | Self::Ret(RetLowering::Temp)
        )
    }

    fn slice(self) -> Option<ObjectSlice> {
        match self {
            Self::Arg(lowering) => lowering.source_slice(),
            Self::Ret(RetLowering::Temp) => None,
            Self::Ret(RetLowering::ForwardDest { dest_slice, .. }) => Some(dest_slice),
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

fn shift_synthetic_out_args(
    synthetic_out_args: &mut super::LocalObjectArgMap,
    plans: &FxHashMap<FuncRef, FuncPlan>,
) {
    for (&func, plan) in plans {
        let shift = plan.hidden_out_tys.len();
        if shift == 0 {
            continue;
        }
        let Some(args) = synthetic_out_args.get_mut(&func) else {
            continue;
        };
        let shifted: FxHashMap<_, _> = std::mem::take(args)
            .into_iter()
            .map(|(idx, info)| (idx + shift, info))
            .collect();
        *args = shifted;
    }
}

fn hidden_out_local_object_args(count: usize) -> FxHashMap<usize, LocalObjectArgInfo> {
    (0..count)
        .map(|idx| {
            (
                idx,
                LocalObjectArgInfo {
                    init: super::RootInit::UndefFresh,
                    fresh_result_out: true,
                },
            )
        })
        .collect()
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
        let _ = run_object_aggregate_abi(module);
    }

    fn run_object_aggregate_abi(module: &Module) -> crate::transform::aggregate::LocalObjectArgMap {
        let mut pass = ObjectAggregateAbi::default();
        let synthetic_out_args = pass
            .run_with_synthetic_out_args(module)
            .expect("object aggregate ABI lowering should succeed");
        let report = verify_module(
            module,
            &VerifierConfig::for_level(VerificationLevel::Standard),
        );
        assert!(
            !report.has_errors(),
            "module should verify after rewrite:\n{report}"
        );
        synthetic_out_args
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

    fn count_obj_stores(module: &Module, name: &str) -> usize {
        let func_ref = lookup_func(module, name);
        module.func_store.view(func_ref, |func| {
            let mut count = 0;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    if downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)).is_some() {
                        count += 1;
                    }
                }
            }
            count
        })
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
    fn retained_byvalue_array_roots_share_across_branch_when_still_current() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Result = { i1, i256 };
type @Pair = { [i256; 5], [i8; 5] };

func private %check(v0.[i256; 5], v1.[i8; 5]) -> @Result {
block0:
    v2.objref<[i256; 5]> = obj.alloc [i256; 5];
    obj.store v2 v0;
    v3.objref<[i8; 5]> = obj.alloc [i8; 5];
    obj.store v3 v1;
    v4.[i256; 5] = obj.load v2;
    v5.i256 = extract_value v4 1.i8;
    v6.[i8; 5] = obj.load v3;
    v7.i8 = extract_value v6 1.i8;
    v8.i1 = eq v5 1.i256;
    v9.i1 = eq v7 1.i8;
    v10.i1 = and v8 v9;
    v11.@Result = insert_value undef.@Result 0.i8 v10;
    v12.@Result = insert_value v11 1.i8 0.i256;
    return v12;
}

func private %main() -> i1 {
block0:
    v0.objref<[i256; 5]> = obj.alloc [i256; 5];
    v1.[i256; 5] = insert_value undef.[i256; 5] 0.i8 0.i256;
    v2.[i256; 5] = insert_value v1 1.i8 1.i256;
    obj.store v0 v2;
    v3.objref<[i8; 5]> = obj.alloc [i8; 5];
    v4.[i8; 5] = insert_value undef.[i8; 5] 0.i8 0.i8;
    v5.[i8; 5] = insert_value v4 1.i8 1.i8;
    obj.store v3 v5;
    v6.objref<@Pair> = obj.alloc @Pair;
    v7.objref<[i256; 5]> = obj.proj v6 0.i8;
    v8.[i256; 5] = obj.load v0;
    obj.store v7 v8;
    v9.objref<[i8; 5]> = obj.proj v6 1.i8;
    v10.[i8; 5] = obj.load v3;
    obj.store v9 v10;
    v11.@Result = call %check v8 v10;
    v12.i1 = extract_value v11 0.i8;
    br v12 block1 block2;

block1:
    v13.@Result = call %check v8 v10;
    v14.i1 = extract_value v13 0.i8;
    return v14;

block2:
    return 0.i1;
}
"#,
        );

        run_byvalue_arg_abi(&module);
        let caller_ref = lookup_func(&module, "main");
        let callee_ref = lookup_func(&module, "check");
        let dumped = dump_func(&module, "main");
        assert_eq!(
            count_obj_allocs(&module, "main"),
            3,
            "current whole-root loads should be shared directly without extra copies:\n{dumped}"
        );
        let expected_arg_tys = module.func_store.view(callee_ref, |func| {
            [
                func.dfg.value_ty(func.arg_values[0]),
                func.dfg.value_ty(func.arg_values[1]),
            ]
        });
        module.func_store.view(caller_ref, |func| {
            let mut calls = Vec::new();
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    let Some(call) =
                        downcast::<&control_flow::Call>(func.inst_set(), func.dfg.inst(inst))
                    else {
                        continue;
                    };
                    if *call.callee() == callee_ref {
                        calls.push(call.args().to_vec());
                    }
                }
            }
            assert_eq!(
                calls.len(),
                2,
                "expected both calls to remain after rewrite:\n{dumped}"
            );
            for args in calls {
                assert_eq!(
                    args.len(),
                    2,
                    "rewritten calls should still have exactly two by-value args:\n{dumped}"
                );
                assert!(
                    value_is_obj_alloc(func, args[0])
                        && value_is_obj_alloc(func, args[1])
                        && func.dfg.value_ty(args[0]) == expected_arg_tys[0]
                        && func.dfg.value_ty(args[1]) == expected_arg_tys[1],
                    "rewritten calls should share the existing roots directly:\n{dumped}"
                );
            }
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
    fn readonly_borrowed_struct_with_dynamic_nested_index_should_share_without_copy() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Data = { [i8; 5], [i256; 5], [i256; 5] };
type @Res = { i1, i256 };

func private %element_get(v0.@Data, v1.i256, v2.i256) -> @Res {
block0:
    v3.objref<@Data> = obj.alloc @Data;
    obj.store v3 v0;
    v4.objref<[i8; 5]> = obj.proj v3 0.i8;
    v5.objref<i8> = obj.index v4 v2;
    v6.i8 = obj.load v5;
    v7.i1 = eq v6 0.i8;
    br v7 block1 block2;

block1:
    v8.@Res = insert_value undef.@Res 0.i8 0.i1;
    v9.@Res = insert_value v8 1.i8 0.i256;
    return v9;

block2:
    v10.objref<[i256; 5]> = obj.proj v3 2.i8;
    v11.objref<i256> = obj.index v10 v2;
    v12.i256 = obj.load v11;
    v13.@Res = insert_value undef.@Res 0.i8 1.i1;
    v14.@Res = insert_value v13 1.i8 v12;
    return v14;
}

func private %caller(v0.objref<@Data>, v1.i256) -> i256 {
block0:
    v2.@Data = obj.load v0;
    v3.@Res = call %element_get v2 0.i256 v1;
    v4.i1 = extract_value v3 0.i8;
    br v4 block1 block2;

block1:
    v5.i256 = extract_value v3 1.i8;
    return v5;

block2:
    return 0.i256;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let call_args = first_call_args(&module, "caller", "element_get");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            0,
            "readonly borrowed struct path should not copy:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_arg(func, call_args[0]) && call_args[0] == func.arg_values[0],
                "readonly borrowed struct path should share the live-in objref:\n{dumped}"
            );
            assert!(
                call_args.get(2).copied() == Some(func.arg_values[1]),
                "dynamic index should stay the original scalar arg:\n{dumped}"
            );
        });
    }

    #[test]
    fn readonly_large_borrowed_struct_with_dynamic_nested_index_should_share_without_copy() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Data = { [i8; 192], [i256; 192], [i256; 192] };
type @Res = { i1, i256 };

func private %element_get(v0.@Data, v1.i256, v2.i256) -> @Res {
block0:
    v3.objref<@Data> = obj.alloc @Data;
    obj.store v3 v0;
    v4.objref<[i8; 192]> = obj.proj v3 0.i8;
    v5.objref<i8> = obj.index v4 v2;
    v6.i8 = obj.load v5;
    v7.i1 = eq v6 0.i8;
    br v7 block1 block2;

block1:
    v8.@Res = insert_value undef.@Res 0.i8 0.i1;
    v9.@Res = insert_value v8 1.i8 0.i256;
    return v9;

block2:
    v10.objref<[i256; 192]> = obj.proj v3 2.i8;
    v11.objref<i256> = obj.index v10 v2;
    v12.i256 = obj.load v11;
    v13.@Res = insert_value undef.@Res 0.i8 1.i1;
    v14.@Res = insert_value v13 1.i8 v12;
    return v14;
}

func private %caller(v0.objref<@Data>, v1.i256) -> i256 {
block0:
    v2.@Data = obj.load v0;
    v3.@Res = call %element_get v2 0.i256 v1;
    v4.i1 = extract_value v3 0.i8;
    br v4 block1 block2;

block1:
    v5.i256 = extract_value v3 1.i8;
    return v5;

block2:
    return 0.i256;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let call_args = first_call_args(&module, "caller", "element_get");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            0,
            "readonly large borrowed struct path should not copy:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_arg(func, call_args[0]) && call_args[0] == func.arg_values[0],
                "readonly large borrowed struct path should share the live-in objref:\n{dumped}"
            );
            assert!(
                call_args.get(2).copied() == Some(func.arg_values[1]),
                "dynamic index should stay the original scalar arg:\n{dumped}"
            );
        });
    }

    #[test]
    fn readonly_borrowed_arg_across_branch_should_share_without_copy() {
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

func private %caller(v0.objref<[i256; 8]>, v1.i1) -> i256 {
block0:
    v2.[i256; 8] = obj.load v0;
    br v1 block1 block2;

block1:
    v3.i256 = call %readonly v2;
    return v3;

block2:
    return 0.i256;
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
            "readonly borrowed arg across a branch should not copy:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_arg(func, call_args[0]) && call_args[0] == func.arg_values[0],
                "readonly borrowed arg across a branch should share the live-in objref:\n{dumped}"
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
    fn large_aggregate_return_rewrites_to_hidden_out_arg() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @subtree = { i256, i256 };
type @big = { i256, i256, i256, [i256; 32], [@subtree; 32], i1 };

func private %empty() -> @big {
block0:
    v0.objref<@big> = obj.alloc @big;
    v1.@big = obj.load v0;
    return v1;
}

func private %caller() -> i1 {
block0:
    v0.@big = call %empty;
    v1.i1 = extract_value v0 5.i8;
    return v1;
}
"#,
        );

        let synthetic_out_args = run_object_aggregate_abi(&module);

        let empty = lookup_func(&module, "empty");
        let sig = module.ctx.get_sig(empty).expect("signature should exist");
        assert_eq!(
            sig.args().len(),
            1,
            "big return should become hidden out arg"
        );
        assert!(
            sig.ret_tys().is_empty(),
            "big aggregate return should be removed from direct returns"
        );
        assert!(
            synthetic_out_args
                .get(&empty)
                .and_then(|args| args.get(&0))
                .is_some(),
            "hidden out arg should be recorded as synthetic local root"
        );

        let call_args = first_call_args(&module, "caller", "empty");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            call_args.len(),
            1,
            "caller should pass a hidden out root:\n{dumped}"
        );
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            1,
            "caller should use one temp out object:\n{dumped}"
        );
        assert_eq!(
            dumped.matches("obj.load").count(),
            1,
            "live aggregate result should reload exactly once after call:\n{dumped}"
        );
    }

    #[test]
    fn large_aggregate_call_forwards_explicit_store_destination() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %make() -> [i256; 20] {
block0:
    v0.[i256; 20] = insert_value undef.[i256; 20] 0.i8 7.i256;
    return v0;
}

func private %caller() -> i256 {
block0:
    v0.objref<[i256; 20]> = obj.alloc [i256; 20];
    v1.[i256; 20] = call %make;
    obj.store v0 v1;
    v2.[i256; 20] = obj.load v0;
    v3.i256 = extract_value v2 0.i8;
    return v3;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let dest_root = first_obj_alloc_result(&module, "caller");
        let call_args = first_call_args(&module, "caller", "make");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            call_args,
            vec![dest_root],
            "call should forward dst:\n{dumped}"
        );
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            1,
            "forwarding should avoid a temp out object:\n{dumped}"
        );
        assert_eq!(
            count_obj_stores(&module, "caller"),
            0,
            "forwarding should remove the explicit post-call store:\n{dumped}"
        );
    }

    #[test]
    fn large_aggregate_call_forwards_caller_hidden_out_arg() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %make() -> [i256; 20] {
block0:
    v0.[i256; 20] = insert_value undef.[i256; 20] 0.i8 7.i256;
    return v0;
}

func private %caller() -> [i256; 20] {
block0:
    v0.[i256; 20] = call %make;
    return v0;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let caller_ref = lookup_func(&module, "caller");
        let call_args = first_call_args(&module, "caller", "make");
        let dumped = dump_func(&module, "caller");
        assert_eq!(
            count_obj_allocs(&module, "caller"),
            0,
            "caller return forwarding should avoid temp allocation:\n{dumped}"
        );
        module.func_store.view(caller_ref, |func| {
            assert!(
                value_is_arg(func, call_args[0]),
                "caller hidden out arg should be forwarded:\n{dumped}"
            );
        });
    }

    #[test]
    fn callee_return_root_fold_reuses_hidden_out_arg() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %make() -> [i256; 20] {
block0:
    v0.objref<[i256; 20]> = obj.alloc [i256; 20];
    v1.[i256; 20] = insert_value undef.[i256; 20] 0.i8 7.i256;
    obj.store v0 v1;
    v2.[i256; 20] = obj.load v0;
    return v2;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let dumped = dump_func(&module, "make");
        assert_eq!(
            count_obj_allocs(&module, "make"),
            0,
            "callee root fold should remove the local return alloc:\n{dumped}"
        );
        assert_eq!(
            count_obj_stores(&module, "make"),
            1,
            "folded return should not add a second final obj.store:\n{dumped}"
        );
    }

    #[test]
    fn dead_large_aggregate_call_result_skips_post_call_load() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @subtree = { i256, i256 };
type @big = { i256, i256, i256, [i256; 32], [@subtree; 32], i1 };

func private %empty() -> @big {
block0:
    v0.objref<@big> = obj.alloc @big;
    v1.@big = obj.load v0;
    return v1;
}

func private %caller() {
block0:
    v0.@big = call %empty;
    return;
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let dumped = dump_func(&module, "caller");
        assert_eq!(
            dumped.matches("obj.load").count(),
            0,
            "dead aggregate result should not reload temp out object:\n{dumped}"
        );
    }

    #[test]
    fn mixed_returns_only_large_aggregate_becomes_out_object() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @small = { i256, i256 };
type @subtree = { i256, i256 };
type @big = { i256, i256, i256, [i256; 32], [@subtree; 32], i1 };

func private %mix() -> (i256, @big, @small) {
block0:
    v0.objref<@big> = obj.alloc @big;
    v1.@big = obj.load v0;
    v2.@small = insert_value undef.@small 0.i8 1.i256;
    return (7.i256, v1, v2);
}
"#,
        );

        run_byvalue_arg_abi(&module);

        let mix = lookup_func(&module, "mix");
        let sig = module.ctx.get_sig(mix).expect("signature should exist");
        assert_eq!(
            sig.args().len(),
            1,
            "only big aggregate should use hidden out arg"
        );
        assert_eq!(
            sig.ret_tys().len(),
            2,
            "small direct returns should remain direct"
        );
        assert_eq!(sig.ret_tys()[0], Type::I256);
        assert!(
            matches!(
                sig.ret_tys()[1].resolve_compound(&module.ctx),
                Some(CompoundType::Struct(_))
            ),
            "small aggregate return should remain direct"
        );
    }

    #[test]
    fn impossible_call_budget_reports_clear_error() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func private %impossible(v0.i256, v1.i256, v2.i256, v3.i256, v4.i256, v5.i256, v6.i256, v7.i256, v8.i256, v9.i256, v10.i256, v11.i256, v12.i256, v13.i256, v14.i256, v15.i256, v16.i256) -> [i256; 20] {
block0:
    v17.objref<[i256; 20]> = obj.alloc [i256; 20];
    v18.[i256; 20] = obj.load v17;
    return v18;
}
"#,
        );

        let err = ObjectAggregateAbi::default()
            .run_with_synthetic_out_args(&module)
            .expect_err("rewriting should report impossible call budget");
        assert!(
            err.contains("cannot lower impossible for EVM")
                && err.contains("hidden out parameters")
                && err.contains("direct call operands"),
            "unexpected diagnostic: {err}"
        );
    }

    #[test]
    fn large_aggregate_return_compiles_through_evm_pipeline() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @subtree = { i256, i256 };
type @big = { i256, i256, i256, [i256; 32], [@subtree; 32], i1 };

func private %empty_10() -> @big {
block0:
    v0.objref<@big> = obj.alloc @big;
    v1.@big = obj.load v0;
    return v1;
}

func public %entry() -> i1 {
block0:
    v0.@big = call %empty_10;
    v1.i1 = extract_value v0 5.i8;
    return v1;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );

        let backend = test_backend();
        let opts = CompileOptions {
            fixup_policy: PushWidthPolicy::MinimalRelax,
            emit_symtab: false,
            emit_observability: false,
            verifier_cfg: VerifierConfig::for_level(VerificationLevel::Fast),
        };
        compile_all_objects(&module, &backend, &opts).expect("compile should succeed");
        prepare_root(&module, &backend, lookup_func(&module, "entry"))
            .expect("prepare should succeed");
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
