use std::collections::{BTreeMap, BTreeSet};

use crate::module_analysis::{CallGraph, CallGraphSccs, SccBuilder, SccRef};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, Function, Module, Type, ValueId,
    cfg::ControlFlowGraph,
    inst::{control_flow, data, downcast},
    module::{FuncRef, ModuleCtx},
};

use super::{
    capture_state::{
        CaptureRelevantInst, RootCaptureMap as SharedRootCaptureMap, RootCapturePayload,
        capture_relevant_inst, compute_capture_states_for_blocks as compute_block_capture_states,
        kill_capture_access as kill_capture_projection_access,
        kill_capture_slice_set as kill_capture_exact_slice_set, slices_overlap_relative,
    },
    object_tracking::AggregateFacts,
    provenance::{
        CompleteProvenance, CompleteRootSet, MayProvenance, RootValue, exact_capture_destination,
        observed_root_slices,
    },
    shape,
};

const MAX_EXACT_EFFECT_LEAVES: usize = 64;

pub(crate) type ObjectEffectSummaryMap = FxHashMap<FuncRef, ObjectEffectSummary>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ObjectEffectSummary {
    pub arg_effects: Vec<ObjectArgEffect>,
    pub captures: Vec<ObjectCaptureEffect>,
    pub ret_effect: ObjectReturnEffect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ObjectCaptureDestination {
    Arg {
        index: usize,
        slice: shape::AggregateSlice,
    },
    Return {
        slice: shape::AggregateSlice,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ObjectCaptureEffect {
    pub dst: ObjectCaptureDestination,
    pub src_arg: usize,
    pub src_slice: shape::AggregateSlice,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RootCaptureEffect {
    dst_slice: shape::AggregateSlice,
    src_arg: usize,
    src_slice: shape::AggregateSlice,
}

type RootCaptureMap = SharedRootCaptureMap<RootCaptureEffect>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ReturnedFreshSlice {
    root_value: RootValue,
    return_slice: shape::AggregateSlice,
    possible_slices: Option<Vec<shape::AggregateSlice>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ReturnAnalysis {
    ret_effect: ObjectReturnEffect,
    returned_fresh_slices: Vec<ReturnedFreshSlice>,
}

#[derive(Clone, Copy)]
struct EffectProvenance<'a> {
    complete: CompleteProvenance<'a>,
    may: MayProvenance<'a>,
    arg_roots: &'a FxHashMap<RootValue, usize>,
}

impl<'a> EffectProvenance<'a> {
    fn exact_projection(self, value: ValueId) -> Option<super::Projection> {
        self.complete.exact_projection(value)
    }

    fn arg_root_indices_for_observation(self, value: ValueId) -> SmallVec<[usize; 4]> {
        let mut seen = FxHashSet::default();
        let mut out = SmallVec::new();

        for root in self.may.may_roots(value).observed().iter() {
            if let Some(&idx) = self.arg_roots.get(&root)
                && seen.insert(idx)
            {
                out.push(idx);
            }
        }

        out
    }

    fn root_slices_for_observation(
        self,
        value: ValueId,
    ) -> SmallVec<[(RootValue, shape::AggregateSlice); 4]> {
        observed_root_slices(
            self.exact_projection(value),
            self.may.may_roots(value).observed(),
            |root| {
                self.complete
                    .exact_root_slice(root)
                    .expect("observed provenance root must have an exact root slice")
            },
        )
    }
}

impl RootCapturePayload for RootCaptureEffect {
    fn dst_slice(self) -> shape::AggregateSlice {
        self.dst_slice
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ObjectArgEffect {
    pub local_only: bool,
    pub escapes: bool,
    pub reads: SliceSet,
    pub writes: SliceSet,
    pub materializes_stack: bool,
    pub materializes_heap: bool,
}

impl ObjectArgEffect {
    pub(crate) fn needs_unknown_object_barrier(&self) -> bool {
        self.escapes || self.materializes_stack || self.materializes_heap
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ObjectReturnEffect {
    None,
    FreshObject,
    SameAsArg { index: usize },
    DerivedFromArg { index: usize },
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SliceSet {
    total_leaves: usize,
    exact_leaves: Option<FxHashSet<usize>>,
    whole_root: bool,
}

impl SliceSet {
    pub(crate) fn empty(total_leaves: usize) -> Self {
        Self {
            total_leaves,
            exact_leaves: (total_leaves <= MAX_EXACT_EFFECT_LEAVES).then(FxHashSet::default),
            whole_root: false,
        }
    }

    pub(crate) fn whole_root(total_leaves: usize) -> Self {
        Self {
            total_leaves,
            exact_leaves: None,
            whole_root: total_leaves != 0,
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        !self.whole_root && self.exact_leaves.as_ref().is_none_or(FxHashSet::is_empty)
    }

    pub(crate) fn is_whole_root(&self) -> bool {
        self.whole_root
    }

    pub(crate) fn total_leaves(&self) -> usize {
        self.total_leaves
    }

    pub(crate) fn exact_leaves(&self) -> Option<&FxHashSet<usize>> {
        self.exact_leaves.as_ref().filter(|_| !self.whole_root)
    }

    pub(crate) fn add_slice(&mut self, slice: shape::AggregateSlice) {
        if self.total_leaves == 0 {
            return;
        }
        if slice.first_leaf == 0 && slice.leaf_count == self.total_leaves {
            self.whole_root = true;
            self.exact_leaves = None;
            return;
        }
        let Some(exact_leaves) = self.exact_leaves.as_mut() else {
            self.whole_root = true;
            return;
        };
        exact_leaves.extend(slice.first_leaf..slice.first_leaf + slice.leaf_count);
    }

    pub(crate) fn union_with(&mut self, other: &SliceSet) {
        self.total_leaves = self.total_leaves.max(other.total_leaves);
        if self.whole_root || other.whole_root {
            self.whole_root = self.total_leaves != 0;
            self.exact_leaves = None;
            return;
        }
        match (&mut self.exact_leaves, &other.exact_leaves) {
            (Some(dst), Some(src)) => dst.extend(src.iter().copied()),
            (_, Some(src)) if !src.is_empty() => {
                self.whole_root = self.total_leaves != 0;
                self.exact_leaves = None;
            }
            _ => {}
        }
    }
}

impl ObjectEffectSummary {
    fn new(
        module: &ModuleCtx,
        func: FuncRef,
        layout_cache: &mut shape::AggregateLayoutCache,
    ) -> Self {
        let arg_effects = module
            .get_sig(func)
            .map(|sig| {
                sig.args()
                    .iter()
                    .copied()
                    .map(|ty| ObjectArgEffect::new(module, ty, layout_cache))
                    .collect()
            })
            .unwrap_or_default();
        Self {
            arg_effects,
            captures: Vec::new(),
            ret_effect: ObjectReturnEffect::None,
        }
    }

    pub(crate) fn conservative_unknown(
        module: &ModuleCtx,
        func: FuncRef,
        layout_cache: &mut shape::AggregateLayoutCache,
    ) -> Self {
        let mut summary = Self::new(module, func, layout_cache);
        for (idx, effect) in summary.arg_effects.iter_mut().enumerate() {
            let Some(sig) = module.get_sig(func) else {
                break;
            };
            let Some(elem_ty) = objref_element_ty(module, sig.args()[idx]) else {
                continue;
            };
            let whole = whole_root_slice(layout_cache, module, elem_ty);
            effect.escapes = true;
            effect.local_only = false;
            effect.materializes_heap = true;
            effect.reads = SliceSet::whole_root(whole.leaf_count);
            effect.writes = SliceSet::whole_root(whole.leaf_count);
        }
        summary.ret_effect = ObjectReturnEffect::Unknown;
        summary
    }
}

impl ObjectArgEffect {
    fn new(module: &ModuleCtx, ty: Type, layout_cache: &mut shape::AggregateLayoutCache) -> Self {
        let total_leaves = objref_element_ty(module, ty)
            .map(|elem_ty| whole_root_slice(layout_cache, module, elem_ty).leaf_count)
            .unwrap_or(0);
        Self {
            local_only: false,
            escapes: false,
            reads: SliceSet::empty(total_leaves),
            writes: SliceSet::empty(total_leaves),
            materializes_stack: false,
            materializes_heap: false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReturnClass {
    None,
    FreshObject,
    SameAsArg(usize),
    DerivedFromArg(usize),
    Unknown,
}

pub(crate) fn compute_object_effect_summaries(module: &Module) -> ObjectEffectSummaryMap {
    let mut summaries = ObjectEffectSummaryMap::default();
    let mut layout_cache = shape::AggregateLayoutCache::default();
    let funcs = defined_object_effect_funcs(module);
    if funcs.is_empty() {
        return summaries;
    }

    let func_set = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &func_set);
    let sccs = SccBuilder::new().compute_scc(&call_graph);
    let topo = topo_sort_object_effect_sccs(&func_set, &call_graph, &sccs);

    for scc_ref in topo.iter().rev().copied() {
        let funcs = sorted_scc_funcs(&sccs, scc_ref);
        if !sccs.scc_info(scc_ref).is_cycle {
            for func in funcs {
                let next = compute_summary_for_func(module, func, &summaries, &mut layout_cache);
                summaries.insert(func, next);
            }
            continue;
        }

        initialize_object_effect_scc(module, &funcs, &mut summaries, &mut layout_cache);
        loop {
            let mut changed = false;
            for &func in &funcs {
                let next = compute_summary_for_func(module, func, &summaries, &mut layout_cache);
                if summaries.get(&func) != Some(&next) {
                    summaries.insert(func, next);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    summaries
}

fn defined_object_effect_funcs(module: &Module) -> Vec<FuncRef> {
    let mut funcs: Vec<_> = module
        .funcs()
        .into_iter()
        .filter(|&func| {
            module
                .ctx
                .get_sig(func)
                .is_some_and(|sig| sig.linkage().has_definition())
        })
        .collect();
    funcs.sort_unstable_by_key(|func| func.as_u32());
    funcs
}

fn initialize_object_effect_scc(
    module: &Module,
    funcs: &[FuncRef],
    summaries: &mut ObjectEffectSummaryMap,
    layout_cache: &mut shape::AggregateLayoutCache,
) {
    for &func in funcs {
        summaries.entry(func).or_insert_with(|| {
            ObjectEffectSummary::conservative_unknown(&module.ctx, func, layout_cache)
        });
    }
}

fn sorted_scc_funcs(sccs: &CallGraphSccs, scc_ref: SccRef) -> Vec<FuncRef> {
    let mut funcs: Vec<_> = sccs.scc_info(scc_ref).components.iter().copied().collect();
    funcs.sort_unstable_by_key(|func| func.as_u32());
    funcs
}

fn topo_sort_object_effect_sccs(
    funcs: &FxHashSet<FuncRef>,
    call_graph: &CallGraph,
    sccs: &CallGraphSccs,
) -> Vec<SccRef> {
    let mut scc_refs = BTreeSet::new();
    for &func in funcs {
        scc_refs.insert(sccs.scc_ref(func));
    }

    let mut edges = BTreeMap::<SccRef, BTreeSet<SccRef>>::new();
    let mut indegree = BTreeMap::<SccRef, usize>::new();
    for &scc_ref in &scc_refs {
        edges.insert(scc_ref, BTreeSet::new());
        indegree.insert(scc_ref, 0);
    }

    for &func in funcs {
        let from = sccs.scc_ref(func);
        for &callee in call_graph.callee_of(func) {
            let to = sccs.scc_ref(callee);
            if from != to && edges.get_mut(&from).expect("missing SCC").insert(to) {
                *indegree.get_mut(&to).expect("missing SCC") += 1;
            }
        }
    }

    let mut ready: BTreeSet<_> = indegree
        .iter()
        .filter_map(|(&scc_ref, &deg)| (deg == 0).then_some(scc_ref))
        .collect();
    let mut topo = Vec::with_capacity(scc_refs.len());
    while let Some(scc_ref) = ready.pop_first() {
        topo.push(scc_ref);
        let tos: Vec<_> = edges
            .get(&scc_ref)
            .expect("missing SCC")
            .iter()
            .copied()
            .collect();
        for to in tos {
            let deg = indegree.get_mut(&to).expect("missing SCC");
            *deg = deg.checked_sub(1).expect("SCC indegree underflow");
            if *deg == 0 {
                ready.insert(to);
            }
        }
    }

    debug_assert_eq!(topo.len(), scc_refs.len(), "SCC topo sort incomplete");
    topo
}

fn compute_summary_for_func(
    module: &Module,
    func: FuncRef,
    summaries: &ObjectEffectSummaryMap,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> ObjectEffectSummary {
    module.func_store.view(func, |function| {
        let mut summary = ObjectEffectSummary::new(function.ctx(), func, layout_cache);
        let mut root_slices = FxHashMap::default();
        let mut arg_roots = FxHashMap::default();

        for (idx, &arg) in function.arg_values.iter().enumerate() {
            let Some(elem_ty) = objref_element_ty(function.ctx(), function.dfg.value_ty(arg))
            else {
                continue;
            };
            let slice = whole_root_slice(layout_cache, function.ctx(), elem_ty);
            root_slices.insert(arg, slice);
            arg_roots.insert(RootValue::new(arg), idx);
        }

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                if let Some(obj_alloc) =
                    downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(inst))
                    && let Some(result) = function.dfg.inst_result(inst)
                {
                    root_slices.insert(
                        result,
                        whole_root_slice(layout_cache, function.ctx(), *obj_alloc.ty()),
                    );
                }
            }
        }

        let facts = AggregateFacts::from_root_slices(
            function,
            function.ctx(),
            root_slices,
            layout_cache,
            Some(summaries),
        );
        let effect_provenance = EffectProvenance {
            complete: facts.complete(),
            may: facts.may(),
            arg_roots: &arg_roots,
        };
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(function);
        let reachable = cfg.reachable_blocks();
        let return_analysis = analyze_returns(
            function,
            &reachable,
            &arg_roots,
            facts.complete(),
            layout_cache,
        );
        let (block_entry_captures, exit_root_captures) = compute_capture_states_for_blocks(
            function,
            effect_provenance,
            summaries,
            layout_cache,
            &cfg,
            &reachable,
        );

        for block in function.layout.iter_block() {
            if !reachable[block] {
                continue;
            }

            let mut root_captures = block_entry_captures[block].clone();
            for inst in function.layout.iter_inst(block) {
                if !function.layout.is_inst_inserted(inst) {
                    continue;
                }

                if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(function.inst_set(), function.dfg.inst(inst))
                {
                    record_read(
                        &mut summary,
                        &root_captures,
                        effect_provenance,
                        *obj_load.object(),
                    );
                    continue;
                }

                if let Some(enum_get_tag) =
                    downcast::<&data::EnumGetTag>(function.inst_set(), function.dfg.inst(inst))
                {
                    record_enum_tag_read(
                        &mut summary,
                        &root_captures,
                        effect_provenance,
                        *enum_get_tag.object(),
                    );
                    continue;
                }

                if let Some(enum_assert_ref) = downcast::<&data::EnumAssertVariantRef>(
                    function.inst_set(),
                    function.dfg.inst(inst),
                ) {
                    record_enum_tag_read(
                        &mut summary,
                        &root_captures,
                        effect_provenance,
                        *enum_assert_ref.object(),
                    );
                    continue;
                }

                if let Some(obj_store) =
                    downcast::<&data::ObjStore>(function.inst_set(), function.dfg.inst(inst))
                {
                    record_write(
                        &mut summary,
                        &mut root_captures,
                        effect_provenance,
                        *obj_store.object(),
                    );
                    record_capture(
                        &mut root_captures,
                        effect_provenance,
                        *obj_store.object(),
                        *obj_store.value(),
                    );
                    continue;
                }

                if let Some(enum_set_tag) =
                    downcast::<&data::EnumSetTag>(function.inst_set(), function.dfg.inst(inst))
                {
                    record_enum_tag_write(
                        &mut summary,
                        &mut root_captures,
                        effect_provenance,
                        *enum_set_tag.object(),
                    );
                    continue;
                }

                if let Some(enum_write_variant) = downcast::<&data::EnumWriteVariant>(
                    function.inst_set(),
                    function.dfg.inst(inst),
                ) {
                    record_enum_write_variant(
                        function,
                        &mut summary,
                        &mut root_captures,
                        effect_provenance,
                        *enum_write_variant.object(),
                        *enum_write_variant.variant(),
                        enum_write_variant.values(),
                    );
                    continue;
                }

                if let Some(mat_stack) = downcast::<&data::ObjMaterializeStack>(
                    function.inst_set(),
                    function.dfg.inst(inst),
                ) {
                    record_materialize(
                        &mut summary,
                        &root_captures,
                        effect_provenance,
                        *mat_stack.object(),
                        false,
                    );
                    continue;
                }

                if let Some(mat_heap) = downcast::<&data::ObjMaterializeHeap>(
                    function.inst_set(),
                    function.dfg.inst(inst),
                ) {
                    record_materialize(
                        &mut summary,
                        &root_captures,
                        effect_provenance,
                        *mat_heap.object(),
                        true,
                    );
                    continue;
                }

                if downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst))
                    .is_some()
                {
                    merge_call_effects(
                        function,
                        inst,
                        &mut summary,
                        &mut root_captures,
                        effect_provenance,
                        summaries,
                        layout_cache,
                    );
                }
            }
        }

        emit_public_capture_effects(
            &mut summary,
            &exit_root_captures,
            &arg_roots,
            &return_analysis.returned_fresh_slices,
        );
        dedup_capture_effects(&mut summary.captures);
        summary.ret_effect = return_analysis.ret_effect;
        for idx in 0..summary.arg_effects.len() {
            summary.arg_effects[idx].local_only = !summary.arg_effects[idx]
                .needs_unknown_object_barrier()
                && !matches!(
                    summary.ret_effect,
                    ObjectReturnEffect::SameAsArg { index }
                        | ObjectReturnEffect::DerivedFromArg { index }
                        if index == idx
                );
        }
        summary
    })
}

fn compute_capture_states_for_blocks(
    function: &Function,
    effect_provenance: EffectProvenance<'_>,
    summaries: &ObjectEffectSummaryMap,
    layout_cache: &mut shape::AggregateLayoutCache,
    cfg: &ControlFlowGraph,
    reachable: &cranelift_entity::SecondaryMap<BlockId, bool>,
) -> (
    cranelift_entity::SecondaryMap<BlockId, RootCaptureMap>,
    RootCaptureMap,
) {
    compute_block_capture_states(function, cfg, reachable, |inst, exit_captures| {
        apply_inst_capture_transfer(
            function,
            inst,
            exit_captures,
            effect_provenance,
            summaries,
            layout_cache,
        );
    })
}

fn apply_inst_capture_transfer(
    function: &Function,
    inst: sonatina_ir::InstId,
    root_captures: &mut RootCaptureMap,
    effect_provenance: EffectProvenance<'_>,
    summaries: &ObjectEffectSummaryMap,
    layout_cache: &mut shape::AggregateLayoutCache,
) {
    if !function.layout.is_inst_inserted(inst) {
        return;
    }

    match capture_relevant_inst(function, inst) {
        Some(CaptureRelevantInst::ObjStore(obj_store)) => {
            kill_capture_access(root_captures, effect_provenance, *obj_store.object(), None);
            record_capture(
                root_captures,
                effect_provenance,
                *obj_store.object(),
                *obj_store.value(),
            );
        }
        Some(CaptureRelevantInst::EnumSetTag(enum_set_tag)) => {
            kill_capture_access(
                root_captures,
                effect_provenance,
                *enum_set_tag.object(),
                Some((0, 1)),
            );
        }
        Some(CaptureRelevantInst::EnumWriteVariant(enum_write_variant)) => {
            kill_capture_access(
                root_captures,
                effect_provenance,
                *enum_write_variant.object(),
                None,
            );
            record_enum_variant_captures(
                function,
                root_captures,
                effect_provenance,
                *enum_write_variant.object(),
                enum_write_variant.values(),
                *enum_write_variant.variant(),
            );
        }
        Some(CaptureRelevantInst::Call) => {
            apply_call_capture_transfer(
                function,
                inst,
                root_captures,
                effect_provenance,
                summaries,
                layout_cache,
            );
        }
        None => {}
    }
}

fn analyze_returns(
    function: &Function,
    reachable: &cranelift_entity::SecondaryMap<BlockId, bool>,
    arg_roots: &FxHashMap<RootValue, usize>,
    provenance: CompleteProvenance<'_>,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> ReturnAnalysis {
    let mut combined = ReturnClass::None;
    let mut saw_return = false;
    let mut returned_fresh_slices = Vec::new();
    let mut seen_returned_slices = FxHashSet::default();

    for block in function.layout.iter_block() {
        if !reachable[block] {
            continue;
        }

        for inst in function.layout.iter_inst(block) {
            let Some(ret) =
                downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(inst))
            else {
                continue;
            };
            saw_return = true;
            if ret.returns_unit() {
                combined = join_return_class(combined, ReturnClass::None);
                continue;
            }
            if !ret.returns_single() {
                combined = ReturnClass::Unknown;
                continue;
            }
            let Some(&value) = ret.arg() else {
                combined = join_return_class(combined, ReturnClass::None);
                continue;
            };
            let (class, fresh_slices) =
                classify_return_value(function, value, arg_roots, provenance, layout_cache);
            combined = join_return_class(combined, class);
            for fresh_slice in fresh_slices {
                if seen_returned_slices.insert(fresh_slice.clone()) {
                    returned_fresh_slices.push(fresh_slice);
                }
            }
        }
    }

    if !saw_return {
        return ReturnAnalysis {
            ret_effect: ObjectReturnEffect::None,
            returned_fresh_slices: Vec::new(),
        };
    }

    let ret_effect = match combined {
        ReturnClass::None => ObjectReturnEffect::None,
        ReturnClass::FreshObject => ObjectReturnEffect::FreshObject,
        ReturnClass::SameAsArg(index) => ObjectReturnEffect::SameAsArg { index },
        ReturnClass::DerivedFromArg(index) => ObjectReturnEffect::DerivedFromArg { index },
        ReturnClass::Unknown => ObjectReturnEffect::Unknown,
    };
    if ret_effect != ObjectReturnEffect::FreshObject {
        returned_fresh_slices.clear();
    }
    ReturnAnalysis {
        ret_effect,
        returned_fresh_slices,
    }
}

fn classify_return_value(
    function: &Function,
    value: ValueId,
    arg_roots: &FxHashMap<RootValue, usize>,
    provenance: CompleteProvenance<'_>,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> (ReturnClass, Vec<ReturnedFreshSlice>) {
    if objref_element_ty(function.ctx(), function.dfg.value_ty(value)).is_none() {
        return (ReturnClass::None, Vec::new());
    }

    if let Some(projection) = provenance.exact_projection(value) {
        let Some(return_ty) = objref_element_ty(function.ctx(), function.dfg.value_ty(value))
        else {
            return (ReturnClass::None, Vec::new());
        };
        if let Some(&idx) = arg_roots.get(&projection.root_value) {
            return (
                if provenance.exact_root_slice(projection.root_value) == Some(projection.slice) {
                    ReturnClass::SameAsArg(idx)
                } else {
                    ReturnClass::DerivedFromArg(idx)
                },
                Vec::new(),
            );
        }
        if is_fresh_root(function, projection.root_value.value()) {
            return (
                ReturnClass::FreshObject,
                vec![ReturnedFreshSlice {
                    root_value: projection.root_value,
                    return_slice: whole_root_slice(layout_cache, function.ctx(), return_ty),
                    possible_slices: Some(vec![projection.slice]),
                }],
            );
        }
        return (ReturnClass::Unknown, Vec::new());
    }

    match provenance.complete_roots(value) {
        Some(CompleteRootSet::Single(root)) => {
            if let Some(&idx) = arg_roots.get(&root) {
                (ReturnClass::DerivedFromArg(idx), Vec::new())
            } else if let Some(fresh_roots) =
                classify_all_fresh_roots(function, value, [root], provenance, layout_cache)
            {
                (ReturnClass::FreshObject, fresh_roots)
            } else {
                (ReturnClass::Unknown, Vec::new())
            }
        }
        Some(CompleteRootSet::Multiple(roots)) => {
            if roots.iter().any(|root| arg_roots.contains_key(&root)) {
                return (ReturnClass::Unknown, Vec::new());
            }
            if let Some(fresh_roots) =
                classify_all_fresh_roots(function, value, roots.iter(), provenance, layout_cache)
            {
                (ReturnClass::FreshObject, fresh_roots)
            } else {
                (ReturnClass::Unknown, Vec::new())
            }
        }
        None => (ReturnClass::Unknown, Vec::new()),
    }
}

fn classify_all_fresh_roots(
    function: &Function,
    value: ValueId,
    roots: impl IntoIterator<Item = RootValue>,
    provenance: CompleteProvenance<'_>,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> Option<Vec<ReturnedFreshSlice>> {
    let return_ty = objref_element_ty(function.ctx(), function.dfg.value_ty(value))?;
    let return_slice = whole_root_slice(layout_cache, function.ctx(), return_ty);
    let mut roots: Vec<_> = roots.into_iter().collect();
    roots.sort_unstable_by_key(|root| root.as_u32());
    roots.dedup();
    if roots.is_empty()
        || roots
            .iter()
            .any(|&root| !is_fresh_root(function, root.value()))
    {
        return None;
    }

    let mut returned = Vec::with_capacity(roots.len());
    for root in roots {
        let mut possible_slices = Vec::new();
        for slice in provenance.possible_slices_for_root(value, root)? {
            if slice.ty == return_ty {
                push_unique_slice(&mut possible_slices, slice);
            }
        }
        returned.push(ReturnedFreshSlice {
            root_value: root,
            return_slice,
            possible_slices: (!possible_slices.is_empty()).then_some(possible_slices),
        });
    }
    Some(returned)
}

fn join_return_class(lhs: ReturnClass, rhs: ReturnClass) -> ReturnClass {
    match (lhs, rhs) {
        (ReturnClass::Unknown, _) | (_, ReturnClass::Unknown) => ReturnClass::Unknown,
        (ReturnClass::None, other) | (other, ReturnClass::None) => other,
        (ReturnClass::FreshObject, ReturnClass::FreshObject) => ReturnClass::FreshObject,
        (ReturnClass::SameAsArg(lhs), ReturnClass::SameAsArg(rhs)) if lhs == rhs => {
            ReturnClass::SameAsArg(lhs)
        }
        (ReturnClass::SameAsArg(lhs), ReturnClass::DerivedFromArg(rhs))
        | (ReturnClass::DerivedFromArg(lhs), ReturnClass::SameAsArg(rhs))
        | (ReturnClass::DerivedFromArg(lhs), ReturnClass::DerivedFromArg(rhs))
            if lhs == rhs =>
        {
            ReturnClass::DerivedFromArg(lhs)
        }
        _ => ReturnClass::Unknown,
    }
}

fn emit_public_capture_effects(
    summary: &mut ObjectEffectSummary,
    root_captures: &RootCaptureMap,
    arg_roots: &FxHashMap<RootValue, usize>,
    returned_fresh_slices: &[ReturnedFreshSlice],
) {
    for (&root, &index) in arg_roots {
        let Some(captures) = root_captures.get(&root) else {
            continue;
        };
        for &capture in captures {
            push_capture_effect(
                summary,
                ObjectCaptureEffect {
                    dst: ObjectCaptureDestination::Arg {
                        index,
                        slice: capture.dst_slice,
                    },
                    src_arg: capture.src_arg,
                    src_slice: capture.src_slice,
                },
            );
        }
    }

    for returned in returned_fresh_slices {
        let Some(captures) = root_captures.get(&returned.root_value) else {
            continue;
        };
        let mut captures_by_source =
            FxHashMap::<(usize, shape::AggregateSlice), Vec<shape::AggregateSlice>>::default();
        for &capture in captures {
            captures_by_source
                .entry((capture.src_arg, capture.src_slice))
                .or_default()
                .push(capture.dst_slice);
        }
        for ((src_arg, src_slice), dst_slices) in captures_by_source {
            for slice in return_capture_slices_for_source(returned, &dst_slices) {
                push_capture_effect(
                    summary,
                    ObjectCaptureEffect {
                        dst: ObjectCaptureDestination::Return { slice },
                        src_arg,
                        src_slice,
                    },
                );
            }
        }
    }
}

fn return_capture_slices_for_source(
    returned: &ReturnedFreshSlice,
    dst_slices: &[shape::AggregateSlice],
) -> Vec<shape::AggregateSlice> {
    let Some(possible_slices) = returned.possible_slices.as_deref() else {
        return vec![returned.return_slice];
    };

    let mut common_slices = None::<Vec<shape::AggregateSlice>>;
    let mut any_overlap = false;
    for &possible_slice in possible_slices {
        let mut candidate_slices = Vec::new();
        for &dst_slice in dst_slices {
            let Some(slice) = rebase_return_capture_slice(possible_slice, dst_slice) else {
                continue;
            };
            push_unique_slice(&mut candidate_slices, slice);
        }
        any_overlap |= !candidate_slices.is_empty();
        match common_slices.as_ref() {
            Some(existing) if !same_slice_set(existing, &candidate_slices) => {
                return any_overlap
                    .then_some(vec![returned.return_slice])
                    .unwrap_or_default();
            }
            Some(_) => {}
            None => common_slices = Some(candidate_slices),
        }
    }

    common_slices
        .filter(|slices| !slices.is_empty())
        .unwrap_or_else(|| {
            any_overlap
                .then_some(vec![returned.return_slice])
                .unwrap_or_default()
        })
}

fn rebase_return_capture_slice(
    returned_slice: shape::AggregateSlice,
    capture_slice: shape::AggregateSlice,
) -> Option<shape::AggregateSlice> {
    if let Some(slice) = rebase_slice(returned_slice, capture_slice) {
        return Some(slice);
    }
    slices_overlap_relative(returned_slice, capture_slice).then_some(shape::AggregateSlice {
        ty: returned_slice.ty,
        first_leaf: 0,
        leaf_count: returned_slice.leaf_count,
    })
}

fn rebase_slice(
    base_slice: shape::AggregateSlice,
    nested_slice: shape::AggregateSlice,
) -> Option<shape::AggregateSlice> {
    (base_slice.first_leaf <= nested_slice.first_leaf
        && nested_slice.first_leaf + nested_slice.leaf_count
            <= base_slice.first_leaf + base_slice.leaf_count)
        .then(|| shape::AggregateSlice {
            ty: nested_slice.ty,
            first_leaf: nested_slice.first_leaf - base_slice.first_leaf,
            leaf_count: nested_slice.leaf_count,
        })
}

fn merge_call_effects(
    function: &Function,
    inst: sonatina_ir::InstId,
    summary: &mut ObjectEffectSummary,
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    summaries: &ObjectEffectSummaryMap,
    layout_cache: &mut shape::AggregateLayoutCache,
) {
    let call = downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst))
        .expect("merge_call_effects requires a call instruction");
    let callee_summary = call_effect_summary(function, call, summaries, layout_cache);
    let pre_call_captures = root_captures.clone();

    for (callee_idx, &arg) in call.args().iter().enumerate() {
        let Some(callee_effect) = callee_summary.arg_effects.get(callee_idx) else {
            continue;
        };
        merge_call_arg_effect(
            summary,
            &pre_call_captures,
            root_captures,
            capture_ctx,
            arg,
            callee_effect,
        );
    }
    merge_call_capture_effects(
        function,
        inst,
        root_captures,
        &pre_call_captures,
        capture_ctx,
        call,
        &callee_summary.captures,
    );
}

fn apply_call_capture_transfer(
    function: &Function,
    inst: sonatina_ir::InstId,
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    summaries: &ObjectEffectSummaryMap,
    layout_cache: &mut shape::AggregateLayoutCache,
) {
    let call = downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst))
        .expect("apply_call_capture_transfer requires a call instruction");
    let callee_summary = call_effect_summary(function, call, summaries, layout_cache);
    let pre_call_captures = root_captures.clone();

    for (callee_idx, &arg) in call.args().iter().enumerate() {
        let Some(callee_effect) = callee_summary.arg_effects.get(callee_idx) else {
            continue;
        };
        kill_capture_slice_set(root_captures, capture_ctx, arg, &callee_effect.writes);
    }
    merge_call_capture_effects(
        function,
        inst,
        root_captures,
        &pre_call_captures,
        capture_ctx,
        call,
        &callee_summary.captures,
    );
}

fn call_effect_summary(
    function: &Function,
    call: &control_flow::Call,
    summaries: &ObjectEffectSummaryMap,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> ObjectEffectSummary {
    summaries.get(call.callee()).cloned().unwrap_or_else(|| {
        ObjectEffectSummary::conservative_unknown(function.ctx(), *call.callee(), layout_cache)
    })
}

fn merge_call_arg_effect(
    summary: &mut ObjectEffectSummary,
    capture_sources: &RootCaptureMap,
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    value: ValueId,
    callee_effect: &ObjectArgEffect,
) {
    if callee_effect.reads.is_empty()
        && callee_effect.writes.is_empty()
        && !callee_effect.needs_unknown_object_barrier()
    {
        return;
    }

    if let Some(projection) = capture_ctx.exact_projection(value)
        && let Some(&idx) = capture_ctx.arg_roots.get(&projection.root_value)
    {
        merge_effect_into_arg(summary, idx, Some(projection.slice), callee_effect);
    } else {
        for idx in capture_ctx.arg_root_indices_for_observation(value) {
            merge_effect_into_arg(summary, idx, None, callee_effect);
        }
    }

    for (src_arg, src_slice) in capture_source_slices_for_slice_set(
        capture_sources,
        capture_ctx,
        value,
        &callee_effect.reads,
    ) {
        summary.arg_effects[src_arg].reads.add_slice(src_slice);
    }
    if callee_effect.needs_unknown_object_barrier() {
        let mut seen = FxHashSet::default();
        for (src_arg, _) in capture_source_slices(capture_sources, capture_ctx, value, None) {
            if !seen.insert(src_arg) {
                continue;
            }
            summary.arg_effects[src_arg].escapes |= callee_effect.escapes;
            summary.arg_effects[src_arg].materializes_stack |= callee_effect.materializes_stack;
            summary.arg_effects[src_arg].materializes_heap |= callee_effect.materializes_heap;
        }
    }
    kill_capture_slice_set(root_captures, capture_ctx, value, &callee_effect.writes);
}

fn merge_effect_into_arg(
    summary: &mut ObjectEffectSummary,
    idx: usize,
    base_slice: Option<shape::AggregateSlice>,
    callee_effect: &ObjectArgEffect,
) {
    let Some(arg_effect) = summary.arg_effects.get_mut(idx) else {
        return;
    };
    arg_effect.escapes |= callee_effect.escapes;
    arg_effect.materializes_stack |= callee_effect.materializes_stack;
    arg_effect.materializes_heap |= callee_effect.materializes_heap;
    map_into_slice_set(&mut arg_effect.reads, base_slice, &callee_effect.reads);
    map_into_slice_set(&mut arg_effect.writes, base_slice, &callee_effect.writes);
}

fn merge_call_capture_effects(
    function: &Function,
    inst: sonatina_ir::InstId,
    root_captures: &mut RootCaptureMap,
    capture_sources: &RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    call: &control_flow::Call,
    callee_captures: &[ObjectCaptureEffect],
) {
    let call_result = single_result_value(function, inst);
    for capture in callee_captures {
        let Some(&src_arg) = call.args().get(capture.src_arg) else {
            continue;
        };
        let src_slices = capture_source_slices(
            capture_sources,
            capture_ctx,
            src_arg,
            Some(capture.src_slice),
        );
        if src_slices.is_empty() {
            continue;
        }
        let dst_roots = match capture.dst {
            ObjectCaptureDestination::Arg { index, slice } => call
                .args()
                .get(index)
                .map(|&dst_arg| map_capture_slice_into_roots(capture_ctx, dst_arg, slice))
                .unwrap_or_default(),
            ObjectCaptureDestination::Return { slice } => call_result
                .map(|result| map_capture_slice_into_roots(capture_ctx, result, slice))
                .unwrap_or_default(),
        };
        record_root_capture_effects(root_captures, &dst_roots, &src_slices);
    }
}

fn record_capture(
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    object: ValueId,
    value: ValueId,
) {
    let dst_roots = value_root_slices(capture_ctx, object);
    if dst_roots.is_empty() {
        return;
    }
    let src_slices = capture_source_slices(root_captures, capture_ctx, value, None);
    if src_slices.is_empty() {
        return;
    }
    record_root_capture_effects(root_captures, &dst_roots, &src_slices);
}

fn record_enum_variant_captures(
    function: &Function,
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    object: ValueId,
    values: &[ValueId],
    variant: sonatina_ir::types::EnumVariantRef,
) {
    for (field_idx, &value) in values.iter().enumerate() {
        if objref_element_ty(function.ctx(), function.dfg.value_ty(value)).is_none() {
            continue;
        }
        let Some(field_slice) = shape::enum_variant_field_slice(
            function.ctx(),
            objref_element_ty(function.ctx(), function.dfg.value_ty(object))
                .expect("enum capture object should be an object ref"),
            variant,
            u32::try_from(field_idx).ok().unwrap_or(u32::MAX),
        ) else {
            continue;
        };
        let dst_roots = map_capture_slice_into_roots(capture_ctx, object, field_slice);
        if dst_roots.is_empty() {
            continue;
        }
        let src_slices = capture_source_slices(root_captures, capture_ctx, value, None);
        if src_slices.is_empty() {
            continue;
        }
        record_root_capture_effects(root_captures, &dst_roots, &src_slices);
    }
}

fn capture_source_slices(
    root_captures: &RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    value: ValueId,
    relative_slice: Option<shape::AggregateSlice>,
) -> Vec<(usize, shape::AggregateSlice)> {
    let mut src_slices = Vec::new();

    // Effect and capture propagation need a conservative may-touch view. Known
    // roots still matter even when provenance is incomplete; only planning and
    // return classification require the strict complete-only view.
    if let Some((root, access_slice)) =
        exact_capture_destination(capture_ctx.exact_projection(value), relative_slice)
    {
        if let Some(&idx) = capture_ctx.arg_roots.get(&root) {
            src_slices.push((idx, access_slice));
        }
        extend_capture_sources_for_root(&mut src_slices, root_captures, root, Some(access_slice));
        dedup_capture_source_slices(&mut src_slices);
        return src_slices;
    }

    for (root, slice) in capture_ctx.root_slices_for_observation(value) {
        if let Some(&idx) = capture_ctx.arg_roots.get(&root) {
            src_slices.push((idx, slice));
        }
        extend_capture_sources_for_root(&mut src_slices, root_captures, root, None);
    }

    dedup_capture_source_slices(&mut src_slices);
    src_slices
}

fn capture_source_slices_for_slice_set(
    root_captures: &RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    value: ValueId,
    slices: &SliceSet,
) -> Vec<(usize, shape::AggregateSlice)> {
    if slices.is_empty() {
        return Vec::new();
    }
    let Some(projection) = capture_ctx.exact_projection(value) else {
        return capture_source_slices(root_captures, capture_ctx, value, None);
    };
    if slices.is_whole_root() || projection.slice.leaf_count != slices.total_leaves() {
        return capture_source_slices(root_captures, capture_ctx, value, None);
    }
    let Some(exact_leaves) = slices.exact_leaves() else {
        return capture_source_slices(root_captures, capture_ctx, value, None);
    };

    let mut src_slices = Vec::new();
    for &leaf in exact_leaves {
        src_slices.extend(capture_source_slices(
            root_captures,
            capture_ctx,
            value,
            Some(shape::AggregateSlice {
                ty: projection.slice.ty,
                first_leaf: leaf,
                leaf_count: 1,
            }),
        ));
    }
    dedup_capture_source_slices(&mut src_slices);
    src_slices
}

fn extend_capture_sources_for_root(
    src_slices: &mut Vec<(usize, shape::AggregateSlice)>,
    root_captures: &RootCaptureMap,
    root: RootValue,
    access_slice: Option<shape::AggregateSlice>,
) {
    let Some(captures) = root_captures.get(&root) else {
        return;
    };
    for capture in captures {
        if let Some(access_slice) = access_slice
            && !slices_overlap_relative(access_slice, capture.dst_slice)
        {
            continue;
        }
        src_slices.push((capture.src_arg, capture.src_slice));
    }
}

fn dedup_capture_source_slices(src_slices: &mut Vec<(usize, shape::AggregateSlice)>) {
    let mut seen = FxHashSet::default();
    src_slices.retain(|source| seen.insert(*source));
}

fn same_slice_set(lhs: &[shape::AggregateSlice], rhs: &[shape::AggregateSlice]) -> bool {
    lhs.len() == rhs.len() && lhs.iter().all(|slice| rhs.contains(slice))
}

fn push_unique_slice(slices: &mut Vec<shape::AggregateSlice>, slice: shape::AggregateSlice) {
    if !slices.contains(&slice) {
        slices.push(slice);
    }
}

fn kill_capture_access(
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    object: ValueId,
    relative_slice: Option<(usize, usize)>,
) {
    let projection = capture_ctx.exact_projection(object);
    let relative_slice = relative_slice.and_then(|(first_leaf, leaf_count)| {
        projection.map(|projection| shape::AggregateSlice {
            ty: projection.slice.ty,
            first_leaf,
            leaf_count,
        })
    });
    kill_capture_projection_access(root_captures, projection, relative_slice);
}

fn kill_capture_slice_set(
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    value: ValueId,
    slices: &SliceSet,
) {
    kill_capture_exact_slice_set(
        root_captures,
        exact_capture_destination(capture_ctx.exact_projection(value), None),
        slices,
    );
}

fn value_root_slices(
    capture_ctx: EffectProvenance<'_>,
    value: ValueId,
) -> Vec<(RootValue, shape::AggregateSlice)> {
    capture_ctx.root_slices_for_observation(value).into_vec()
}

fn map_capture_slice_into_roots(
    capture_ctx: EffectProvenance<'_>,
    value: ValueId,
    slice: shape::AggregateSlice,
) -> Vec<(RootValue, shape::AggregateSlice)> {
    if let Some((root, mapped)) =
        exact_capture_destination(capture_ctx.exact_projection(value), Some(slice))
    {
        return vec![(root, mapped)];
    }

    value_root_slices(capture_ctx, value)
}

fn record_root_capture_effects(
    root_captures: &mut RootCaptureMap,
    dst_roots: &[(RootValue, shape::AggregateSlice)],
    src_slices: &[(usize, shape::AggregateSlice)],
) {
    for (root, dst_slice) in dst_roots {
        for (src_arg, src_slice) in src_slices {
            root_captures
                .entry(*root)
                .or_default()
                .push(RootCaptureEffect {
                    dst_slice: *dst_slice,
                    src_arg: *src_arg,
                    src_slice: *src_slice,
                });
        }
    }
}

fn push_capture_effect(summary: &mut ObjectEffectSummary, capture: ObjectCaptureEffect) {
    summary.captures.push(capture);
}

fn dedup_capture_effects(captures: &mut Vec<ObjectCaptureEffect>) {
    let mut seen = FxHashSet::default();
    captures.retain(|capture| seen.insert(*capture));
}

fn single_result_value(func: &Function, inst: sonatina_ir::InstId) -> Option<ValueId> {
    let [result] = func.dfg.inst_results(inst) else {
        return None;
    };
    Some(*result)
}

fn map_into_slice_set(
    dst: &mut SliceSet,
    base_slice: Option<shape::AggregateSlice>,
    src: &SliceSet,
) {
    if src.is_empty() {
        return;
    }
    let Some(base_slice) = base_slice else {
        dst.union_with(&SliceSet::whole_root(dst.total_leaves()));
        return;
    };
    if src.is_whole_root() || base_slice.leaf_count != src.total_leaves() {
        dst.add_slice(base_slice);
        return;
    }
    let Some(exact_leaves) = src.exact_leaves() else {
        dst.add_slice(base_slice);
        return;
    };
    for &leaf in exact_leaves {
        dst.add_slice(shape::AggregateSlice {
            ty: base_slice.ty,
            first_leaf: base_slice.first_leaf + leaf,
            leaf_count: 1,
        });
    }
}

fn record_read(
    summary: &mut ObjectEffectSummary,
    root_captures: &RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    object: ValueId,
) {
    record_slice_access(summary, capture_ctx, object, false, None);
    for (src_arg, src_slice) in capture_source_slices(root_captures, capture_ctx, object, None) {
        summary.arg_effects[src_arg].reads.add_slice(src_slice);
    }
}

fn record_write(
    summary: &mut ObjectEffectSummary,
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    object: ValueId,
) {
    kill_capture_access(root_captures, capture_ctx, object, None);
    record_slice_access(summary, capture_ctx, object, true, None);
}

fn record_enum_tag_read(
    summary: &mut ObjectEffectSummary,
    root_captures: &RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    object: ValueId,
) {
    record_slice_access(summary, capture_ctx, object, false, Some((0, 1)));
    let relative_slice =
        capture_ctx
            .exact_projection(object)
            .map(|projection| shape::AggregateSlice {
                ty: projection.slice.ty,
                first_leaf: 0,
                leaf_count: 1,
            });
    for (src_arg, src_slice) in
        capture_source_slices(root_captures, capture_ctx, object, relative_slice)
    {
        summary.arg_effects[src_arg].reads.add_slice(src_slice);
    }
}

fn record_enum_tag_write(
    summary: &mut ObjectEffectSummary,
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    object: ValueId,
) {
    kill_capture_access(root_captures, capture_ctx, object, Some((0, 1)));
    record_slice_access(summary, capture_ctx, object, true, Some((0, 1)));
}

fn record_enum_write_variant(
    function: &Function,
    summary: &mut ObjectEffectSummary,
    root_captures: &mut RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    object: ValueId,
    variant: sonatina_ir::types::EnumVariantRef,
    values: &[ValueId],
) {
    record_enum_tag_write(summary, root_captures, capture_ctx, object);
    kill_capture_access(root_captures, capture_ctx, object, None);
    if let Some(projection) = capture_ctx.exact_projection(object)
        && let Some(&idx) = capture_ctx.arg_roots.get(&projection.root_value)
    {
        for field_idx in 0..values.len() {
            let Some(field_slice) = shape::enum_variant_field_slice(
                function.ctx(),
                projection.slice.ty,
                variant,
                u32::try_from(field_idx).ok().unwrap_or(u32::MAX),
            ) else {
                continue;
            };
            summary.arg_effects[idx]
                .writes
                .add_slice(shape::AggregateSlice {
                    ty: field_slice.ty,
                    first_leaf: projection.slice.first_leaf + field_slice.first_leaf,
                    leaf_count: field_slice.leaf_count,
                });
        }
        record_enum_variant_captures(
            function,
            root_captures,
            capture_ctx,
            object,
            values,
            variant,
        );
        return;
    }
    for root_idx in capture_ctx.arg_root_indices_for_observation(object) {
        summary.arg_effects[root_idx].writes =
            SliceSet::whole_root(summary.arg_effects[root_idx].writes.total_leaves());
    }
    record_enum_variant_captures(
        function,
        root_captures,
        capture_ctx,
        object,
        values,
        variant,
    );
}

fn record_materialize(
    summary: &mut ObjectEffectSummary,
    root_captures: &RootCaptureMap,
    capture_ctx: EffectProvenance<'_>,
    object: ValueId,
    heap: bool,
) {
    for root_idx in capture_ctx.arg_root_indices_for_observation(object) {
        summary.arg_effects[root_idx].materializes_stack |= !heap;
        summary.arg_effects[root_idx].materializes_heap |= heap;
        summary.arg_effects[root_idx].escapes |= heap;
    }
    let mut seen = FxHashSet::default();
    for (src_arg, _) in capture_source_slices(root_captures, capture_ctx, object, None) {
        if !seen.insert(src_arg) {
            continue;
        }
        summary.arg_effects[src_arg].materializes_stack |= !heap;
        summary.arg_effects[src_arg].materializes_heap |= heap;
        summary.arg_effects[src_arg].escapes |= heap;
    }
}

fn record_slice_access(
    summary: &mut ObjectEffectSummary,
    effect_provenance: EffectProvenance<'_>,
    object: ValueId,
    write: bool,
    fixed_slice: Option<(usize, usize)>,
) {
    if let Some(projection) = effect_provenance.exact_projection(object)
        && let Some(&idx) = effect_provenance.arg_roots.get(&projection.root_value)
    {
        let slice = if let Some((first_leaf, leaf_count)) = fixed_slice {
            shape::AggregateSlice {
                ty: projection.slice.ty,
                first_leaf: projection.slice.first_leaf + first_leaf,
                leaf_count,
            }
        } else {
            projection.slice
        };
        if write {
            summary.arg_effects[idx].writes.add_slice(slice);
        } else {
            summary.arg_effects[idx].reads.add_slice(slice);
        }
        return;
    }

    for root_idx in effect_provenance.arg_root_indices_for_observation(object) {
        if write {
            summary.arg_effects[root_idx].writes =
                SliceSet::whole_root(summary.arg_effects[root_idx].writes.total_leaves());
        } else {
            summary.arg_effects[root_idx].reads =
                SliceSet::whole_root(summary.arg_effects[root_idx].reads.total_leaves());
        }
    }
}

pub(crate) fn is_fresh_root(function: &Function, value: ValueId) -> bool {
    let Some(inst) = function.dfg.value_inst(value) else {
        return false;
    };
    downcast::<&data::ObjAlloc>(function.inst_set(), function.dfg.inst(inst)).is_some()
        || downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst)).is_some()
}

pub(crate) fn objref_element_ty(module: &ModuleCtx, ty: Type) -> Option<Type> {
    match ty.resolve_compound(module)? {
        sonatina_ir::types::CompoundType::ObjRef(elem) => Some(elem),
        _ => None,
    }
}

pub(crate) fn whole_root_slice(
    layout_cache: &mut shape::AggregateLayoutCache,
    ctx: &ModuleCtx,
    pointee_ty: Type,
) -> shape::AggregateSlice {
    shape::AggregateSlice {
        ty: pointee_ty,
        first_leaf: 0,
        leaf_count: layout_cache
            .shape(ctx, pointee_ty)
            .map_or(1, |shape| shape.leaves.len()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::module::FuncRef;
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

    fn has_arg_capture(
        summary: &ObjectEffectSummary,
        dst_index: usize,
        dst_first_leaf: usize,
        dst_leaf_count: usize,
        src_arg: usize,
        src_first_leaf: usize,
        src_leaf_count: usize,
    ) -> bool {
        summary.captures.iter().any(|capture| {
            matches!(
                capture.dst,
                ObjectCaptureDestination::Arg { index, slice }
                    if index == dst_index
                        && slice.first_leaf == dst_first_leaf
                        && slice.leaf_count == dst_leaf_count
            ) && capture.src_arg == src_arg
                && capture.src_slice.first_leaf == src_first_leaf
                && capture.src_slice.leaf_count == src_leaf_count
        })
    }

    fn has_return_capture(
        summary: &ObjectEffectSummary,
        dst_first_leaf: usize,
        dst_leaf_count: usize,
        src_arg: usize,
        src_first_leaf: usize,
        src_leaf_count: usize,
    ) -> bool {
        summary.captures.iter().any(|capture| {
            matches!(
                capture.dst,
                ObjectCaptureDestination::Return { slice }
                    if slice.first_leaf == dst_first_leaf
                        && slice.leaf_count == dst_leaf_count
            ) && capture.src_arg == src_arg
                && capture.src_slice.first_leaf == src_first_leaf
                && capture.src_slice.leaf_count == src_leaf_count
        })
    }

    fn arg_reads_whole_root(summary: &ObjectEffectSummary, index: usize) -> bool {
        summary
            .arg_effects
            .get(index)
            .is_some_and(|effect| effect.reads.is_whole_root())
    }

    fn arg_writes_whole_root(summary: &ObjectEffectSummary, index: usize) -> bool {
        summary
            .arg_effects
            .get(index)
            .is_some_and(|effect| effect.writes.is_whole_root())
    }

    fn arg_reads_slice(
        summary: &ObjectEffectSummary,
        index: usize,
        first_leaf: usize,
        leaf_count: usize,
    ) -> bool {
        summary.arg_effects.get(index).is_some_and(|effect| {
            effect.reads.is_whole_root()
                || effect.reads.exact_leaves().is_some_and(|leaves| {
                    (first_leaf..first_leaf + leaf_count).all(|leaf| leaves.contains(&leaf))
                })
        })
    }

    fn arg_writes_exact_slice(
        summary: &ObjectEffectSummary,
        index: usize,
        first_leaf: usize,
        leaf_count: usize,
    ) -> bool {
        summary.arg_effects.get(index).is_some_and(|effect| {
            !effect.writes.is_whole_root()
                && effect.writes.exact_leaves().is_some_and(|leaves| {
                    (first_leaf..first_leaf + leaf_count).all(|leaf| leaves.contains(&leaf))
                })
        })
    }

    #[test]
    fn object_effects_propagates_acyclic_callee_slice_effects() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Pair = { i256, i256 };

func private %caller(v0.objref<@Pair>, v1.i256) {
block0:
    call %write_first v0 v1;
    return;
}

func private %write_first(v0.objref<@Pair>, v1.i256) {
block0:
    v2.objref<i256> = obj.proj v0 0.i8;
    obj.store v2 v1;
    return;
}
"#,
        );

        let caller = lookup_func(&module, "caller");
        let summary = compute_object_effect_summaries(&module)
            .remove(&caller)
            .expect("caller summary should exist");

        assert!(
            arg_writes_exact_slice(&summary, 0, 0, 1),
            "caller should inherit the callee's exact write slice"
        );
        assert!(
            !arg_writes_whole_root(&summary, 0),
            "acyclic callee propagation should not degrade exact writes to whole-root writes"
        );
    }

    #[test]
    fn object_effects_keeps_external_callee_conservative() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Pair = { i256, i256 };

declare external %touch(objref<@Pair>);

func private %caller(v0.objref<@Pair>) {
block0:
    call %touch v0;
    return;
}
"#,
        );

        let caller = lookup_func(&module, "caller");
        let summary = compute_object_effect_summaries(&module)
            .remove(&caller)
            .expect("caller summary should exist");

        assert!(arg_reads_whole_root(&summary, 0));
        assert!(arg_writes_whole_root(&summary, 0));
    }

    #[test]
    fn object_effects_keeps_recursive_scc_conservative() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Pair = { i256, i256 };

func private %a(v0.objref<@Pair>) {
block0:
    call %b v0;
    return;
}

func private %b(v0.objref<@Pair>) {
block0:
    call %a v0;
    return;
}
"#,
        );

        let summaries = compute_object_effect_summaries(&module);
        for name in ["a", "b"] {
            let func = lookup_func(&module, name);
            let summary = summaries
                .get(&func)
                .expect("recursive summary should exist");
            assert!(arg_reads_whole_root(summary, 0));
            assert!(arg_writes_whole_root(summary, 0));
        }
    }

    #[test]
    fn fresh_out_arg_capture_summary_tracks_source_slices() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Data = { i256, i256 };
type @LiveView = { objref<i256>, objref<i256> };

func private %make_view(v0.objref<@LiveView>, v1.objref<@Data>) {
block0:
    v2.objref<i256> = obj.proj v1 0.i8;
    v3.objref<objref<i256>> = obj.proj v0 0.i8;
    obj.store v3 v2;
    v4.objref<i256> = obj.proj v1 1.i8;
    v5.objref<objref<i256>> = obj.proj v0 1.i8;
    obj.store v5 v4;
    return;
}
"#,
        );

        let func_ref = lookup_func(&module, "make_view");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert!(
            has_arg_capture(&summary, 0, 0, 1, 1, 0, 1),
            "summary should record field-0 capture from the source arg"
        );
        assert!(
            has_arg_capture(&summary, 0, 1, 1, 1, 1, 1),
            "summary should record field-1 capture from the source arg"
        );
    }

    #[test]
    fn mixed_arg_and_unknown_phi_still_marks_arg_read() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Pair = { i256, i256 };

declare external %mystery() -> objref<@Pair>;

func private %read_maybe(v0.i1, v1.objref<@Pair>) -> i256 {
block0:
    br v0 block1 block2;

block1:
    jump block3;

block2:
    v2.objref<@Pair> = call %mystery;
    jump block3;

block3:
    v3.objref<@Pair> = phi (v1 block1) (v2 block2);
    v4.objref<i256> = obj.proj v3 0.i8;
    v5.i256 = obj.load v4;
    return v5;
}
"#,
        );

        let func_ref = lookup_func(&module, "read_maybe");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert!(
            arg_reads_whole_root(&summary, 1),
            "incomplete phi provenance should still conservatively mark arg reads"
        );
    }

    #[test]
    fn mixed_arg_and_unknown_phi_still_marks_arg_write() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Pair = { i256, i256 };

declare external %mystery() -> objref<@Pair>;

func private %write_maybe(v0.i1, v1.objref<@Pair>, v2.i256) {
block0:
    br v0 block1 block2;

block1:
    jump block3;

block2:
    v3.objref<@Pair> = call %mystery;
    jump block3;

block3:
    v4.objref<@Pair> = phi (v1 block1) (v3 block2);
    v5.objref<i256> = obj.proj v4 0.i8;
    obj.store v5 v2;
    return;
}
"#,
        );

        let func_ref = lookup_func(&module, "write_maybe");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert!(
            arg_writes_whole_root(&summary, 1),
            "incomplete phi provenance should still conservatively mark arg writes"
        );
    }

    #[test]
    fn capture_summary_propagates_through_helper_calls() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Data = { i256, i256 };
type @LiveView = { objref<i256>, objref<i256> };

func private %make_view(v0.objref<@LiveView>, v1.objref<@Data>) {
block0:
    v2.objref<i256> = obj.proj v1 0.i8;
    v3.objref<objref<i256>> = obj.proj v0 0.i8;
    obj.store v3 v2;
    return;
}

func private %mid(v0.objref<@LiveView>, v1.objref<@Data>) {
block0:
    call %make_view v0 v1;
    return;
}
"#,
        );

        let func_ref = lookup_func(&module, "mid");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");
        assert!(
            has_arg_capture(&summary, 0, 0, 1, 1, 0, 1),
            "transitive helper summary should preserve capture relations"
        );
    }

    #[test]
    fn inexact_fresh_call_roots_still_propagate_captured_reads() {
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

func private %read_two_calls(v0.i1, v1.objref<@Cell>) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.objref<@Take> = call %take v1;
    jump block3;

block2:
    v3.objref<@Take> = call %take v1;
    jump block3;

block3:
    v4.objref<@Take> = phi (v2 block1) (v3 block2);
    v5.objref<objref<i256>> = obj.proj v4 0.i8;
    v6.objref<i256> = obj.load v5;
    v7.i256 = obj.load v6;
    return v7;
}
"#,
        );

        let func_ref = lookup_func(&module, "read_two_calls");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert!(
            arg_reads_slice(&summary, 1, 0, 1),
            "fresh helper call roots merged through an inexact phi should still propagate arg reads"
        );
    }

    #[test]
    fn weak_update_through_multi_root_phi_preserves_prior_capture_reads() {
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

func private %read_preserved(v0.i1, v1.objref<@Cell>, v2.objref<@Cell>) -> i256 {
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
    v10.i256 = obj.load v9;
    return v10;
}
"#,
        );

        let func_ref = lookup_func(&module, "read_preserved");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert!(
            arg_reads_slice(&summary, 1, 0, 1),
            "weak updates through multi-root destinations must preserve prior captured reads"
        );
    }

    #[test]
    fn unknown_capture_target_does_not_clear_prior_capture_reads() {
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

func private %read_preserved(v0.i1, v1.objref<@Cell>, v2.objref<@Cell>) -> i256 {
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
    v10.i256 = obj.load v9;
    return v10;
}
"#,
        );

        let func_ref = lookup_func(&module, "read_preserved");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert!(
            arg_reads_slice(&summary, 1, 0, 1),
            "unknown write targets must not clear prior captured reads on known roots"
        );
    }

    #[test]
    fn same_root_ambiguous_store_preserves_prior_capture_reads() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Cell = { i256 };
type @Pair = { objref<i256>, objref<i256> };

func private %read_preserved(v0.i1, v1.objref<@Cell>, v2.objref<@Cell>) -> i256 {
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
    v12.i256 = obj.load v11;
    return v12;
}
"#,
        );

        let func_ref = lookup_func(&module, "read_preserved");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert!(
            arg_reads_slice(&summary, 1, 0, 1),
            "same-root ambiguous stores must remain weak updates for capture propagation"
        );
    }

    #[test]
    fn capture_summary_preserves_branch_local_capture_reads() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Data = { i256, i256 };
type @Holder = { objref<i256> };

func private %branch_read(v0.objref<@Holder>, v1.objref<@Data>, v2.i1) {
block0:
    br v2 block1 block2;

block1:
    v3.objref<i256> = obj.proj v1 0.i8;
    v4.objref<objref<i256>> = obj.proj v0 0.i8;
    obj.store v4 v3;
    jump block3;

block2:
    v5.objref<i256> = obj.alloc i256;
    v6.objref<objref<i256>> = obj.proj v0 0.i8;
    obj.store v6 v5;
    jump block3;

block3:
    v7.objref<objref<i256>> = obj.proj v0 0.i8;
    v8.objref<i256> = obj.load v7;
    v9.i256 = obj.load v8;
    return;
}
"#,
        );

        let func_ref = lookup_func(&module, "branch_read");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");
        assert!(
            arg_reads_slice(&summary, 1, 0, 1),
            "merge-block read should preserve captures from the non-overwriting predecessor"
        );
    }

    #[test]
    fn capture_summary_uses_pre_call_capture_snapshot_for_aliased_args() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Data = { i256, i256 };
type @Holder = { objref<i256> };

func private %callee(v0.objref<@Holder>, v1.objref<@Holder>) {
block0:
    v2.objref<objref<i256>> = obj.proj v1 0.i8;
    v3.objref<i256> = obj.load v2;
    v4.i256 = obj.load v3;
    v5.objref<i256> = obj.alloc i256;
    v6.objref<objref<i256>> = obj.proj v0 0.i8;
    obj.store v6 v5;
    return;
}

func private %caller(v0.objref<@Holder>, v1.objref<@Data>) {
block0:
    v2.objref<i256> = obj.proj v1 0.i8;
    v3.objref<objref<i256>> = obj.proj v0 0.i8;
    obj.store v3 v2;
    call %callee v0 v0;
    return;
}
"#,
        );

        let func_ref = lookup_func(&module, "caller");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");
        assert!(
            arg_reads_slice(&summary, 1, 0, 1),
            "aliased call args should read captured sources from the pre-call state"
        );
    }

    #[test]
    fn capture_summary_widens_same_root_phi_sources_to_whole_root() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Data = { i256, i256 };
type @Cell = { objref<i256> };

func private %capture(v0.objref<@Cell>, v1.objref<i256>) {
block0:
    v2.objref<objref<i256>> = obj.proj v0 0.i8;
    obj.store v2 v1;
    return;
}

func private %mid(v0.objref<@Cell>, v1.objref<@Data>, v2.i1) {
block0:
    br v2 block1 block2;

block1:
    v3.objref<i256> = obj.proj v1 0.i8;
    jump block3;

block2:
    v4.objref<i256> = obj.proj v1 1.i8;
    jump block3;

block3:
    v5.objref<i256> = phi (v3 block1) (v4 block2);
    call %capture v0 v5;
    return;
}
"#,
        );

        let func_ref = lookup_func(&module, "mid");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");
        assert!(
            has_arg_capture(&summary, 0, 0, 1, 1, 0, 2),
            "same-root phi capture should conservatively widen to the whole source root"
        );
    }

    #[test]
    fn return_capture_summary_tracks_returned_root_slices() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Take = { i256, objref<[i256; 8]> };

func private %take(v0.i256, v1.objref<[i256; 8]>) -> objref<@Take> {
block0:
    v2.objref<@Take> = obj.alloc @Take;
    v3.objref<i256> = obj.proj v2 0.i8;
    obj.store v3 v0;
    v4.objref<objref<[i256; 8]>> = obj.proj v2 1.i8;
    obj.store v4 v1;
    return v2;
}
"#,
        );

        let func_ref = lookup_func(&module, "take");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert_eq!(summary.ret_effect, ObjectReturnEffect::FreshObject);
        assert!(
            has_return_capture(&summary, 1, 1, 1, 0, 8),
            "returned object field should preserve the captured source root"
        );
    }

    #[test]
    fn return_capture_summary_propagates_through_forwarding_call() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Take = { i256, objref<[i256; 8]> };

func private %take(v0.i256, v1.objref<[i256; 8]>) -> objref<@Take> {
block0:
    v2.objref<@Take> = obj.alloc @Take;
    v3.objref<i256> = obj.proj v2 0.i8;
    obj.store v3 v0;
    v4.objref<objref<[i256; 8]>> = obj.proj v2 1.i8;
    obj.store v4 v1;
    return v2;
}

func private %mid(v0.objref<[i256; 8]>) -> objref<@Take> {
block0:
    v1.objref<@Take> = call %take 4.i256 v0;
    return v1;
}
"#,
        );

        let func_ref = lookup_func(&module, "mid");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert_eq!(summary.ret_effect, ObjectReturnEffect::FreshObject);
        assert!(
            has_return_capture(&summary, 1, 1, 0, 0, 8),
            "forwarding helper should preserve returned capture relations"
        );
    }

    #[test]
    fn dead_exit_does_not_contribute_return_captures() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Take = { objref<[i256; 8]> };

func private %f(v0.objref<[i256; 8]>, v1.objref<@Take>) -> objref<@Take> {
block0:
    return v1;

block1:
    v2.objref<@Take> = obj.alloc @Take;
    v3.objref<objref<[i256; 8]>> = obj.proj v2 0.i8;
    obj.store v3 v0;
    return v2;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert_eq!(
            summary.ret_effect,
            ObjectReturnEffect::SameAsArg { index: 1 }
        );
        assert!(
            summary.captures.is_empty(),
            "dead return exits must not contribute capture summaries"
        );
    }

    #[test]
    fn return_capture_summary_propagates_into_returned_local_out_arg() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Data = { i256, i256 };
type @LiveView = { objref<i256>, objref<i256> };

func private %make_view(v0.objref<@LiveView>, v1.objref<@Data>) {
block0:
    v2.objref<i256> = obj.proj v1 0.i8;
    v3.objref<objref<i256>> = obj.proj v0 0.i8;
    obj.store v3 v2;
    v4.objref<i256> = obj.proj v1 1.i8;
    v5.objref<objref<i256>> = obj.proj v0 1.i8;
    obj.store v5 v4;
    return;
}

func private %wrap(v0.objref<@Data>) -> objref<@LiveView> {
block0:
    v1.objref<@LiveView> = obj.alloc @LiveView;
    call %make_view v1 v0;
    return v1;
}
"#,
        );

        let func_ref = lookup_func(&module, "wrap");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert_eq!(summary.ret_effect, ObjectReturnEffect::FreshObject);
        assert!(
            has_return_capture(&summary, 0, 1, 0, 0, 1),
            "returned local out-arg field 0 should preserve source field 0"
        );
        assert!(
            has_return_capture(&summary, 1, 1, 0, 1, 1),
            "returned local out-arg field 1 should preserve source field 1"
        );
    }

    #[test]
    fn return_capture_summary_preserves_shared_relative_slice_across_same_root_phi() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Cell = { i256 };
type @Inner = { objref<i256>, i256 };
type @Outer = { @Inner, @Inner };

func private %pick(v0.i1, v1.objref<@Cell>) -> objref<@Inner> {
block0:
    v2.objref<@Outer> = obj.alloc @Outer;
    br v0 block1 block2;

block1:
    v3.objref<@Inner> = obj.proj v2 0.i8;
    v4.objref<objref<i256>> = obj.proj v3 0.i8;
    v5.objref<i256> = obj.proj v1 0.i8;
    obj.store v4 v5;
    jump block3;

block2:
    v6.objref<@Inner> = obj.proj v2 1.i8;
    v7.objref<objref<i256>> = obj.proj v6 0.i8;
    v8.objref<i256> = obj.proj v1 0.i8;
    obj.store v7 v8;
    jump block3;

block3:
    v9.objref<@Inner> = phi (v3 block1) (v6 block2);
    return v9;
}
"#,
        );

        let func_ref = lookup_func(&module, "pick");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert_eq!(summary.ret_effect, ObjectReturnEffect::FreshObject);
        assert!(
            has_return_capture(&summary, 0, 1, 1, 0, 1),
            "matching same-root return candidates should keep a precise return capture"
        );
    }

    #[test]
    fn fresh_multi_root_phi_return_is_fresh_object() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Pair = { i256, i256 };

func private %pick(v0.i1, v1.i256, v2.i256) -> objref<@Pair> {
block0:
    br v0 block1 block2;

block1:
    v3.objref<@Pair> = obj.alloc @Pair;
    v4.objref<i256> = obj.proj v3 0.i8;
    obj.store v4 v1;
    jump block3;

block2:
    v5.objref<@Pair> = obj.alloc @Pair;
    v6.objref<i256> = obj.proj v5 0.i8;
    obj.store v6 v2;
    jump block3;

block3:
    v7.objref<@Pair> = phi (v3 block1) (v5 block2);
    return v7;
}
"#,
        );

        let func_ref = lookup_func(&module, "pick");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert_eq!(summary.ret_effect, ObjectReturnEffect::FreshObject);
    }

    #[test]
    fn mixed_fresh_and_arg_root_phi_return_stays_unknown() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Pair = { i256, i256 };

func private %pick(v0.i1, v1.objref<@Pair>, v2.i256) -> objref<@Pair> {
block0:
    br v0 block1 block2;

block1:
    v3.objref<@Pair> = obj.alloc @Pair;
    v4.objref<i256> = obj.proj v3 0.i8;
    obj.store v4 v2;
    jump block3;

block2:
    jump block3;

block3:
    v5.objref<@Pair> = phi (v3 block1) (v1 block2);
    return v5;
}
"#,
        );

        let func_ref = lookup_func(&module, "pick");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert_eq!(summary.ret_effect, ObjectReturnEffect::Unknown);
    }

    #[test]
    fn return_capture_summary_survives_fresh_multi_root_phi() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Cell = { i256 };
type @Take = { objref<i256>, i256 };

func private %pick(v0.i1, v1.objref<@Cell>) -> objref<@Take> {
block0:
    br v0 block1 block2;

block1:
    v2.objref<@Take> = obj.alloc @Take;
    v3.objref<objref<i256>> = obj.proj v2 0.i8;
    v4.objref<i256> = obj.proj v1 0.i8;
    obj.store v3 v4;
    jump block3;

block2:
    v5.objref<@Take> = obj.alloc @Take;
    v6.objref<objref<i256>> = obj.proj v5 0.i8;
    v7.objref<i256> = obj.proj v1 0.i8;
    obj.store v6 v7;
    jump block3;

block3:
    v8.objref<@Take> = phi (v2 block1) (v5 block2);
    return v8;
}
"#,
        );

        let func_ref = lookup_func(&module, "pick");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert_eq!(summary.ret_effect, ObjectReturnEffect::FreshObject);
        assert!(
            has_return_capture(&summary, 0, 1, 1, 0, 1),
            "multi-root fresh phi return should preserve the shared capture"
        );
    }

    #[test]
    fn return_capture_summary_widens_disagreeing_same_root_phi_to_whole_return() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Cell = { i256 };
type @Inner = { objref<i256>, objref<i256> };
type @Outer = { @Inner, @Inner };

func private %pick(v0.i1, v1.objref<@Cell>) -> objref<@Inner> {
block0:
    v2.objref<@Outer> = obj.alloc @Outer;
    br v0 block1 block2;

block1:
    v3.objref<@Inner> = obj.proj v2 0.i8;
    v4.objref<objref<i256>> = obj.proj v3 1.i8;
    v5.objref<i256> = obj.proj v1 0.i8;
    obj.store v4 v5;
    jump block3;

block2:
    v6.objref<@Inner> = obj.proj v2 1.i8;
    v7.objref<objref<i256>> = obj.proj v6 0.i8;
    v8.objref<i256> = obj.proj v1 0.i8;
    obj.store v7 v8;
    jump block3;

block3:
    v9.objref<@Inner> = phi (v3 block1) (v6 block2);
    return v9;
}
"#,
        );

        let func_ref = lookup_func(&module, "pick");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert_eq!(summary.ret_effect, ObjectReturnEffect::FreshObject);
        assert!(
            has_return_capture(&summary, 0, 2, 1, 0, 1),
            "disagreeing same-root return candidates should widen to the whole returned object"
        );
        assert!(
            !has_return_capture(&summary, 0, 1, 1, 0, 1),
            "ambiguous same-root return should not invent a precise field-0 capture"
        );
        assert!(
            !has_return_capture(&summary, 1, 1, 1, 0, 1),
            "ambiguous same-root return should not invent a precise field-1 capture"
        );
    }

    #[test]
    fn capture_summary_propagates_reads_through_local_returned_roots() {
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
"#,
        );

        let func_ref = lookup_func(&module, "sum_last4");
        let summary = compute_object_effect_summaries(&module)
            .remove(&func_ref)
            .expect("summary should exist");

        assert!(
            arg_reads_whole_root(&summary, 0),
            "reading through the returned local object should keep the source arg live"
        );
    }
}
