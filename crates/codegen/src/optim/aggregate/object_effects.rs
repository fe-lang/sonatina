use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, Module, Type, ValueId,
    inst::{control_flow, data, downcast},
    module::{FuncRef, ModuleCtx},
};

use super::{collect_root_provenance, shape};

const MAX_EXACT_EFFECT_LEAVES: usize = 64;

pub(crate) type ObjectEffectSummaryMap = FxHashMap<FuncRef, ObjectEffectSummary>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ObjectEffectSummary {
    pub arg_effects: Vec<ObjectArgEffect>,
    pub captures: Vec<ObjectCaptureEffect>,
    pub ret_effect: ObjectReturnEffect,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ObjectCaptureEffect {
    pub dst_arg: usize,
    pub dst_slice: shape::AggregateSlice,
    pub src_arg: usize,
    pub src_slice: shape::AggregateSlice,
}

#[derive(Clone, Copy)]
struct CaptureContext<'a> {
    root_slices: &'a FxHashMap<ValueId, shape::AggregateSlice>,
    arg_roots: &'a FxHashMap<ValueId, usize>,
    provenance: &'a super::provenance::RootProvenanceMap,
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
    let mut funcs: Vec<_> = module.funcs();
    funcs.sort_unstable_by_key(|func| func.as_u32());

    loop {
        let mut changed = false;
        for func in funcs.iter().copied() {
            let Some(sig) = module.ctx.get_sig(func) else {
                continue;
            };
            if !sig.linkage().has_definition() {
                continue;
            }

            let next = compute_summary_for_func(module, func, &summaries, &mut layout_cache);
            if summaries.get(&func) != Some(&next) {
                summaries.insert(func, next);
                changed = true;
            }
        }

        if !changed {
            return summaries;
        }
    }
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
            arg_roots.insert(arg, idx);
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

        let provenance = collect_root_provenance(
            function,
            function.ctx(),
            &root_slices,
            layout_cache,
            Some(summaries),
        );
        let capture_ctx = CaptureContext {
            root_slices: &root_slices,
            arg_roots: &arg_roots,
            provenance: &provenance,
        };

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                if !function.layout.is_inst_inserted(inst) {
                    continue;
                }

                if let Some(obj_load) =
                    downcast::<&data::ObjLoad>(function.inst_set(), function.dfg.inst(inst))
                {
                    record_read(&mut summary, &arg_roots, &provenance, *obj_load.object());
                    continue;
                }

                if let Some(enum_get_tag) =
                    downcast::<&data::EnumGetTag>(function.inst_set(), function.dfg.inst(inst))
                {
                    record_enum_tag_read(
                        &mut summary,
                        &arg_roots,
                        &provenance,
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
                        &arg_roots,
                        &provenance,
                        *enum_assert_ref.object(),
                    );
                    continue;
                }

                if let Some(obj_store) =
                    downcast::<&data::ObjStore>(function.inst_set(), function.dfg.inst(inst))
                {
                    record_write(&mut summary, &arg_roots, &provenance, *obj_store.object());
                    record_capture(
                        &mut summary,
                        capture_ctx,
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
                        &arg_roots,
                        &provenance,
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
                        capture_ctx,
                        *enum_write_variant.object(),
                        *enum_write_variant.variant(),
                        enum_write_variant.values(),
                        enum_write_variant.values().len(),
                    );
                    continue;
                }

                if let Some(mat_stack) = downcast::<&data::ObjMaterializeStack>(
                    function.inst_set(),
                    function.dfg.inst(inst),
                ) {
                    record_materialize(
                        &mut summary,
                        &arg_roots,
                        &provenance,
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
                        &arg_roots,
                        &provenance,
                        *mat_heap.object(),
                        true,
                    );
                    continue;
                }

                if let Some(call) =
                    downcast::<&control_flow::Call>(function.inst_set(), function.dfg.inst(inst))
                {
                    merge_call_effects(
                        function,
                        &mut summary,
                        capture_ctx,
                        call,
                        summaries,
                        layout_cache,
                    );
                }
            }
        }

        dedup_capture_effects(&mut summary.captures);
        summary.ret_effect =
            classify_return_effect(function, &arg_roots, &root_slices, &provenance);
        for idx in 0..summary.arg_effects.len() {
            summary.arg_effects[idx].local_only = !summary.arg_effects[idx].escapes
                && !summary.arg_effects[idx].materializes_heap
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

fn classify_return_effect(
    function: &Function,
    arg_roots: &FxHashMap<ValueId, usize>,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
    provenance: &super::provenance::RootProvenanceMap,
) -> ObjectReturnEffect {
    let mut combined = ReturnClass::None;
    let mut saw_return = false;

    for block in function.layout.iter_block() {
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
            combined = join_return_class(
                combined,
                classify_return_value(function, value, arg_roots, root_slices, provenance),
            );
        }
    }

    if !saw_return {
        return ObjectReturnEffect::None;
    }

    match combined {
        ReturnClass::None => ObjectReturnEffect::None,
        ReturnClass::FreshObject => ObjectReturnEffect::FreshObject,
        ReturnClass::SameAsArg(index) => ObjectReturnEffect::SameAsArg { index },
        ReturnClass::DerivedFromArg(index) => ObjectReturnEffect::DerivedFromArg { index },
        ReturnClass::Unknown => ObjectReturnEffect::Unknown,
    }
}

fn classify_return_value(
    function: &Function,
    value: ValueId,
    arg_roots: &FxHashMap<ValueId, usize>,
    root_slices: &FxHashMap<ValueId, shape::AggregateSlice>,
    provenance: &super::provenance::RootProvenanceMap,
) -> ReturnClass {
    if objref_element_ty(function.ctx(), function.dfg.value_ty(value)).is_none() {
        return ReturnClass::None;
    }

    if let Some(projection) = provenance.exact_projection(value) {
        if let Some(&idx) = arg_roots.get(&projection.root_value) {
            return if root_slices.get(&projection.root_value) == Some(&projection.slice) {
                ReturnClass::SameAsArg(idx)
            } else {
                ReturnClass::DerivedFromArg(idx)
            };
        }
        return if is_fresh_root(function, projection.root_value) {
            ReturnClass::FreshObject
        } else {
            ReturnClass::Unknown
        };
    }

    match provenance.provenance(value) {
        super::RootProvenance::SameRoot(root) => {
            if let Some(&idx) = arg_roots.get(&root) {
                ReturnClass::DerivedFromArg(idx)
            } else if is_fresh_root(function, root) {
                ReturnClass::FreshObject
            } else {
                ReturnClass::Unknown
            }
        }
        super::RootProvenance::Exact(_)
        | super::RootProvenance::Maybe(_)
        | super::RootProvenance::Unknown => ReturnClass::Unknown,
    }
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

fn merge_call_effects(
    function: &Function,
    summary: &mut ObjectEffectSummary,
    capture_ctx: CaptureContext<'_>,
    call: &control_flow::Call,
    summaries: &ObjectEffectSummaryMap,
    layout_cache: &mut shape::AggregateLayoutCache,
) {
    let callee_summary = summaries.get(call.callee()).cloned().unwrap_or_else(|| {
        ObjectEffectSummary::conservative_unknown(function.ctx(), *call.callee(), layout_cache)
    });

    for (callee_idx, &arg) in call.args().iter().enumerate() {
        let Some(callee_effect) = callee_summary.arg_effects.get(callee_idx) else {
            continue;
        };
        merge_call_arg_effect(
            summary,
            capture_ctx.arg_roots,
            capture_ctx.provenance,
            arg,
            callee_effect,
        );
    }
    merge_call_capture_effects(summary, capture_ctx, call, &callee_summary.captures);
}

fn merge_call_arg_effect(
    summary: &mut ObjectEffectSummary,
    arg_roots: &FxHashMap<ValueId, usize>,
    provenance: &super::provenance::RootProvenanceMap,
    value: ValueId,
    callee_effect: &ObjectArgEffect,
) {
    if callee_effect.reads.is_empty()
        && callee_effect.writes.is_empty()
        && !callee_effect.escapes
        && !callee_effect.materializes_stack
        && !callee_effect.materializes_heap
    {
        return;
    }

    if let Some(projection) = provenance.exact_projection(value)
        && let Some(&idx) = arg_roots.get(&projection.root_value)
    {
        merge_effect_into_arg(summary, idx, Some(projection.slice), callee_effect);
        return;
    }

    match provenance.provenance(value) {
        super::RootProvenance::SameRoot(root) => {
            if let Some(&idx) = arg_roots.get(&root) {
                merge_effect_into_arg(summary, idx, None, callee_effect);
            }
        }
        super::RootProvenance::Maybe(roots) => {
            for root in roots {
                if let Some(&idx) = arg_roots.get(&root) {
                    merge_effect_into_arg(summary, idx, None, callee_effect);
                }
            }
        }
        super::RootProvenance::Exact(_) | super::RootProvenance::Unknown => {}
    }
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
    summary: &mut ObjectEffectSummary,
    capture_ctx: CaptureContext<'_>,
    call: &control_flow::Call,
    callee_captures: &[ObjectCaptureEffect],
) {
    for capture in callee_captures {
        let Some(&dst_arg) = call.args().get(capture.dst_arg) else {
            continue;
        };
        let Some(&src_arg) = call.args().get(capture.src_arg) else {
            continue;
        };
        let dst_slices = map_capture_slice_into_arg_slices(capture_ctx, dst_arg, capture.dst_slice);
        let src_slices = map_capture_slice_into_arg_slices(capture_ctx, src_arg, capture.src_slice);

        for (dst_idx, dst_slice) in &dst_slices {
            for (src_idx, src_slice) in &src_slices {
                push_capture_effect(
                    summary,
                    ObjectCaptureEffect {
                        dst_arg: *dst_idx,
                        dst_slice: *dst_slice,
                        src_arg: *src_idx,
                        src_slice: *src_slice,
                    },
                );
            }
        }
    }
}

fn record_capture(
    summary: &mut ObjectEffectSummary,
    capture_ctx: CaptureContext<'_>,
    object: ValueId,
    value: ValueId,
) {
    let dst_slices = capture_arg_slices(capture_ctx, object);
    if dst_slices.is_empty() {
        return;
    }
    let src_slices = capture_arg_slices(capture_ctx, value);
    if src_slices.is_empty() {
        return;
    }

    for (dst_arg, dst_slice) in &dst_slices {
        for (src_arg, src_slice) in &src_slices {
            push_capture_effect(
                summary,
                ObjectCaptureEffect {
                    dst_arg: *dst_arg,
                    dst_slice: *dst_slice,
                    src_arg: *src_arg,
                    src_slice: *src_slice,
                },
            );
        }
    }
}

fn record_enum_variant_captures(
    function: &Function,
    summary: &mut ObjectEffectSummary,
    capture_ctx: CaptureContext<'_>,
    dst_arg: usize,
    base_slice: shape::AggregateSlice,
    values: &[ValueId],
    variant: sonatina_ir::types::EnumVariantRef,
) {
    for (field_idx, &value) in values.iter().enumerate() {
        if objref_element_ty(function.ctx(), function.dfg.value_ty(value)).is_none() {
            continue;
        }
        let Some(field_slice) = shape::enum_variant_field_slice(
            function.ctx(),
            base_slice.ty,
            variant,
            u32::try_from(field_idx).ok().unwrap_or(u32::MAX),
        ) else {
            continue;
        };
        let src_slices = capture_arg_slices(capture_ctx, value);
        if src_slices.is_empty() {
            continue;
        }
        let dst_slice = shape::AggregateSlice {
            ty: field_slice.ty,
            first_leaf: base_slice.first_leaf + field_slice.first_leaf,
            leaf_count: field_slice.leaf_count,
        };
        for (src_arg, src_slice) in &src_slices {
            push_capture_effect(
                summary,
                ObjectCaptureEffect {
                    dst_arg,
                    dst_slice,
                    src_arg: *src_arg,
                    src_slice: *src_slice,
                },
            );
        }
    }
}

fn record_enum_variant_captures_from_roots(
    function: &Function,
    summary: &mut ObjectEffectSummary,
    capture_ctx: CaptureContext<'_>,
    object: ValueId,
    values: &[ValueId],
    variant: sonatina_ir::types::EnumVariantRef,
) {
    for (field_idx, &value) in values.iter().enumerate() {
        if objref_element_ty(function.ctx(), function.dfg.value_ty(value)).is_none() {
            continue;
        }
        let mut dst_slices = Vec::new();
        for (root_idx, root_slice) in capture_arg_slices(capture_ctx, object) {
            let Some(field_slice) = shape::enum_variant_field_slice(
                function.ctx(),
                root_slice.ty,
                variant,
                u32::try_from(field_idx).ok().unwrap_or(u32::MAX),
            ) else {
                continue;
            };
            dst_slices.push((
                root_idx,
                shape::AggregateSlice {
                    ty: field_slice.ty,
                    first_leaf: root_slice.first_leaf + field_slice.first_leaf,
                    leaf_count: field_slice.leaf_count,
                },
            ));
        }
        if dst_slices.is_empty() {
            continue;
        }
        let src_slices = capture_arg_slices(capture_ctx, value);
        if src_slices.is_empty() {
            continue;
        }

        for (dst_arg, dst_slice) in &dst_slices {
            for (src_arg, src_slice) in &src_slices {
                push_capture_effect(
                    summary,
                    ObjectCaptureEffect {
                        dst_arg: *dst_arg,
                        dst_slice: *dst_slice,
                        src_arg: *src_arg,
                        src_slice: *src_slice,
                    },
                );
            }
        }
    }
}

fn capture_arg_slices(
    capture_ctx: CaptureContext<'_>,
    value: ValueId,
) -> Vec<(usize, shape::AggregateSlice)> {
    if let Some(projection) = capture_ctx.provenance.exact_projection(value)
        && let Some(&idx) = capture_ctx.arg_roots.get(&projection.root_value)
    {
        return vec![(idx, projection.slice)];
    }

    match capture_ctx.provenance.provenance(value) {
        super::RootProvenance::SameRoot(root) => capture_ctx
            .arg_roots
            .get(&root)
            .and_then(|&idx| {
                capture_ctx
                    .root_slices
                    .get(&root)
                    .copied()
                    .map(|slice| (idx, slice))
            })
            .into_iter()
            .collect(),
        super::RootProvenance::Maybe(roots) => roots
            .into_iter()
            .filter_map(|root| {
                capture_ctx.arg_roots.get(&root).and_then(|&idx| {
                    capture_ctx
                        .root_slices
                        .get(&root)
                        .copied()
                        .map(|slice| (idx, slice))
                })
            })
            .collect(),
        super::RootProvenance::Exact(_) | super::RootProvenance::Unknown => Vec::new(),
    }
}

fn map_capture_slice_into_arg_slices(
    capture_ctx: CaptureContext<'_>,
    value: ValueId,
    slice: shape::AggregateSlice,
) -> Vec<(usize, shape::AggregateSlice)> {
    if let Some(projection) = capture_ctx.provenance.exact_projection(value)
        && let Some(&idx) = capture_ctx.arg_roots.get(&projection.root_value)
    {
        return offset_slice(projection.slice, slice)
            .map(|mapped| vec![(idx, mapped)])
            .unwrap_or_default();
    }

    capture_arg_slices(capture_ctx, value)
}

fn offset_slice(
    base_slice: shape::AggregateSlice,
    relative: shape::AggregateSlice,
) -> Option<shape::AggregateSlice> {
    (relative.first_leaf + relative.leaf_count <= base_slice.leaf_count).then_some(
        shape::AggregateSlice {
            ty: relative.ty,
            first_leaf: base_slice.first_leaf + relative.first_leaf,
            leaf_count: relative.leaf_count,
        },
    )
}

fn push_capture_effect(summary: &mut ObjectEffectSummary, capture: ObjectCaptureEffect) {
    summary.captures.push(capture);
}

fn dedup_capture_effects(captures: &mut Vec<ObjectCaptureEffect>) {
    let mut seen = FxHashSet::default();
    captures.retain(|capture| seen.insert(*capture));
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
    arg_roots: &FxHashMap<ValueId, usize>,
    provenance: &super::provenance::RootProvenanceMap,
    object: ValueId,
) {
    record_slice_access(summary, arg_roots, provenance, object, false, None);
}

fn record_write(
    summary: &mut ObjectEffectSummary,
    arg_roots: &FxHashMap<ValueId, usize>,
    provenance: &super::provenance::RootProvenanceMap,
    object: ValueId,
) {
    record_slice_access(summary, arg_roots, provenance, object, true, None);
}

fn record_enum_tag_read(
    summary: &mut ObjectEffectSummary,
    arg_roots: &FxHashMap<ValueId, usize>,
    provenance: &super::provenance::RootProvenanceMap,
    object: ValueId,
) {
    record_slice_access(summary, arg_roots, provenance, object, false, Some((0, 1)));
}

fn record_enum_tag_write(
    summary: &mut ObjectEffectSummary,
    arg_roots: &FxHashMap<ValueId, usize>,
    provenance: &super::provenance::RootProvenanceMap,
    object: ValueId,
) {
    record_slice_access(summary, arg_roots, provenance, object, true, Some((0, 1)));
}

fn record_enum_write_variant(
    function: &Function,
    summary: &mut ObjectEffectSummary,
    capture_ctx: CaptureContext<'_>,
    object: ValueId,
    variant: sonatina_ir::types::EnumVariantRef,
    values: &[ValueId],
    payload_len: usize,
) {
    record_enum_tag_write(
        summary,
        capture_ctx.arg_roots,
        capture_ctx.provenance,
        object,
    );
    if let Some(projection) = capture_ctx.provenance.exact_projection(object)
        && let Some(&idx) = capture_ctx.arg_roots.get(&projection.root_value)
    {
        for field_idx in 0..payload_len {
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
            summary,
            capture_ctx,
            idx,
            projection.slice,
            values,
            variant,
        );
        return;
    }
    for root_idx in root_arg_indices(capture_ctx.arg_roots, capture_ctx.provenance, object) {
        summary.arg_effects[root_idx].writes =
            SliceSet::whole_root(summary.arg_effects[root_idx].writes.total_leaves());
    }
    record_enum_variant_captures_from_roots(
        function,
        summary,
        capture_ctx,
        object,
        values,
        variant,
    );
}

fn record_materialize(
    summary: &mut ObjectEffectSummary,
    arg_roots: &FxHashMap<ValueId, usize>,
    provenance: &super::provenance::RootProvenanceMap,
    object: ValueId,
    heap: bool,
) {
    for root_idx in root_arg_indices(arg_roots, provenance, object) {
        summary.arg_effects[root_idx].materializes_stack |= !heap;
        summary.arg_effects[root_idx].materializes_heap |= heap;
        summary.arg_effects[root_idx].escapes |= heap;
    }
}

fn record_slice_access(
    summary: &mut ObjectEffectSummary,
    arg_roots: &FxHashMap<ValueId, usize>,
    provenance: &super::provenance::RootProvenanceMap,
    object: ValueId,
    write: bool,
    fixed_slice: Option<(usize, usize)>,
) {
    if let Some(projection) = provenance.exact_projection(object)
        && let Some(&idx) = arg_roots.get(&projection.root_value)
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

    for root_idx in root_arg_indices(arg_roots, provenance, object) {
        if write {
            summary.arg_effects[root_idx].writes =
                SliceSet::whole_root(summary.arg_effects[root_idx].writes.total_leaves());
        } else {
            summary.arg_effects[root_idx].reads =
                SliceSet::whole_root(summary.arg_effects[root_idx].reads.total_leaves());
        }
    }
}

fn root_arg_indices(
    arg_roots: &FxHashMap<ValueId, usize>,
    provenance: &super::provenance::RootProvenanceMap,
    object: ValueId,
) -> Vec<usize> {
    match provenance.provenance(object) {
        super::RootProvenance::Exact(projection) => arg_roots
            .get(&projection.root_value)
            .copied()
            .into_iter()
            .collect(),
        super::RootProvenance::SameRoot(root) => {
            arg_roots.get(&root).copied().into_iter().collect()
        }
        super::RootProvenance::Maybe(roots) => roots
            .into_iter()
            .filter_map(|root| arg_roots.get(&root).copied())
            .collect(),
        super::RootProvenance::Unknown => Vec::new(),
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
            summary.captures.iter().any(|capture| {
                capture.dst_arg == 0
                    && capture.src_arg == 1
                    && capture.dst_slice.first_leaf == 0
                    && capture.dst_slice.leaf_count == 1
                    && capture.src_slice.ty == Type::I256
                    && capture.src_slice.first_leaf == 0
                    && capture.src_slice.leaf_count == 1
            }),
            "summary should record field-0 capture from the source arg"
        );
        assert!(
            summary.captures.iter().any(|capture| {
                capture.dst_arg == 0
                    && capture.src_arg == 1
                    && capture.dst_slice.first_leaf == 1
                    && capture.dst_slice.leaf_count == 1
                    && capture.src_slice.ty == Type::I256
                    && capture.src_slice.first_leaf == 1
                    && capture.src_slice.leaf_count == 1
            }),
            "summary should record field-1 capture from the source arg"
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
            summary.captures.iter().any(|capture| {
                capture.dst_arg == 0
                    && capture.src_arg == 1
                    && capture.dst_slice.first_leaf == 0
                    && capture.src_slice.first_leaf == 0
            }),
            "transitive helper summary should preserve capture relations"
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
            summary.captures.iter().any(|capture| {
                capture.dst_arg == 0
                    && capture.src_arg == 1
                    && capture.dst_slice.first_leaf == 0
                    && capture.dst_slice.leaf_count == 1
                    && capture.src_slice.first_leaf == 0
                    && capture.src_slice.leaf_count == 2
            }),
            "same-root phi capture should conservatively widen to the whole source root"
        );
    }
}
