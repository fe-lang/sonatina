//! Whole-function may reachability. This consumes conservative root alternatives,
//! never exact loaded-reference proofs, and does not construct provenance itself.

use super::{
    ObjectEffectSummaryMap, ObjectReturnEffect,
    object_alias::ObjectAliasFacts,
    object_effects::ObjectCaptureDestination,
    provenance::{MayProvenance, RootValue},
    shape,
};
use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, InstId, Type, ValueId,
    effects::{AccessKind, AccessLoc, MemoryAccess},
    inst::{cast, control_flow, data, downcast},
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct References {
    pub(crate) roots: FxHashSet<RootValue>,
    pub(crate) external: bool,
    pub(crate) unknown: bool,
}

impl References {
    fn union_with(&mut self, other: &Self) -> bool {
        let old_len = self.roots.len();
        let changed = other.external && !self.external || other.unknown && !self.unknown;
        self.roots.extend(&other.roots);
        self.external |= other.external;
        self.unknown |= other.unknown;
        changed || old_len != self.roots.len()
    }
}

pub(crate) struct ObjectReachability {
    pub(crate) aliases: ObjectAliasFacts,
    pub(crate) references: SecondaryMap<ValueId, References>,
    roots: FxHashSet<RootValue>,
    contents: FxHashMap<RootValue, References>,
    exposed: FxHashSet<RootValue>,
    unknown_published: bool,
}

impl ObjectReachability {
    pub(crate) fn new(
        func: &Function,
        summaries: Option<&ObjectEffectSummaryMap>,
        may: MayProvenance<'_>,
    ) -> Self {
        let aliases = ObjectAliasFacts::new(func, summaries);
        let roots: FxHashSet<_> = func
            .dfg
            .value_ids()
            .filter(|&value| {
                aliases.is_fresh(RootValue::new(value))
                    || func.arg_values.contains(&value)
                        && func.dfg.value_ty(value).is_obj_ref(func.ctx())
            })
            .map(RootValue::new)
            .collect();
        let mut this = Self {
            roots,
            aliases,
            references: SecondaryMap::default(),
            contents: FxHashMap::default(),
            exposed: FxHashSet::default(),
            unknown_published: false,
        };
        for &root in &this.roots {
            let value = root.value();
            this.references[value].roots.insert(root);
            if !this.aliases.is_fresh(root) {
                this.exposed.insert(root);
                this.contents.entry(root).or_default().external = true;
            }
        }
        for &arg in &func.arg_values {
            if reference_bearing(func, arg) && this.references[arg].roots.is_empty() {
                this.references[arg].external = true;
            }
        }
        // Only values without definitions start unknown. Recognized producers
        // grow from bottom; an unrelated unresolved SSA value is not published.
        for value in func.dfg.value_ids() {
            if this.aliases.is_fresh(RootValue::new(value)) {
                this.references[value].roots.insert(RootValue::new(value));
            }
            if reference_bearing(func, value)
                && func.dfg.value_inst(value).is_none()
                && !func.arg_values.contains(&value)
            {
                this.references[value].unknown = true;
            }
        }
        loop {
            let mut changed = false;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    changed |= this.transfer_references(func, inst, summaries, may);
                }
            }
            for root in this.exposed.clone() {
                if let Some(contents) = this.contents.get(&root).cloned() {
                    changed |= this.expose(&contents);
                }
            }
            if !changed {
                // Cyclic or unsupported source chains can converge at bottom.
                // Bottom is not an exhaustive empty set for a direct reference.
                // Widen only after propagation, then close exposure again.
                for value in func.dfg.value_ids() {
                    let ty = func.dfg.value_ty(value);
                    let refs = &mut this.references[value];
                    if (ty.is_obj_ref(func.ctx()) || ty.is_pointer(func.ctx()))
                        && refs.roots.is_empty()
                        && !refs.external
                        && !refs.unknown
                    {
                        refs.unknown = true;
                        changed = true;
                    }
                }
                if !changed {
                    return this;
                }
            }
        }
    }

    pub(crate) fn exposed(&self, root: RootValue) -> bool {
        self.unknown_published || !self.aliases.is_fresh(root) || self.exposed.contains(&root)
    }

    fn expose(&mut self, references: &References) -> bool {
        let old_len = self.exposed.len();
        let changed = references.unknown && !self.unknown_published;
        self.unknown_published |= references.unknown;
        self.exposed.extend(&references.roots);
        if self.unknown_published {
            self.exposed.extend(self.roots.iter().copied());
        }
        changed || old_len != self.exposed.len()
    }

    fn store_references(&mut self, object: ValueId, contents: &References) -> bool {
        let destinations = self.references[object].clone();
        let mut changed = false;
        for root in &destinations.roots {
            changed |= self.contents.entry(*root).or_default().union_with(contents);
        }
        if destinations.external
            || destinations.unknown
            || destinations.roots.iter().any(|&root| self.exposed(root))
        {
            changed |= self.expose(contents);
        }
        changed
    }

    fn transfer_references(
        &mut self,
        func: &Function,
        inst: InstId,
        summaries: Option<&ObjectEffectSummaryMap>,
        may: MayProvenance<'_>,
    ) -> bool {
        let data = func.dfg.inst(inst);
        let is = func.inst_set();
        let mut changed = false;
        if let Some(store) = downcast::<&data::ObjStore>(is, data) {
            changed |=
                self.store_references(*store.object(), &self.references[*store.value()].clone());
        } else if downcast::<&data::ObjInitConst>(is, data).is_some() {
            // Constant initialization does not publish the destination.
        } else if let Some(store) = downcast::<&data::EnumWriteVariant>(is, data) {
            for value in store.values() {
                changed |= self.store_references(*store.object(), &self.references[*value].clone());
            }
        } else if let Some(mat) = downcast::<&data::ObjMaterializeStack>(is, data) {
            changed |= self.expose(&self.references[*mat.object()].clone());
        } else if let Some(mat) = downcast::<&data::ObjMaterializeHeap>(is, data) {
            changed |= self.expose(&self.references[*mat.object()].clone());
        } else if let Some(call) = downcast::<&control_flow::Call>(is, data) {
            let summary = summaries.and_then(|summaries| summaries.get(call.callee()));
            for (index, &arg) in call.args().iter().enumerate() {
                if summary.is_none_or(|summary| {
                    summary.non_arg.external.publishes
                        || summary.non_arg.unknown.publishes
                        || summary
                            .arg_effects
                            .get(index)
                            .is_none_or(|effect| effect.needs_unknown_object_barrier())
                }) {
                    changed |= self.expose(&self.references[arg].clone());
                }
            }
            if let Some(summary) = summary {
                for capture in &summary.captures {
                    let dst = match capture.dst {
                        ObjectCaptureDestination::Arg { index, .. } => {
                            call.args().get(index).copied()
                        }
                        ObjectCaptureDestination::Return { .. } => func.dfg.inst_result(inst),
                    };
                    if let Some(dst) = dst
                        && let Some(&src) = call.args().get(capture.src_arg)
                    {
                        changed |= self.store_references(dst, &self.references[src].clone());
                    }
                }
            }
        } else if downcast::<&control_flow::Return>(is, data).is_some()
            || func
                .dfg
                .effects(inst)
                .accesses
                .iter()
                .any(|access| access.kind == AccessKind::Write)
        {
            for value in data.collect_values() {
                changed |= self.expose(&self.references[value].clone());
            }
        }

        for &result in func.dfg.inst_results(inst) {
            if !reference_bearing(func, result)
                || self.roots.contains(&RootValue::new(result))
                || self.aliases.is_fresh(RootValue::new(result))
            {
                continue;
            }
            let mut next = References::default();
            if let Some(load) = downcast::<&data::ObjLoad>(is, data) {
                let address = &self.references[*load.object()];
                next.external =
                    address.external || address.roots.iter().any(|&root| self.exposed(root));
                next.unknown = address.unknown;
                for (&root, contents) in &self.contents {
                    if address.unknown
                        || address.external && self.exposed(root)
                        || address
                            .roots
                            .iter()
                            .any(|&source| self.aliases.roots_may_overlap(source, root))
                    {
                        next.union_with(contents);
                    }
                }
                let known = may.may_roots(result);
                next.roots.extend(known.observed().iter());
                // A private cell without a complete initialization/content proof
                // still has an unresolved local alternative.
                next.unknown |= known.has_unknown() && !next.external;
            } else if let Some(call) = downcast::<&control_flow::Call>(is, data) {
                match summaries
                    .and_then(|summaries| summaries.get(call.callee()))
                    .map(|s| &s.ret_effect)
                {
                    Some(
                        ObjectReturnEffect::SameAsArg { index }
                        | ObjectReturnEffect::DerivedFromArg { index },
                    ) => {
                        if let Some(&arg) = call.args().get(*index) {
                            next.union_with(&self.references[arg]);
                        } else {
                            next.unknown = true;
                        }
                    }
                    Some(ObjectReturnEffect::BorrowedArgs { indices }) => {
                        for &index in indices {
                            if let Some(&arg) = call.args().get(index) {
                                next.union_with(&self.references[arg]);
                            } else {
                                next.unknown = true;
                            }
                        }
                    }
                    _ => {
                        next.external = true;
                        next.unknown = self.unknown_published;
                    }
                }
            } else if downcast::<&data::Mload>(is, data).is_some() {
                next.external = true;
                next.unknown = self.unknown_published;
            } else if downcast::<&data::ObjProj>(is, data).is_some()
                || downcast::<&data::ObjIndex>(is, data).is_some()
                || downcast::<&data::EnumProj>(is, data).is_some()
                || downcast::<&data::EnumAssertVariantRef>(is, data).is_some()
                || downcast::<&data::ObjMaterializeStack>(is, data).is_some()
                || downcast::<&data::ObjMaterializeHeap>(is, data).is_some()
                || downcast::<&data::Gep>(is, data).is_some()
                || downcast::<&cast::Bitcast>(is, data).is_some()
                || downcast::<&control_flow::Phi>(is, data).is_some()
                || downcast::<&data::InsertValue>(is, data).is_some()
                || downcast::<&data::ExtractValue>(is, data).is_some()
                || downcast::<&data::EnumMake>(is, data).is_some()
                || downcast::<&data::EnumExtract>(is, data).is_some()
                || downcast::<&data::EnumAssertVariant>(is, data).is_some()
            {
                for value in data.collect_values() {
                    next.union_with(&self.references[value]);
                }
            } else {
                next.unknown = true;
            }
            changed |= self.references[result].union_with(&next);
        }
        changed
    }

    pub(crate) fn reachable(&self, value: ValueId) -> References {
        let mut refs = self.references[value].clone();
        loop {
            let mut changed = false;
            for root in refs.roots.clone() {
                if let Some(contents) = self.contents.get(&root) {
                    changed |= refs.union_with(contents);
                }
            }
            if !changed {
                return refs;
            }
        }
    }

    pub(crate) fn may_reach(&self, value: ValueId, root: RootValue) -> bool {
        let refs = &self.references[value];
        refs.unknown
            || refs.external && self.exposed(root)
            || refs
                .roots
                .iter()
                .any(|&source| self.aliases.roots_may_overlap(source, root))
    }
}

pub(crate) fn reference_bearing(func: &Function, value: ValueId) -> bool {
    let ty: Type = func.dfg.value_ty(value);
    ty.is_obj_ref(func.ctx())
        || ty.is_pointer(func.ctx())
        || shape::is_reference_aggregate(func.ctx(), ty)
}

/// Raw bytes have no typed-leaf coordinates. Only the bounded direct-allocation
/// exception proves that an access cannot interfere with typed object storage.
pub(crate) fn raw_access_may_reach_objects(func: &Function, access: &MemoryAccess) -> bool {
    if access.space != func.ctx().address_spaces().default_space() {
        return false;
    }
    !match access.loc {
        AccessLoc::LinearExact { addr, bytes, .. } => func
            .dfg
            .value_inst(addr)
            .and_then(|inst| downcast::<&data::Alloca>(func.inst_set(), func.dfg.inst(inst)))
            .is_some_and(|alloc| {
                func.ctx()
                    .size_of(*alloc.ty())
                    .is_ok_and(|size| u64::from(bytes) <= size as u64)
            }),
        _ => false,
    }
}
