//! Access facts cover all operands, independently of optimization eligibility.
//! Exposure is a whole-function may fixed point; it never proves an overwrite.

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, InstId, ValueId,
    effects::AccessKind,
    inst::{control_flow, data, downcast},
    types::EnumVariantRef,
};

use super::{
    LocalObjectArgInfo, ObjectEffectSummaryMap, SliceSet,
    object_effects::{ObjectCaptureDestination, ObjectEffectSummary},
    object_reachability::{ObjectReachability, raw_access_may_reach_objects, reference_bearing},
    object_tracking::{AggregateFacts, ObjectSlice, TrackedObject, collect_tracked_objects},
    provenance::{MayProvenance, Projection, ProvenanceSnapshot, RootValue},
    shape::{self, AggregateLayoutCache, AggregateSlice},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ObjectAccess {
    Exact(Projection),
    Root(RootValue),
    External,
    Unknown,
}

type AccessSet = SmallVec<[ObjectAccess; 4]>;

/// Only direct typed writes construct this type. May-write summaries cannot.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DefiniteObjectWrite(Projection);

#[derive(Clone, Copy, Debug)]
pub(crate) enum ObjectInitializationSource {
    Value(ValueId),
    /// Constant data and an instruction-selected enum tag are defined encodings.
    Intrinsic,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ObjectInitializationWrite {
    pub destination: DefiniteObjectWrite,
    pub source: ObjectInitializationSource,
}

#[derive(Default)]
pub(crate) struct ObjectInstEffects {
    pub reads: AccessSet,
    pub writes: AccessSet,
    pub overwrites: SmallVec<[DefiniteObjectWrite; 4]>,
    pub captures: Vec<(AccessSet, AccessSet)>,
    /// Additional logical readability invalidation, beyond physical may-writes.
    pub unreadable: AccessSet,
    pub tag_selections: SmallVec<[(Projection, EnumVariantRef); 1]>,
    pub variant_assumptions: SmallVec<[(ValueId, EnumVariantRef); 1]>,
    pub initialization: SmallVec<[ObjectInitializationWrite; 4]>,
}

pub(crate) struct ObjectAccessFacts {
    facts: AggregateFacts,
    reachability: ObjectReachability,
}

impl ObjectAccessFacts {
    pub(crate) fn tracked(
        &self,
        func: &Function,
        local_args: Option<&FxHashMap<usize, LocalObjectArgInfo>>,
        cache: &mut AggregateLayoutCache,
    ) -> SecondaryMap<ValueId, Option<TrackedObject>> {
        let mut eligible: FxHashSet<_> = self
            .facts
            .root_slices()
            .keys()
            .copied()
            .filter(|&root| self.reachability.aliases.is_fresh(RootValue::new(root)))
            .collect();
        if let Some(local_args) = local_args {
            eligible.extend(
                local_args
                    .keys()
                    .filter_map(|&index| func.arg_values.get(index).copied()),
            );
        }
        self.tracked_for_roots(func, &eligible, cache)
    }

    pub(crate) fn tracked_for_roots(
        &self,
        func: &Function,
        eligible: &FxHashSet<ValueId>,
        cache: &mut AggregateLayoutCache,
    ) -> SecondaryMap<ValueId, Option<TrackedObject>> {
        let mut tracked = self.tracked_all(func, cache);
        for (_, object) in tracked.iter_mut() {
            let root = match object {
                Some(TrackedObject::Exact(slice)) => slice.root,
                Some(TrackedObject::RootUnknown { root, .. }) => *root,
                None => continue,
            };
            if !eligible.contains(&root) {
                *object = None;
            }
        }
        tracked
    }

    pub(crate) fn tracked_all(
        &self,
        func: &Function,
        cache: &mut AggregateLayoutCache,
    ) -> SecondaryMap<ValueId, Option<TrackedObject>> {
        collect_tracked_objects(func, self.facts.complete(), cache)
    }

    fn ancestor_tag_reads(
        &self,
        func: &Function,
        projection: Projection,
        cache: &mut AggregateLayoutCache,
    ) -> AccessSet {
        let mut ancestors = AccessSet::new();
        let mut current = self.facts.root_slices()[&projection.root_value.value()];
        for _ in 0..64 {
            if current.first_leaf == projection.slice.first_leaf
                && current.leaf_count == projection.slice.leaf_count
            {
                return ancestors;
            }
            let relative = AggregateSlice {
                first_leaf: projection.slice.first_leaf - current.first_leaf,
                ..projection.slice
            };
            let Some((index, child)) =
                cache.child_containing_slice(func.ctx(), current.ty, relative)
            else {
                return smallvec![ObjectAccess::Root(projection.root_value)];
            };
            if index != 0
                && func.ctx().with_ty_store(|types| types.is_enum(current.ty))
                && let Some(tag) = shape::enum_tag_slice(func.ctx(), current.ty)
            {
                ancestors.push(ObjectAccess::Exact(Projection {
                    root_value: projection.root_value,
                    slice: AggregateSlice {
                        first_leaf: current.first_leaf + tag.first_leaf,
                        ..tag
                    },
                }));
            }
            current = AggregateSlice {
                first_leaf: current.first_leaf + child.first_leaf,
                ..child
            };
        }
        // An analysis limit may broaden an observation, never remove it.
        smallvec![ObjectAccess::Root(projection.root_value)]
    }

    pub(crate) fn single_instance(&self, root: RootValue) -> bool {
        self.reachability.aliases.single_instance(root)
    }

    pub(crate) fn write_slice(&self, write: DefiniteObjectWrite) -> ObjectSlice {
        self.projection_slice(write.0)
    }

    pub(crate) fn projection_slice(&self, projection: Projection) -> ObjectSlice {
        ObjectSlice {
            root: projection.root_value.value(),
            ty: projection.slice.ty,
            first_leaf: projection.slice.first_leaf,
            leaf_count: projection.slice.leaf_count,
            total_leaves: self.facts.root_slices()[&projection.root_value.value()].leaf_count,
        }
    }

    pub(crate) fn may(&self) -> MayProvenance<'_> {
        self.facts.may()
    }

    pub(crate) fn new(func: &Function, summaries: Option<&ObjectEffectSummaryMap>) -> Self {
        let mut cache = AggregateLayoutCache::default();
        let mut snapshot = ProvenanceSnapshot::new(func, summaries);
        let facts = AggregateFacts::for_accesses(func, &mut cache, &mut snapshot);
        let reachability = ObjectReachability::new(func, summaries, facts.may());
        Self {
            facts,
            reachability,
        }
    }

    pub(crate) fn exposed(&self, root: RootValue) -> bool {
        self.reachability.exposed(root)
    }

    pub(crate) fn may_overlap(&self, access: ObjectAccess, target: ObjectSlice) -> bool {
        let target = Projection {
            root_value: RootValue::new(target.root),
            slice: AggregateSlice {
                ty: target.ty,
                first_leaf: target.first_leaf,
                leaf_count: target.leaf_count,
            },
        };
        match access {
            ObjectAccess::Exact(projection) => {
                self.reachability.aliases.may_overlap(projection, target)
            }
            ObjectAccess::Root(root) => self
                .reachability
                .aliases
                .roots_may_overlap(root, target.root_value),
            ObjectAccess::External => self.exposed(target.root_value),
            ObjectAccess::Unknown => true,
        }
    }

    pub(crate) fn write_covers(&self, write: DefiniteObjectWrite, target: ObjectSlice) -> bool {
        self.reachability.aliases.exact_write_covers(
            write.0,
            Projection {
                root_value: RootValue::new(target.root),
                slice: AggregateSlice {
                    ty: target.ty,
                    first_leaf: target.first_leaf,
                    leaf_count: target.leaf_count,
                },
            },
        )
    }

    fn access(&self, value: ValueId, relative: Option<AggregateSlice>) -> AccessSet {
        if let Some(mut exact) = self.facts.complete().exact_projection(value) {
            if let Some(relative) = relative {
                if relative
                    .first_leaf
                    .checked_add(relative.leaf_count)
                    .is_none_or(|end| end > exact.slice.leaf_count)
                {
                    return smallvec![ObjectAccess::Root(exact.root_value)];
                }
                exact.slice = AggregateSlice {
                    first_leaf: exact.slice.first_leaf + relative.first_leaf,
                    ..relative
                };
            }
            return smallvec![ObjectAccess::Exact(exact)];
        }
        let refs = &self.reachability.references[value];
        let mut out: AccessSet = refs.roots.iter().copied().map(ObjectAccess::Root).collect();
        if refs.external {
            out.push(ObjectAccess::External);
        }
        if refs.unknown || out.is_empty() {
            out.push(ObjectAccess::Unknown);
        }
        out
    }

    fn typed_write(
        &self,
        effects: &mut ObjectInstEffects,
        value: ValueId,
        relative: Option<AggregateSlice>,
        source: ObjectInitializationSource,
    ) {
        let accesses = self.access(value, relative);
        if let [ObjectAccess::Exact(projection)] = accesses.as_slice() {
            let destination = DefiniteObjectWrite(*projection);
            effects.overwrites.push(destination);
            effects.initialization.push(ObjectInitializationWrite {
                destination,
                source,
            });
        }
        effects.writes.extend(accesses);
    }

    fn summary_access(&self, value: ValueId, slices: &SliceSet) -> AccessSet {
        if slices.is_empty() {
            return AccessSet::new();
        }
        let Some(exact) = self.facts.complete().exact_projection(value) else {
            return self.access(value, None);
        };
        if slices.is_whole_root() || exact.slice.leaf_count != slices.total_leaves() {
            return self.access(value, None);
        }
        let Some(leaves) = slices.exact_leaves() else {
            return self.access(value, None);
        };
        leaves
            .iter()
            .flat_map(|&leaf| {
                self.access(
                    value,
                    Some(AggregateSlice {
                        ty: exact.slice.ty,
                        first_leaf: leaf,
                        leaf_count: 1,
                    }),
                )
            })
            .collect()
    }

    fn reachable_access(&self, value: ValueId) -> AccessSet {
        let refs = self.reachability.reachable(value);
        let mut out: AccessSet = refs.roots.into_iter().map(ObjectAccess::Root).collect();
        if refs.external {
            out.push(ObjectAccess::External);
        }
        if refs.unknown {
            out.push(ObjectAccess::Unknown);
        }
        out
    }

    pub(crate) fn effects(
        &self,
        func: &Function,
        inst: InstId,
        summaries: Option<&ObjectEffectSummaryMap>,
    ) -> ObjectInstEffects {
        let mut effects = ObjectInstEffects::default();
        let data = func.dfg.inst(inst);
        let is = func.inst_set();
        let tag = |object| {
            self.facts
                .complete()
                .exact_projection(object)
                .and_then(|p| shape::enum_tag_slice(func.ctx(), p.slice.ty))
        };
        if let Some(load) = downcast::<&data::ObjLoad>(is, data) {
            effects.reads = self.access(*load.object(), None);
        } else if let Some(load) = downcast::<&data::EnumGetTag>(is, data) {
            effects.reads = self.access(*load.object(), tag(*load.object()));
        } else if let Some(assert) = downcast::<&data::EnumAssertVariantRef>(is, data) {
            effects.reads = self.access(*assert.object(), tag(*assert.object()));
            effects
                .variant_assumptions
                .push((*assert.object(), *assert.variant()));
        } else if let Some(assert) = downcast::<&data::EnumAssertVariant>(is, data) {
            effects
                .variant_assumptions
                .push((*assert.value(), *assert.variant()));
        } else if let Some(store) = downcast::<&data::ObjStore>(is, data) {
            self.typed_write(
                &mut effects,
                *store.object(),
                None,
                ObjectInitializationSource::Value(*store.value()),
            );
            if reference_bearing(func, *store.value()) {
                effects.captures.push((
                    self.access(*store.object(), None),
                    self.reachable_access(*store.value()),
                ));
            }
        } else if let Some(init) = downcast::<&data::ObjInitConst>(is, data) {
            self.typed_write(
                &mut effects,
                *init.object(),
                None,
                ObjectInitializationSource::Intrinsic,
            );
        } else if let Some(store) = downcast::<&data::EnumSetTag>(is, data) {
            effects
                .unreadable
                .extend(self.access(*store.object(), None));
            self.typed_write(
                &mut effects,
                *store.object(),
                tag(*store.object()),
                ObjectInitializationSource::Intrinsic,
            );
        } else if let Some(store) = downcast::<&data::EnumWriteVariant>(is, data) {
            effects
                .unreadable
                .extend(self.access(*store.object(), None));
            self.typed_write(
                &mut effects,
                *store.object(),
                tag(*store.object()),
                ObjectInitializationSource::Intrinsic,
            );
            if let Some(projection) = self.facts.complete().exact_projection(*store.object()) {
                for (index, _) in store.values().iter().enumerate() {
                    let field = u32::try_from(index).ok().and_then(|index| {
                        shape::enum_variant_field_slice(
                            func.ctx(),
                            projection.slice.ty,
                            *store.variant(),
                            index,
                        )
                    });
                    if let Some(field) = field {
                        self.typed_write(
                            &mut effects,
                            *store.object(),
                            Some(field),
                            ObjectInitializationSource::Value(store.values()[index]),
                        );
                        let value = store.values()[index];
                        if reference_bearing(func, value) {
                            effects.captures.push((
                                self.access(*store.object(), Some(field)),
                                self.reachable_access(value),
                            ));
                        }
                    }
                }
            }
        } else if let Some(call) = downcast::<&control_flow::Call>(is, data) {
            let unknown;
            let summary = match summaries.and_then(|summaries| summaries.get(call.callee())) {
                Some(summary) => summary,
                None => {
                    unknown = ObjectEffectSummary::conservative_unknown(
                        func.ctx(),
                        *call.callee(),
                        &mut AggregateLayoutCache::default(),
                    );
                    &unknown
                }
            };
            for (index, &arg) in call.args().iter().enumerate() {
                if let Some(effect) = summary.arg_effects.get(index) {
                    effects
                        .reads
                        .extend(self.summary_access(arg, &effect.reads));
                    effects
                        .writes
                        .extend(self.summary_access(arg, &effect.writes));
                    if effect.needs_unknown_object_barrier() {
                        effects.reads.extend(self.reachable_access(arg));
                    }
                }
            }
            for capture in &summary.captures {
                let (dst, slice) = match capture.dst {
                    ObjectCaptureDestination::Arg { index, slice } => {
                        (call.args().get(index).copied(), slice)
                    }
                    ObjectCaptureDestination::Return { slice } => {
                        (func.dfg.inst_result(inst), slice)
                    }
                };
                if let Some(dst) = dst
                    && let Some(&src) = call.args().get(capture.src_arg)
                {
                    effects.captures.push((
                        self.access(dst, Some(slice)),
                        self.access(src, Some(capture.src_slice)),
                    ));
                }
            }
            for (location, effect) in [
                (ObjectAccess::External, summary.non_arg.external),
                (ObjectAccess::Unknown, summary.non_arg.unknown),
            ] {
                if effect.reads {
                    effects.reads.push(location);
                }
                if effect.writes {
                    effects.writes.push(location);
                }
            }
        } else if let Some(mat) = downcast::<&data::ObjMaterializeStack>(is, data) {
            effects.reads.extend(self.reachable_access(*mat.object()));
        } else if let Some(mat) = downcast::<&data::ObjMaterializeHeap>(is, data) {
            effects.reads.extend(self.reachable_access(*mat.object()));
        } else if downcast::<&control_flow::Return>(is, data).is_some() {
            for value in data.collect_values() {
                effects.reads.extend(self.reachable_access(value));
            }
        } else {
            for access in func.dfg.effects(inst).accesses {
                if access.kind == AccessKind::Write {
                    for value in data.collect_values() {
                        effects.reads.extend(self.reachable_access(value));
                    }
                }
                if !raw_access_may_reach_objects(func, &access) {
                    continue;
                }
                match access.kind {
                    AccessKind::Read => effects.reads.push(ObjectAccess::External),
                    AccessKind::Write => effects.writes.push(ObjectAccess::External),
                }
            }
        }
        let selection = downcast::<&data::EnumSetTag>(is, data)
            .map(|tag| (*tag.object(), *tag.variant()))
            .or_else(|| {
                downcast::<&data::EnumWriteVariant>(is, data)
                    .map(|write| (*write.object(), *write.variant()))
            });
        if let Some((object, variant)) = selection
            && let [ObjectAccess::Exact(projection)] = self.access(object, None).as_slice()
        {
            effects.tag_selections.push((*projection, variant));
        }
        let mut cache = AggregateLayoutCache::default();
        let reads = effects.reads.clone();
        for read in reads {
            if let ObjectAccess::Exact(projection) = read {
                for ancestor in self.ancestor_tag_reads(func, projection, &mut cache) {
                    if !effects.reads.contains(&ancestor) {
                        effects.reads.push(ancestor);
                    }
                }
            }
        }
        effects
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transform::aggregate::compute_object_effect_summaries;
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    fn check(
        source: &str,
        test: impl FnOnce(&Function, &ObjectAccessFacts, &ObjectEffectSummaryMap),
    ) {
        let module = parse_module(source).unwrap().module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(report.is_ok(), "{report}");
        let summaries = compute_object_effect_summaries(&module);
        let f = module
            .funcs()
            .into_iter()
            .find(|&f| module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .unwrap();
        module.func_store.view(f, |func| {
            test(
                func,
                &ObjectAccessFacts::new(func, Some(&summaries)),
                &summaries,
            )
        });
    }

    fn location(facts: &ObjectAccessFacts, value: u32) -> ObjectSlice {
        let projection = facts
            .facts
            .complete()
            .exact_projection(ValueId::from_u32(value))
            .unwrap();
        ObjectSlice {
            root: projection.root_value.value(),
            ty: projection.slice.ty,
            first_leaf: projection.slice.first_leaf,
            leaf_count: projection.slice.leaf_count,
            total_leaves: facts.facts.root_slices()[&projection.root_value.value()].leaf_count,
        }
    }

    #[test]
    fn publishing_unresolved_pointer_cannot_leave_an_empty_alternative() {
        check(
            r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<*i256>) {
block0:
    v1.objref<i256> = obj.alloc i256;
    v2.*i256 = bitcast 0.i256 *i256;
    obj.store v0 v2;
    return;
}
"#,
            |_, facts, _| {
                assert!(facts.reachability.references[ValueId::from_u32(2)].unknown);
                assert!(facts.may_overlap(ObjectAccess::External, location(facts, 1)));
            },
        );
    }

    #[test]
    fn opaque_zero_argument_effects_spare_unpublished_fresh_roots() {
        check(
            r#"
target = "evm-ethereum-osaka"
declare external %opaque();
func private %f(v0.objref<i256>) {
block0:
    v1.objref<i256> = obj.alloc i256;
    obj.store v1 11.i256;
    call %opaque;
    return;
}
"#,
            |func, facts, summaries| {
                let call = func
                    .layout
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .find(|&inst| func.dfg.call_info(inst).is_some())
                    .unwrap();
                let effects = facts.effects(func, call, Some(summaries));
                assert!(effects.overwrites.is_empty());
                for accesses in [&effects.reads, &effects.writes] {
                    assert!(
                        accesses
                            .iter()
                            .any(|&access| facts.may_overlap(access, location(facts, 0)))
                    );
                    assert!(
                        !accesses
                            .iter()
                            .any(|&access| facts.may_overlap(access, location(facts, 1)))
                    );
                }
            },
        );
    }

    #[test]
    fn recovered_reference_reaches_published_but_not_unrelated_fresh_storage() {
        check(
            r#"
target = "evm-ethereum-osaka"
func private %recover(v0.objref<objref<i256>>) -> objref<i256> {
block0:
    v1.objref<i256> = obj.load v0;
    return v1;
}
func private %f(v0.objref<objref<i256>>) -> i256 {
block0:
    v1.objref<i256> = obj.alloc i256;
    v2.objref<i256> = obj.alloc i256;
    obj.store v1 11.i256;
    obj.store v0 v1;
    v3.objref<i256> = call %recover v0;
    obj.store v3 22.i256;
    v4.i256 = obj.load v1;
    return v4;
}
"#,
            |func, facts, summaries| {
                let store = func
                    .layout
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .find(|&inst| {
                        downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst))
                            .is_some_and(|store| *store.object() == ValueId::from_u32(3))
                    })
                    .unwrap();
                let effects = facts.effects(func, store, Some(summaries));
                assert!(effects.overwrites.is_empty());
                assert!(
                    effects
                        .writes
                        .iter()
                        .any(|&access| facts.may_overlap(access, location(facts, 1)))
                );
                assert!(
                    !effects
                        .writes
                        .iter()
                        .any(|&access| facts.may_overlap(access, location(facts, 2)))
                );
            },
        );
    }

    #[test]
    fn exposure_closes_transitively_through_private_holders() {
        check(
            r#"
target = "evm-ethereum-osaka"
declare external %opaque();
type @Holder = { objref<i256> };
func private %f(v0.objref<objref<@Holder>>) {
block0:
    v1.objref<i256> = obj.alloc i256;
    v2.objref<@Holder> = obj.alloc @Holder;
    v3.objref<i256> = obj.alloc i256;
    obj.store v1 11.i256;
    v4.objref<objref<i256>> = obj.proj v2 0.i8;
    obj.store v4 v1;
    obj.store v0 v2;
    call %opaque;
    return;
}
"#,
            |_, facts, _| {
                assert!(facts.may_overlap(ObjectAccess::External, location(facts, 1)));
                assert!(facts.may_overlap(ObjectAccess::External, location(facts, 2)));
                assert!(!facts.may_overlap(ObjectAccess::External, location(facts, 3)));
            },
        );
    }

    #[test]
    fn materialization_exposes_sibling_fields_allocation_wide() {
        check(
            r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
func private %f() {
block0:
    v0.objref<@Pair> = obj.alloc @Pair;
    v1.objref<i256> = obj.proj v0 0.i8;
    v2.objref<i256> = obj.proj v0 1.i8;
    obj.store v1 11.i256;
    obj.store v2 22.i256;
    v3.*i256 = obj.materialize.stack v1;
    return;
}
"#,
            |_, facts, _| {
                assert!(facts.may_overlap(ObjectAccess::External, location(facts, 2)));
            },
        );
    }
}
