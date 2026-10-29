//! Semantic object overlap, separate from exact projection coordinates (I1-I3).
//!
//! This table describes every direct origin in the function, independently of
//! the roots selected for an optimization. Missing origins are unknown, never
//! evidence of separation. It contains no locality or initialization claims.

use std::sync::Arc;

use rustc_hash::FxHashMap;
use sonatina_ir::{
    ControlFlowGraph, Function, Type, ValueId,
    inst::{control_flow, data, downcast},
    types::CompoundType,
};

use crate::cfg_scc::CfgSccAnalysis;

use super::{
    ObjectEffectSummaryMap, ObjectReturnEffect,
    provenance::{Projection, RootValue},
    shape::{PayloadPartition, payload_partition},
};

#[derive(Clone, Copy, Debug)]
enum ObjectOrigin {
    /// An object argument. A `noalias` one is reached during the call only
    /// through this function's own references to it, unless nothing writes.
    Incoming {
        noalias: bool,
    },
    Fresh {
        repeating: bool,
    },
}

#[derive(Clone)]
pub(crate) struct ObjectAliasFacts {
    origins: FxHashMap<ValueId, ObjectOrigin>,
    /// The enum payloads of each root whose object holds an enum.
    payloads: FxHashMap<ValueId, Arc<PayloadPartition>>,
}

impl ObjectAliasFacts {
    /// `cfg` must be computed from `func`.
    pub(crate) fn new(
        func: &Function,
        cfg: &ControlFlowGraph,
        effects: Option<&ObjectEffectSummaryMap>,
    ) -> Self {
        let mut origins = FxHashMap::default();
        let mut payloads = FxHashMap::default();
        let mut partitions = FxHashMap::<Type, Option<Arc<PayloadPartition>>>::default();
        let mut record_payloads = |value: ValueId| {
            let pointee = func.dfg.value_ty(value).resolve_compound(func.ctx());
            if let Some(CompoundType::ObjRef(pointee) | CompoundType::Ptr(pointee)) = pointee
                && let Some(partition) = partitions
                    .entry(pointee)
                    .or_insert_with(|| payload_partition(func.ctx(), pointee).map(Arc::new))
            {
                payloads.insert(value, partition.clone());
            }
        };
        for &arg in &func.arg_values {
            record_payloads(arg);
            if func.dfg.value_ty(arg).is_obj_ref(func.ctx()) {
                let noalias = func.is_noalias_arg(arg);
                origins.insert(arg, ObjectOrigin::Incoming { noalias });
            }
        }
        // Only blocks with a fresh origin need their cycle membership.
        let mut sccs = None;
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                func.dfg
                    .inst_results(inst)
                    .iter()
                    .copied()
                    .for_each(&mut record_payloads);
                let data = func.dfg.inst(inst);
                let fresh = downcast::<&data::ObjAlloc>(func.inst_set(), data).is_some()
                    || downcast::<&data::Alloca>(func.inst_set(), data).is_some()
                    || downcast::<&control_flow::Call>(func.inst_set(), data).is_some_and(|call| {
                        effects
                            .and_then(|effects| effects.get(call.callee()))
                            .is_some_and(|summary| {
                                summary.ret_effect == ObjectReturnEffect::FreshObject
                            })
                    });
                if fresh && let [result] = func.dfg.inst_results(inst) {
                    let sccs = sccs.get_or_insert_with(|| {
                        let mut sccs = CfgSccAnalysis::new();
                        sccs.compute(cfg);
                        sccs
                    });
                    // Disconnected code has no dynamic-instance proof from this CFG.
                    let repeating = sccs
                        .scc_of(block)
                        .is_none_or(|scc| sccs.scc_data(scc).is_cycle);
                    origins.insert(*result, ObjectOrigin::Fresh { repeating });
                }
            }
        }
        Self { origins, payloads }
    }

    pub(crate) fn is_fresh(&self, root: RootValue) -> bool {
        matches!(
            self.origins.get(&root.value()),
            Some(ObjectOrigin::Fresh { .. })
        )
    }

    /// Whether `root` is a `noalias` argument.
    pub(crate) fn is_noalias(&self, root: RootValue) -> bool {
        matches!(
            self.origins.get(&root.value()),
            Some(ObjectOrigin::Incoming { noalias: true })
        )
    }

    /// A `noalias` argument overlaps no other root: if another reference did
    /// reach its object, neither would write it during the call.
    pub(crate) fn roots_may_overlap(&self, lhs: RootValue, rhs: RootValue) -> bool {
        if lhs == rhs {
            return true;
        }
        !matches!(
            (
                self.origins.get(&lhs.value()),
                self.origins.get(&rhs.value())
            ),
            (
                Some(ObjectOrigin::Fresh { .. }),
                Some(ObjectOrigin::Fresh { .. } | ObjectOrigin::Incoming { .. })
            ) | (
                Some(ObjectOrigin::Incoming { .. }),
                Some(ObjectOrigin::Fresh { .. })
            ) | (Some(ObjectOrigin::Incoming { noalias: true }), Some(_))
                | (Some(_), Some(ObjectOrigin::Incoming { noalias: true }))
        )
    }

    /// Slices of one root overlap where their leaves meet, or where they lie
    /// in different variants of one enum, whose payloads share storage.
    pub(crate) fn may_overlap(&self, lhs: Projection, rhs: Projection) -> bool {
        if lhs.root_value != rhs.root_value {
            return self.roots_may_overlap(lhs.root_value, rhs.root_value);
        }
        let root = lhs.root_value.value();
        let range = |projection: Projection| {
            let first = projection.slice.first_leaf;
            first..first.saturating_add(projection.slice.leaf_count)
        };
        let (lhs, rhs) = (range(lhs), range(rhs));
        lhs.start < rhs.end && rhs.start < lhs.end
            || !lhs.is_empty()
                && !rhs.is_empty()
                && self
                    .payloads
                    .get(&root)
                    .is_some_and(|payloads| payloads.separates_variants(lhs, rhs))
    }

    /// Whether `root`'s object holds an enum.
    pub(crate) fn holds_enum(&self, root: RootValue) -> bool {
        self.payloads.contains_key(&root.value())
    }

    pub(crate) fn single_instance(&self, root: RootValue) -> bool {
        matches!(
            self.origins.get(&root.value()),
            Some(ObjectOrigin::Incoming { .. } | ObjectOrigin::Fresh { repeating: false })
        )
    }

    pub(crate) fn exact_write_covers(&self, write: Projection, target: Projection) -> bool {
        // I5: overlap is insufficient for a strong update. A repeating site
        // needs an additional instance proof, which this origin table lacks.
        write.root_value == target.root_value
            && self.single_instance(write.root_value)
            && write.slice.first_leaf <= target.slice.first_leaf
            && target
                .slice
                .first_leaf
                .checked_add(target.slice.leaf_count)
                .zip(write.slice.first_leaf.checked_add(write.slice.leaf_count))
                .is_some_and(|(target_end, write_end)| target_end <= write_end)
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{Function, ValueId};
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use super::*;
    use crate::transform::aggregate::{
        compute_object_effect_summaries, object_tracking::AggregateFacts,
        provenance::ProvenanceSnapshot, shape::AggregateLayoutCache,
    };

    fn check(source: &str, test: impl FnOnce(&Function, &ObjectAliasFacts, &AggregateFacts)) {
        let module = parse_module(source).unwrap().module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(report.is_ok(), "{report}");
        let effects = compute_object_effect_summaries(&module);
        let f = module
            .funcs()
            .into_iter()
            .find(|&f| module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .unwrap();
        module.func_store.view(f, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);
            let aliases = ObjectAliasFacts::new(func, &cfg, Some(&effects));
            let mut snapshot = ProvenanceSnapshot::new(func, Some(&effects));
            let facts = AggregateFacts::for_all_objref_args(
                func,
                &mut AggregateLayoutCache::default(),
                &mut snapshot,
            );
            test(func, &aliases, &facts);
        });
    }

    #[test]
    fn incoming_coordinates_fresh_identity_and_directional_coverage() {
        check(
            r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
func private %f(v0.objref<@Pair>, v1.objref<@Pair>) {
block0:
    v2.objref<i256> = obj.proj v0 0.i8;
    v3.objref<i256> = obj.proj v0 1.i8;
    v4.objref<i256> = obj.proj v1 1.i8;
    v5.objref<@Pair> = obj.alloc @Pair;
    v6.objref<@Pair> = obj.alloc @Pair;
    return;
}
"#,
            |func, aliases, facts| {
                let results: Vec<_> = func
                    .layout
                    .iter_all_insts()
                    .filter_map(|inst| func.dfg.inst_result(inst))
                    .collect();
                let exact = |value| facts.complete().exact_projection(value).unwrap();
                let a = exact(func.arg_values[0]);
                let b = exact(func.arg_values[1]);
                let [first, second, other_second, fresh, other_fresh] = results.as_slice() else {
                    panic!("five reference results expected")
                };
                assert!(!aliases.may_overlap(exact(*first), exact(*second)));
                assert!(aliases.may_overlap(exact(*first), exact(*other_second)));
                assert!(aliases.may_overlap(a, exact(*first)));
                assert!(!aliases.may_overlap(a, exact(*fresh)));
                assert!(!aliases.may_overlap(exact(*fresh), exact(*other_fresh)));
                assert!(aliases.exact_write_covers(a, exact(*second)));
                assert!(!aliases.exact_write_covers(exact(*second), a));
                assert!(!aliases.exact_write_covers(b, a));
                let missing = RootValue::new(ValueId(1000));
                assert!(aliases.roots_may_overlap(missing, exact(*fresh).root_value));
                for &left in &results {
                    for &right in &results {
                        assert_eq!(
                            aliases.may_overlap(exact(left), exact(right)),
                            aliases.may_overlap(exact(right), exact(left))
                        );
                    }
                }
            },
        );
    }

    #[test]
    fn different_variants_of_one_enum_overlap() {
        check(
            r#"
target = "evm-ethereum-osaka"
type @Inner = enum { #None, #Some(i256) };
type @E = enum { #A(i256, i256), #B(i256), #C(@Inner, i256) };
type @Holder = { i256, [@E; 2] };
func private %f(v0.objref<@Holder>) {
block0:
    v1.objref<[@E; 2]> = obj.proj v0 1.i8;
    v2.objref<@E> = obj.index v1 0.i8;
    v3.objref<@E> = obj.index v1 1.i8;
    v4.objref<i256> = enum.proj v2 #A 0.i8;
    v5.objref<i256> = enum.proj v2 #A 1.i8;
    v6.objref<i256> = enum.proj v2 #B 0.i8;
    v7.objref<i256> = enum.proj v3 #B 0.i8;
    v8.objref<@Inner> = enum.proj v2 #C 0.i8;
    v9.objref<i256> = enum.proj v8 #Some 0.i8;
    v10.objref<i256> = enum.proj v2 #C 1.i8;
    v11.objref<i256> = obj.proj v0 0.i8;
    return;
}
"#,
            |func, aliases, facts| {
                let results: Vec<_> = func
                    .layout
                    .iter_all_insts()
                    .filter_map(|inst| func.dfg.inst_result(inst))
                    .collect();
                let exact = |value| facts.complete().exact_projection(value).unwrap();
                let [
                    _,
                    first,
                    second,
                    a0,
                    a1,
                    b0,
                    other_b0,
                    c0,
                    c0_some,
                    c1,
                    plain,
                ] = results.as_slice()
                else {
                    panic!("eleven reference results expected")
                };
                let overlap = |left, right| {
                    let overlap = aliases.may_overlap(exact(left), exact(right));
                    assert_eq!(overlap, aliases.may_overlap(exact(right), exact(left)));
                    overlap
                };
                assert!(aliases.holds_enum(exact(*first).root_value));
                assert!(overlap(*a0, *b0));
                assert!(overlap(*a1, *b0));
                assert!(overlap(*b0, *c0_some));
                assert!(overlap(*a0, *c1));
                assert!(!overlap(*a0, *a1));
                assert!(!overlap(*c0, *c1));
                assert!(!overlap(*c0_some, *c1));
                assert!(!overlap(*b0, *other_b0));
                assert!(!overlap(*first, *second));
                assert!(!overlap(*a0, *plain));
            },
        );
    }

    #[test]
    fn unknown_contributor_prevents_separation_from_unrelated_fresh_root() {
        check(
            r#"
target = "evm-ethereum-osaka"
func private %recover(v0.objref<objref<i256>>) -> objref<i256> {
block0:
    v1.objref<i256> = obj.load v0;
    return v1;
}
func private %f(v0.i1, v1.objref<objref<i256>>) -> objref<i256> {
block0:
    v2.objref<i256> = obj.alloc i256;
    v3.objref<i256> = obj.alloc i256;
    br v0 block1 block2;
block1:
    v4.objref<i256> = call %recover v1;
    jump block2;
block2:
    v5.objref<i256> = phi (v2 block0) (v4 block1);
    return v5;
}
"#,
            |func, aliases, facts| {
                let results: Vec<_> = func
                    .layout
                    .iter_all_insts()
                    .filter_map(|inst| func.dfg.inst_result(inst))
                    .collect();
                let [known, unrelated, opaque, merged] = results.as_slice() else {
                    panic!("four reference results expected")
                };
                let target = RootValue::new(*unrelated);
                let known = facts.may().may_roots(*known);
                // I2/I7: observed roots are not exhaustive in the presence of unknowns.
                assert!(!known.has_unknown());
                assert!(
                    known
                        .observed()
                        .iter()
                        .all(|root| !aliases.roots_may_overlap(root, target))
                );
                assert!(facts.may().may_roots(*opaque).has_unknown());
                assert!(facts.may().may_roots(*merged).has_unknown());
                assert!(facts.complete().exact_projection(*merged).is_none());
            },
        );
    }

    #[test]
    fn repeating_allocation_site_is_not_a_definite_instance() {
        check(
            r#"
target = "evm-ethereum-osaka"
func private %f(v0.i1) {
block0:
    jump block1;
block1:
    v1.objref<i256> = obj.alloc i256;
    br v0 block1 block2;
block2:
    return;
}
"#,
            |func, aliases, facts| {
                let value = func
                    .layout
                    .iter_all_insts()
                    .find_map(|inst| func.dfg.inst_result(inst))
                    .unwrap();
                let projection = facts.complete().exact_projection(value).unwrap();
                assert!(aliases.may_overlap(projection, projection));
                assert!(!aliases.exact_write_covers(projection, projection));
            },
        );
    }
}
