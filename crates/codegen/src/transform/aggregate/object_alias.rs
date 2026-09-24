//! Semantic object overlap, separate from exact projection coordinates (I1-I3).
//!
//! This table describes every direct origin in the function, independently of
//! the roots selected for an optimization. Missing origins are unknown, never
//! evidence of separation. It contains no locality or initialization claims.

use rustc_hash::FxHashMap;
use sonatina_ir::{
    ControlFlowGraph, Function, ValueId,
    inst::{control_flow, data, downcast},
};

use crate::cfg_scc::CfgSccAnalysis;

use super::{
    ObjectEffectSummaryMap, ObjectReturnEffect,
    provenance::{MayRootSet, Projection, RootValue},
};

#[derive(Clone, Copy, Debug)]
enum ObjectOrigin {
    Incoming,
    Fresh { repeating: bool },
}

pub(crate) struct ObjectAliasFacts {
    origins: FxHashMap<ValueId, ObjectOrigin>,
}

impl ObjectAliasFacts {
    pub(crate) fn new(func: &Function, effects: Option<&ObjectEffectSummaryMap>) -> Self {
        let mut origins = FxHashMap::default();
        for &arg in &func.arg_values {
            if func.dfg.value_ty(arg).is_obj_ref(func.ctx()) {
                origins.insert(arg, ObjectOrigin::Incoming);
            }
        }
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let mut sccs = CfgSccAnalysis::new();
        sccs.compute(&cfg);
        for block in func.layout.iter_block() {
            // Disconnected code has no dynamic-instance proof from this CFG.
            let repeating = sccs
                .scc_of(block)
                .is_none_or(|scc| sccs.scc_data(scc).is_cycle);
            for inst in func.layout.iter_inst(block) {
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
                    origins.insert(*result, ObjectOrigin::Fresh { repeating });
                }
            }
        }
        Self { origins }
    }

    pub(crate) fn is_fresh(&self, root: RootValue) -> bool {
        matches!(
            self.origins.get(&root.value()),
            Some(ObjectOrigin::Fresh { .. })
        )
    }

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
                Some(ObjectOrigin::Fresh { .. } | ObjectOrigin::Incoming)
            ) | (
                Some(ObjectOrigin::Incoming),
                Some(ObjectOrigin::Fresh { .. })
            )
        )
    }

    pub(crate) fn may_roots_overlap(&self, roots: MayRootSet<'_>, target: RootValue) -> bool {
        // I2/I7: observed roots are not exhaustive in the presence of unknowns.
        roots.has_unknown()
            || roots
                .observed()
                .iter()
                .any(|root| self.roots_may_overlap(root, target))
    }

    pub(crate) fn may_overlap(&self, lhs: Projection, rhs: Projection) -> bool {
        if lhs.root_value != rhs.root_value {
            return self.roots_may_overlap(lhs.root_value, rhs.root_value);
        }
        lhs.slice.first_leaf < rhs.slice.first_leaf.saturating_add(rhs.slice.leaf_count)
            && rhs.slice.first_leaf < lhs.slice.first_leaf.saturating_add(lhs.slice.leaf_count)
    }

    pub(crate) fn single_instance(&self, root: RootValue) -> bool {
        matches!(
            self.origins.get(&root.value()),
            Some(ObjectOrigin::Incoming | ObjectOrigin::Fresh { repeating: false })
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
            let aliases = ObjectAliasFacts::new(func, Some(&effects));
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
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
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
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .filter_map(|inst| func.dfg.inst_result(inst))
                    .collect();
                let [known, unrelated, opaque, merged] = results.as_slice() else {
                    panic!("four reference results expected")
                };
                let target = RootValue::new(*unrelated);
                assert!(!aliases.may_roots_overlap(facts.may().may_roots(*known), target));
                assert!(aliases.may_roots_overlap(facts.may().may_roots(*opaque), target));
                assert!(aliases.may_roots_overlap(facts.may().may_roots(*merged), target));
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
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .find_map(|inst| func.dfg.inst_result(inst))
                    .unwrap();
                let projection = facts.complete().exact_projection(value).unwrap();
                assert!(aliases.may_overlap(projection, projection));
                assert!(!aliases.exact_write_covers(projection, projection));
            },
        );
    }
}
