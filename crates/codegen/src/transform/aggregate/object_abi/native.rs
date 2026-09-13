use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    ControlFlowGraph, Function, Module, Signature, Value, ValueId,
    inst::{control_flow, downcast},
};

use super::{
    FuncPlan, ObjectReturnOutParam, RewriteRoot, fresh_root_blocks_are_pairwise_unreachable,
    objref_element_ty, whole_object_slice,
};
use crate::{
    cfg_scc::CfgSccAnalysis,
    module_analysis::{CallGraph, SccBuilder},
    transform::aggregate::{
        ObjectEffectSummaryMap, compute_object_effect_summaries, object_locality,
        object_tracking::AggregateFacts, private_abi, provenance::ProvenanceSnapshot, shape,
    },
};

/// Native objects use stack storage. Promote proven fresh return roots into
/// caller storage, but keep the reference result to preserve borrowed aliases.
pub(crate) fn legalize_native_object_returns(module: &Module) -> Result<(), String> {
    let sccs = SccBuilder::new().compute_scc(&CallGraph::build_graph(module));
    loop {
        let effects = compute_object_effect_summaries(module);
        let mut plans = FxHashMap::default();
        for func in module.funcs() {
            let sig = module.ctx.get_sig(func).expect("function signature exists");
            if !private_abi::is_owned_private_abi_func(&sig) || sccs.scc_of(func).is_cycle {
                continue;
            }
            if let Some(plan) = module
                .func_store
                .view(func, |function| collect_plan(function, &sig, &effects))
            {
                plans.insert(func, plan);
            }
        }
        private_abi::retain_higher_order_safe_plans(module, &mut plans);
        if plans.is_empty() {
            for func in module.funcs() {
                let sig = module.ctx.get_sig(func).expect("function signature exists");
                if sig.linkage().is_external() {
                    continue;
                }
                module
                    .func_store
                    .view(func, |function| check_lifetimes(function, &effects))
                    .map_err(|error| {
                        format!("native reference lifetime in {}: {error}", sig.name())
                    })?;
            }
            return Ok(());
        }

        let old_sigs = private_abi::rewrite_declared_signatures(module, &plans);
        for (&func, plan) in &plans {
            module.func_store.modify(func, |function| {
                ObjectReturnOutParam.rewrite_function(function, plan);
                function.rebuild_users();
            });
        }
        for func in module.funcs() {
            module.func_store.modify(func, |function| {
                if ObjectReturnOutParam.rewrite_calls(function, None, &plans) {
                    function.rebuild_users();
                }
            });
        }
        private_abi::propagate_private_abi_types(module, &old_sigs);
    }
}

fn collect_plan(
    function: &Function,
    sig: &Signature,
    effects: &ObjectEffectSummaryMap,
) -> Option<FuncPlan> {
    let out_ty = sig.single_ret_ty()?;
    let out_elem_ty = objref_element_ty(function.ctx(), out_ty)?;
    if shape::is_reference_aggregate(function.ctx(), out_elem_ty)
        || out_elem_ty.is_obj_ref(function.ctx())
    {
        return None;
    }
    let mut layout_cache = shape::AggregateLayoutCache::default();
    let mut snapshot = ProvenanceSnapshot::new(function, Some(effects));
    let facts = AggregateFacts::for_all_objref_args(function, &mut layout_cache, &mut snapshot);
    let provenance = facts.complete();
    let whole = whole_object_slice(&mut layout_cache, function.ctx(), out_elem_ty);
    let mut fresh = FxHashSet::default();
    let mut allowed = FxHashSet::default();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let Some(ret) =
                downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(inst))
            else {
                continue;
            };
            let value = *ret.arg()?;
            for root in provenance.complete_roots(value)?.iter() {
                allowed.insert(root.value());
                if matches!(function.dfg.value(root.value()), Value::Arg { .. }) {
                    continue;
                }
                // Only whole allocations of the returned T can share its
                // hidden buffer. A fresh subobject needs a different lifetime plan.
                if facts.root_slices().get(&root.value()) != Some(&whole)
                    || provenance
                        .possible_slices_for_root(value, root)?
                        .iter()
                        .any(|slice| *slice != whole)
                {
                    return None;
                }
                fresh.insert(root.value());
            }
        }
    }
    let mut fresh: Vec<ValueId> = fresh.into_iter().collect();
    fresh.sort_unstable();
    if fresh.is_empty() || !fresh_root_blocks_are_pairwise_unreachable(function, &fresh) {
        return None;
    }
    let mut roots = SmallVec::new();
    for root in fresh {
        let rewrite = ObjectReturnOutParam.classify_rewrite_root(
            function,
            root,
            out_ty,
            out_elem_ty,
            effects,
        )?;
        if !matches!(rewrite, RewriteRoot::LocalAlloc { .. })
            || !ObjectReturnOutParam.root_is_rewritable(
                function,
                root,
                facts.root_slices(),
                provenance,
                effects,
                &allowed,
            )
        {
            return None;
        }
        roots.push(rewrite);
    }
    Some(FuncPlan {
        out_ty,
        out_elem_ty,
        roots,
        new_arg_tys: std::iter::once(out_ty)
            .chain(sig.args().iter().copied())
            .collect(),
        new_ret_tys: smallvec![out_ty],
    })
}

fn check_lifetimes(function: &Function, effects: &ObjectEffectSummaryMap) -> Result<(), String> {
    let mut layout_cache = shape::AggregateLayoutCache::default();
    let mut snapshot = ProvenanceSnapshot::new(function, Some(effects));
    let facts = AggregateFacts::for_all_objref_args(function, &mut layout_cache, &mut snapshot);
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);
    let mut sccs = CfgSccAnalysis::new();
    sccs.compute(&cfg);
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if downcast::<&control_flow::Phi>(function.inst_set(), function.dfg.inst(inst))
                .is_some()
                && let Some(result) = function.dfg.inst_result(inst)
                && let Some(scc) = sccs
                    .scc_of(block)
                    .filter(|&scc| sccs.scc_data(scc).is_cycle)
                && facts.may().may_roots(result).observed().iter().any(|root| {
                    function
                        .dfg
                        .value_inst(root.value())
                        .is_some_and(|root_inst| {
                            sccs.scc_of(function.layout.inst_block(root_inst)) == Some(scc)
                        })
                })
            {
                return Err(format!(
                    "unproven loop-carried fresh object at {inst:?}; a static stack slot cannot preserve distinct iterations"
                ));
            }
            let Some(ret) =
                downcast::<&control_flow::Return>(function.inst_set(), function.dfg.inst(inst))
            else {
                continue;
            };
            for &value in ret.args().iter() {
                let ty = function.dfg.value_ty(value);
                if shape::is_reference_aggregate(function.ctx(), ty) {
                    return Err(format!("unproven reference-aggregate return at {inst:?}"));
                }
                if let Some(elem) = objref_element_ty(function.ctx(), ty)
                    && (!ret.returns_single()
                        || shape::is_reference_aggregate(function.ctx(), elem)
                        || elem.is_obj_ref(function.ctx())
                        || !facts.complete().complete_roots(value).is_some_and(|roots| {
                            roots.iter().all(|root| {
                                matches!(function.dfg.value(root.value()), Value::Arg { .. })
                            })
                        }))
                {
                    return Err(format!(
                        "unproven object-reference return at {inst:?}; stack-only native returns must borrow caller storage"
                    ));
                }
            }
        }
    }
    // Also reject roots captured through an argument or reference aggregate;
    // checking only the syntactic return operands misses those escape paths.
    for &root in facts.root_slices().keys() {
        if !matches!(function.dfg.value(root), Value::Arg { .. })
            && !object_locality::object_root_stays_local_with_effects(
                function,
                root,
                function.dfg.value_ty(root),
                effects,
                |_| true,
                false,
            )
        {
            return Err(format!(
                "unproven escape of local object {root:?}; native objects require stack-local lifetimes"
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transform::aggregate::ObjectReturnEffect;
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    fn verified_module(source: &str) -> Module {
        let module = parse_module(&format!("target = \"aarch64-unknown-native\"\n{source}"))
            .unwrap()
            .module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        module
    }

    #[test]
    fn borrowed_unions_survive_calls_and_projections_without_exact_aliases() {
        let module = verified_module(
            r#"
func private %choose(v0.i1, v1.objref<[i64; 2]>, v2.objref<[i64; 2]>) -> objref<[i64; 2]> {
block0:
    br v0 block1 block2;
block1:
    return v1;
block2:
    return v2;
}
func private %forward(v0.i1, v1.objref<[i64; 2]>, v2.objref<[i64; 2]>) -> objref<i64> {
block0:
    v3.objref<[i64; 2]> = call %choose v0 v1 v2;
    v4.objref<i64> = obj.index v3 1.i64;
    return v4;
}
"#,
        );
        legalize_native_object_returns(&module).unwrap();
        let effects = compute_object_effect_summaries(&module);
        for func in module.funcs() {
            let effect = &effects[&func];
            assert_eq!(
                effect.ret_effect,
                ObjectReturnEffect::BorrowedArgs {
                    indices: smallvec![1, 2]
                }
            );
            assert!(!effect.arg_effects[1].local_only);
            assert!(!effect.arg_effects[2].local_only);
            let sig = module.ctx.get_sig(func).unwrap();
            assert_eq!(
                sig.args().len(),
                3,
                "borrowed-only returns need no hidden storage"
            );
            module.func_store.view(func, |function| {
                let mut cache = shape::AggregateLayoutCache::default();
                let mut snapshot = ProvenanceSnapshot::new(function, Some(&effects));
                let facts =
                    AggregateFacts::for_all_objref_args(function, &mut cache, &mut snapshot);
                for block in function.layout.iter_block() {
                    for inst in function.layout.iter_inst(block) {
                        for &result in function.dfg.inst_results(inst) {
                            assert!(facts.complete().exact_projection(result).is_none());
                            assert_eq!(
                                facts
                                    .complete()
                                    .complete_roots(result)
                                    .unwrap()
                                    .iter()
                                    .count(),
                                2
                            );
                        }
                    }
                }
            });
        }
    }

    #[test]
    fn rejects_unproven_stack_only_return_shapes() {
        for source in [
            // A fresh projected field cannot fit the whole allocation into
            // storage sized for the returned scalar.
            r#"func private %escape() -> objref<i64> {
block0:
    v0.objref<[i64; 2]> = obj.alloc [i64; 2];
    v1.objref<i64> = obj.index v0 1.i64;
    obj.store v1 42.i64;
    return v1;
}"#,
            // Both allocations execute, so aliasing them into one out-buffer
            // would change observable identity and mutation semantics.
            r#"func private %escape(v0.i1) -> objref<i64> {
block0:
    v1.objref<i64> = obj.alloc i64;
    v2.objref<i64> = obj.alloc i64;
    obj.store v1 11.i64;
    obj.store v2 22.i64;
    br v0 block1 block2;
block1:
    return v1;
block2:
    return v2;
}"#,
            r#"func private %escape() -> (objref<i64>, objref<i64>) {
block0:
    v0.objref<i64> = obj.alloc i64;
    return (v0, v0);
}"#,
            r#"func private %escape(v0.i1) -> objref<i64> {
block0:
    br v0 block1 block2;
block1:
    v1.objref<i64> = obj.alloc i64;
    return v1;
block2:
    v2.objref<i64> = call %escape 1.i1;
    return v2;
}"#,
            r#"func private %escape(v0.i1) -> objref<i64> {
block0:
    jump block1;
block1:
    v1.objref<i64> = obj.alloc i64;
    br v0 block1 block2;
block2:
    return v1;
}"#,
            r#"type @Refs = {objref<i64>};
func private %escape() -> objref<@Refs> {
block0:
    v0.objref<@Refs> = obj.alloc @Refs;
    v1.objref<i64> = obj.alloc i64;
    v2.objref<objref<i64>> = obj.proj v0 0.i64;
    obj.store v2 v1;
    return v0;
}"#,
            r#"func private %escape(v0.objref<objref<i64>>) {
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v0 v1;
    return;
}"#,
            r#"func private %escape(v0.objref<objref<i64>>) -> objref<i64> {
block0:
    v1.objref<i64> = obj.load v0;
    return v1;
}"#,
        ] {
            let module = verified_module(source);
            let error = legalize_native_object_returns(&module).unwrap_err();
            assert!(
                error.contains("native reference lifetime in escape"),
                "{error}"
            );
        }
    }

    #[test]
    fn rejects_loop_carried_results_from_repeated_fresh_calls() {
        let module = verified_module(
            r#"
func private %fresh(v0.i64) -> objref<i64> {
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v1 v0;
    return v1;
}
func public %run(v0.i64) -> i64 {
block0:
    v1.objref<i64> = call %fresh 0.i64;
    jump block1;
block1:
    v2.objref<i64> = phi (v1 block0) (v4 block1);
    v3.i64 = phi (0.i64 block0) (v5 block1);
    v4.objref<i64> = call %fresh v3;
    v5.i64 = add v3 1.i64;
    v6.i64 = obj.load v2;
    v7.i1 = lt v5 v0;
    br v7 block1 block2;
block2:
    return v6;
}
"#,
        );
        let error = legalize_native_object_returns(&module).unwrap_err();
        assert!(error.contains("loop-carried fresh object"), "{error}");
    }

    #[test]
    fn mixed_return_rewrite_keeps_verified_reference_results() {
        let module = verified_module(
            r#"
func private %choose(v0.i1, v1.objref<i64>) -> objref<i64> {
block0:
    br v0 block1 block2;
block1:
    v2.objref<i64> = obj.alloc i64;
    obj.store v2 42.i64;
    return v2;
block2:
    return v1;
}
func private %forward(v0.i1, v1.objref<i64>) -> objref<i64> {
block0:
    v2.objref<i64> = call %choose v0 v1;
    return v2;
}
"#,
        );
        legalize_native_object_returns(&module).unwrap();
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        for func in module.funcs() {
            let sig = module.ctx.get_sig(func).unwrap();
            assert_eq!(sig.args().len(), 3);
            assert!(sig.single_ret_ty().unwrap().is_obj_ref(&module.ctx));
        }
        // Re-running the pass must not add another hidden buffer.
        legalize_native_object_returns(&module).unwrap();
        assert!(
            module
                .funcs()
                .iter()
                .all(|&func| module.ctx.get_sig(func).unwrap().args().len() == 3)
        );
    }
}
