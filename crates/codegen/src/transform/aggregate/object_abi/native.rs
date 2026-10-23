use std::ops::ControlFlow;

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    ControlFlowGraph, Function, Module, Signature, Value, ValueId,
    inst::{control_flow, data},
};

use super::{
    FuncPlan, ObjectReturnOutParam, RewriteRoot, fresh_root_blocks_are_pairwise_unreachable,
    whole_object_slice,
};
use crate::{
    cfg_scc::CfgSccAnalysis,
    liveness::{Liveness, phi_args_for_edge},
    module_analysis::{CallGraph, SccBuilder},
    transform::aggregate::{
        ObjectEffectSummaryMap, compute_object_effect_summaries,
        object_locality::{self, SpecialObjectUse},
        object_tracking::{AggregateFacts, objref_element_ty},
        private_abi,
        provenance::{ProvenanceSnapshot, RootValue},
        shape,
    },
};

/// Promote proven fresh stack return roots into caller storage, but keep the
/// reference result to preserve borrowed aliases. Explicit heap exports retain
/// their original allocation instead.
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
            let Some(ret) = function.dfg.downcast::<&control_flow::Return>(inst) else {
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
    let heap_roots = native_heap_object_roots(function, effects);
    if fresh.is_empty()
        || fresh.iter().any(|root| heap_roots.contains(root))
        || !fresh_root_blocks_are_pairwise_unreachable(function, &fresh)
    {
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

/// Heap materialization exports the original object, including its aliases.
/// Propagate that requirement through callee summaries before choosing storage;
/// allocating a copy at the export would break mutations through existing views.
pub(crate) fn native_heap_object_roots(
    function: &Function,
    effects: &ObjectEffectSummaryMap,
) -> FxHashSet<ValueId> {
    function
        .layout
        .iter_all_insts()
        .filter(|&inst| function.dfg.downcast::<&data::ObjAlloc>(inst).is_some())
        .filter_map(|inst| function.dfg.inst_result(inst))
        .filter(|&root| {
            object_locality::walk_object_root_uses_with_effects(function, root, effects, |usage| {
                match usage {
                    SpecialObjectUse::MaterializeHeap => ControlFlow::Break(()),
                    SpecialObjectUse::Call { value, call, .. }
                        if effects.get(call.callee()).is_some_and(|summary| {
                            call.args().iter().enumerate().any(|(index, arg)| {
                                *arg == value
                                    && summary
                                        .arg_effects
                                        .get(index)
                                        .is_some_and(|effect| effect.materializes_heap)
                            })
                        }) =>
                    {
                        ControlFlow::Break(())
                    }
                    _ => ControlFlow::Continue(()),
                }
            })
            .is_some()
        })
        .collect()
}

fn check_lifetimes(function: &Function, effects: &ObjectEffectSummaryMap) -> Result<(), String> {
    let heap_roots = native_heap_object_roots(function, effects);
    let mut layout_cache = shape::AggregateLayoutCache::default();
    let mut snapshot = ProvenanceSnapshot::new(function, Some(effects));
    let facts = AggregateFacts::for_all_objref_args(function, &mut layout_cache, &mut snapshot);
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);
    let mut sccs = CfgSccAnalysis::new();
    sccs.compute(&cfg);
    let mut loop_roots = FxHashMap::default();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if function.dfg.downcast::<&control_flow::Phi>(inst).is_some()
                && let Some(result) = function.dfg.inst_result(inst)
                && let Some(scc) = sccs
                    .scc_of(block)
                    .filter(|&scc| sccs.scc_data(scc).is_cycle)
            {
                for root in facts.may().may_roots(result).observed().iter() {
                    if let Some(root_inst) = function.dfg.value_inst(root.value())
                        && !heap_roots.contains(&root.value())
                        && sccs.scc_of(function.layout.inst_block(root_inst)) == Some(scc)
                    {
                        loop_roots.insert(root_inst, root.value());
                    }
                }
            }
            let Some(ret) = function.dfg.downcast::<&control_flow::Return>(inst) else {
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
                                    || heap_roots.contains(&root.value())
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
    if !loop_roots.is_empty() {
        // A cyclic allocation can reuse one stack slot only after every alias
        // of its previous instance has died. A phi alone does not imply overlap:
        // value loops commonly read the old object before constructing the next.
        // Check before the allocation, excluding its newly defined result.
        let mut liveness = Liveness::new();
        liveness.compute(function, &cfg);
        for block in cfg.post_order() {
            let mut live = liveness.block_live_outs(block).clone();
            // Phi inputs are uses at the predecessor's tail. Block liveness
            // can omit inputs defined here, including aliases carried only
            // along a backedge, so seed them before scanning allocations.
            for &succ in cfg.succs_of(block) {
                for value in phi_args_for_edge(function, block, succ) {
                    if !function.dfg.value_is_imm(value) {
                        live.insert(value);
                    }
                }
            }
            let insts: Vec<_> = function.layout.iter_inst(block).collect();
            for inst in insts.into_iter().rev() {
                for &result in function.dfg.inst_results(inst) {
                    live.remove(result);
                }
                if !function.dfg.is_phi(inst) {
                    function.dfg.inst(inst).for_each_value(&mut |value| {
                        if !function.dfg.value_is_imm(value) {
                            live.insert(value);
                        }
                    });
                }
                if let Some(&root) = loop_roots.get(&inst)
                    && let Some(alias) = live.iter().find(|&value| {
                        let roots = facts.may().may_roots(value);
                        roots.has_unknown() || roots.observed().contains(RootValue::new(root))
                    })
                {
                    return Err(format!(
                        "unproven loop-carried fresh object at {inst:?}: {alias:?} remains live when {root:?} is allocated again; a static stack slot cannot preserve distinct iterations"
                    ));
                }
            }
        }
    }
    // Also reject roots captured through an argument or reference aggregate;
    // checking only the syntactic return operands misses those escape paths.
    // A reference may rest in an SSA aggregate or another local allocation
    // only when its object lives as long as the frame: a slot reused by a
    // later iteration would leave the held reference naming the new object.
    for &root in facts.root_slices().keys() {
        if !matches!(function.dfg.value(root), Value::Arg { .. })
            && !heap_roots.contains(&root)
            && !object_locality::object_root_stays_local_with_effects(
                function,
                root,
                effects,
                |_| true,
                false,
                function.dfg.value_inst(root).is_none_or(|inst| {
                    sccs.scc_of(function.layout.inst_block(inst))
                        .is_none_or(|scc| !sccs.scc_data(scc).is_cycle)
                }),
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
    fn accepts_local_projected_arguments_through_borrowing_calls() {
        let module = verified_module(
            r#"
type @pair = { i64, i64 };
type @nested = { [@pair; 2] };
func private %borrow(v0.objref<i64>) -> objref<i64> {
block0:
    return v0;
}
func private %write(v0.objref<i64>) {
block0:
    obj.store v0 42.i64;
    return;
}
func public %run() -> i64 {
block0:
    v0.objref<@nested> = obj.alloc @nested;
    v1.objref<[@pair; 2]> = obj.proj v0 0.i64;
    v2.objref<@pair> = obj.index v1 1.i64;
    v3.objref<i64> = obj.proj v2 1.i64;
    v4.objref<i64> = call %borrow v3;
    call %write v4;
    v5.i64 = obj.load v3;
    return v5;
}
"#,
        );
        legalize_native_object_returns(&module).unwrap();
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
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
            // A callee capture remains an escape even when it has an exact
            // summary instead of an unknown-object barrier.
            r#"func private %retain(v0.objref<i64>, v1.objref<objref<i64>>) {
block0:
    obj.store v1 v0;
    return;
}
func private %escape(v0.objref<objref<i64>>) {
block0:
    v1.objref<i64> = obj.alloc i64;
    call %retain v1 v0;
    return;
}"#,
            r#"func private %retain(v0.objref<i64>, v1.objref<objref<i64>>) {
block0:
    obj.store v1 v0;
    return;
}
func private %escape(v0.objref<objref<i64>>) {
block0:
    v1.objref<[i64; 2]> = obj.alloc [i64; 2];
    v2.objref<i64> = obj.index v1 1.i64;
    call %retain v2 v0;
    return;
}"#,
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
    fn loop_carried_projected_alias_must_die_before_reallocation() {
        for reads_before_allocation in [true, false] {
            let read = "v9.i64 = obj.load v8;";
            let source = format!(
                r#"
func private %borrow(v0.objref<[i64; 2]>) -> objref<i64> {{
block0:
    v1.objref<i64> = obj.index v0 1.i64;
    return v1;
}}
func public %run(v0.i64) -> i64 {{
block0:
    v1.objref<[i64; 2]> = obj.alloc [i64; 2];
    v6.objref<i64> = obj.index v1 1.i64;
    obj.store v6 42.i64;
    jump block1;
block1:
    v2.objref<[i64; 2]> = phi (v1 block0) (v4 block1);
    v3.i64 = phi (0.i64 block0) (v5 block1);
    v8.objref<i64> = call %borrow v2;
    {before}
    v4.objref<[i64; 2]> = obj.alloc [i64; 2];
    v10.objref<i64> = obj.index v4 1.i64;
    obj.store v10 v3;
    {after}
    v5.i64 = add v3 1.i64;
    v7.i1 = lt v5 v0;
    br v7 block1 block2;
block2:
    return v9;
}}
"#,
                before = if reads_before_allocation { read } else { "" },
                after = if reads_before_allocation { "" } else { read },
            );
            let module = verified_module(&source);
            let result = legalize_native_object_returns(&module);
            if reads_before_allocation {
                result.unwrap();
                let report =
                    verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
                assert!(!report.has_errors(), "{report}");
            } else {
                let error = result.unwrap_err();
                assert!(error.contains("loop-carried fresh object"), "{error}");
            }
        }
    }

    #[test]
    fn loop_carried_materialized_alias_must_die_before_reallocation() {
        for (alias, address, backedge) in [
            ("v8.*i64 = obj.materialize.stack v2;", "v8", "block1"),
            (
                "v8.*i64 = obj.materialize.stack v2;\n\
                 v10.*i8 = bitcast v8 *i8;\n\
                 v11.*i8 = gep v10 0.i64;\n\
                 v12.*i64 = bitcast v11 *i64;",
                "v12",
                "block1",
            ),
            (
                "v8.*i64 = obj.materialize.stack v2;\n\
                 jump block3;\n\
                 block3:\n\
                 v10.*i64 = phi (v8 block1);",
                "v10",
                "block3",
            ),
        ] {
            for reads_before_allocation in [true, false] {
                let read = format!("v9.i64 = mload {address} i64;");
                let source = format!(
                    r#"
func public %run(v0.i64) -> i64 {{
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v1 42.i64;
    jump block1;
block1:
    v2.objref<i64> = phi (v1 block0) (v4 {backedge});
    v3.i64 = phi (0.i64 block0) (v5 {backedge});
    {alias}
    {before}
    v4.objref<i64> = obj.alloc i64;
    obj.store v4 v3;
    {after}
    v5.i64 = add v3 1.i64;
    v7.i1 = lt v5 v0;
    br v7 block1 block2;
block2:
    return v9;
}}
"#,
                    before = if reads_before_allocation { &read } else { "" },
                    after = if reads_before_allocation { "" } else { &read },
                );
                let module = verified_module(&source);
                let result = legalize_native_object_returns(&module);
                if reads_before_allocation {
                    result.unwrap();
                } else {
                    let error = result.expect_err(&source);
                    assert!(error.contains("loop-carried fresh object"), "{error}");
                }
            }
        }
    }

    #[test]
    fn loop_carried_raw_pointer_identifies_repeated_allocation() {
        for reads_before_allocation in [true, false] {
            let read = "v9.i64 = mload v2 i64;";
            let source = format!(
                r#"
func public %run(v0.i64) -> i64 {{
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v1 42.i64;
    v6.*i64 = obj.materialize.stack v1;
    jump block1;
block1:
    v2.*i64 = phi (v6 block0) (v8 block1);
    v3.i64 = phi (0.i64 block0) (v5 block1);
    {before}
    v4.objref<i64> = obj.alloc i64;
    obj.store v4 v3;
    v8.*i64 = obj.materialize.stack v4;
    {after}
    v5.i64 = add v3 1.i64;
    v7.i1 = lt v5 v0;
    br v7 block1 block2;
block2:
    return v9;
}}
"#,
                before = if reads_before_allocation { read } else { "" },
                after = if reads_before_allocation { "" } else { read },
            );
            let module = verified_module(&source);
            let result = legalize_native_object_returns(&module);
            if reads_before_allocation {
                result.unwrap();
            } else {
                let error = result.expect_err(&source);
                assert!(error.contains("loop-carried fresh object"), "{error}");
            }
        }
    }

    #[test]
    fn loop_carried_reference_two_iterations_old_is_still_live() {
        for reads_before_allocation in [true, false] {
            let read = "v9.i64 = obj.load v6;";
            let source = format!(
                r#"
func public %run(v0.i64) -> i64 {{
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v1 42.i64;
    jump block1;
block1:
    v2.objref<i64> = phi (v1 block0) (v4 block1);
    v6.objref<i64> = phi (v1 block0) (v2 block1);
    v3.i64 = phi (0.i64 block0) (v5 block1);
    v8.i64 = obj.load v2;
    {before}
    v4.objref<i64> = obj.alloc i64;
    obj.store v4 v3;
    {after}
    v5.i64 = add v3 1.i64;
    v7.i1 = lt v5 v0;
    br v7 block1 block2;
block2:
    v10.i64 = add v8 v9;
    return v10;
}}
"#,
                before = if reads_before_allocation { read } else { "" },
                after = if reads_before_allocation { "" } else { read },
            );
            let module = verified_module(&source);
            let error = legalize_native_object_returns(&module).expect_err(&source);
            assert!(error.contains("loop-carried fresh object"), "{error}");
        }
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

    #[test]
    fn heap_exported_holders_put_what_they_reference_on_the_heap() {
        // `v0` rests in `v2`'s memory, through an SSA pair; exporting `v2` to
        // the heap exports `v0` with it.
        let module = verified_module(
            r#"
type @pair = { i64, objref<i64> };
func private %export(v0.i64) -> *@pair {
block0:
    v1.objref<i64> = obj.alloc i64;
    obj.store v1 v0;
    v2.@pair = insert_value undef.@pair 1.i64 v1;
    v3.objref<@pair> = obj.alloc @pair;
    obj.store v3 v2;
    v4.*@pair = obj.materialize.heap v3;
    return v4;
}
"#,
        );
        let effects = compute_object_effect_summaries(&module);
        let func = module.funcs()[0];
        module.func_store.view(func, |function| {
            let roots = native_heap_object_roots(function, &effects);
            assert!(roots.contains(&ValueId::from_u32(1)), "{roots:?}");
            assert!(roots.contains(&ValueId::from_u32(3)), "{roots:?}");
            check_lifetimes(function, &effects).unwrap();
        });
    }

    /// The lifetime check and heap roots of `%f`, among `source`'s functions.
    fn check_f(source: &str) -> (Result<(), String>, FxHashSet<ValueId>) {
        let module = verified_module(source);
        let effects = compute_object_effect_summaries(&module);
        let f = module
            .funcs()
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == "f"))
            .expect("f exists");
        module.func_store.view(f, |function| {
            (
                check_lifetimes(function, &effects),
                native_heap_object_roots(function, &effects),
            )
        })
    }

    #[test]
    fn local_references_stay_local_through_fields_nested_holders_and_calls() {
        for (name, source) in [
            // Only field 0 carries `v2`; field 1 carries the argument `v0`,
            // which may rest in the caller's `v1`.
            (
                "field",
                r#"
type @refs = { objref<i64>, objref<i64> };
func private %f(v0.objref<i64>, v1.objref<objref<i64>>) -> i64 {
block0:
    v2.objref<i64> = obj.alloc i64;
    obj.store v2 1.i64;
    v3.@refs = insert_value undef.@refs 0.i64 v2;
    v4.@refs = insert_value v3 1.i64 v0;
    v5.objref<i64> = extract_value v4 1.i64;
    obj.store v1 v5;
    v6.objref<i64> = extract_value v4 0.i64;
    v7.i64 = obj.load v6;
    return v7;
}
"#,
            ),
            // `%read` only reads through the holder it borrows.
            (
                "holder_call",
                r#"
type @holder = { objref<i64> };
func private %read(v0.objref<@holder>) -> i64 {
block0:
    v1.objref<objref<i64>> = obj.proj v0 0.i64;
    v2.objref<i64> = obj.load v1;
    v3.i64 = obj.load v2;
    return v3;
}
func private %f() -> i64 {
block0:
    v0.objref<i64> = obj.alloc i64;
    obj.store v0 5.i64;
    v1.objref<@holder> = obj.alloc @holder;
    v2.objref<objref<i64>> = obj.proj v1 0.i64;
    obj.store v2 v0;
    v3.i64 = call %read v1;
    return v3;
}
"#,
            ),
            // `%slot` returns a projection of the holder it borrows.
            (
                "borrowed_holder_projection",
                r#"
type @holder = { objref<i64> };
func private %slot(v0.objref<@holder>) -> objref<objref<i64>> {
block0:
    v1.objref<objref<i64>> = obj.proj v0 0.i64;
    return v1;
}
func private %f() -> i64 {
block0:
    v0.objref<i64> = obj.alloc i64;
    obj.store v0 5.i64;
    v1.objref<@holder> = obj.alloc @holder;
    v2.objref<objref<i64>> = obj.proj v1 0.i64;
    obj.store v2 v0;
    v3.objref<objref<i64>> = call %slot v1;
    v4.objref<i64> = obj.load v3;
    v5.i64 = obj.load v4;
    return v5;
}
"#,
            ),
            // The holder's raw pointer is never read through.
            (
                "materialized_holder",
                r#"
type @holder = { objref<i64> };
func private %f() -> i64 {
block0:
    v0.objref<i64> = obj.alloc i64;
    obj.store v0 5.i64;
    v1.objref<@holder> = obj.alloc @holder;
    v2.objref<objref<i64>> = obj.proj v1 0.i64;
    obj.store v2 v0;
    v3.*@holder = obj.materialize.stack v1;
    v4.i64 = obj.load v0;
    return v4;
}
"#,
            ),
            // `v0` rests in `v1`, which rests in `v3`.
            (
                "nested_holders",
                r#"
type @holder = { objref<i64> };
type @outer = { i64, objref<@holder> };
func private %f() -> i64 {
block0:
    v0.objref<i64> = obj.alloc i64;
    obj.store v0 5.i64;
    v1.objref<@holder> = obj.alloc @holder;
    v2.objref<objref<i64>> = obj.proj v1 0.i64;
    obj.store v2 v0;
    v3.objref<@outer> = obj.alloc @outer;
    v4.objref<objref<@holder>> = obj.proj v3 1.i64;
    obj.store v4 v1;
    v5.objref<@holder> = obj.load v4;
    v6.objref<objref<i64>> = obj.proj v5 0.i64;
    v7.objref<i64> = obj.load v6;
    v8.i64 = obj.load v7;
    return v8;
}
"#,
            ),
        ] {
            let (lifetimes, heap_roots) = check_f(source);
            assert_eq!(lifetimes, Ok(()), "{name}");
            assert!(heap_roots.is_empty(), "{name}: {heap_roots:?}");
        }
    }

    #[test]
    fn local_references_stay_local_through_callees_that_only_pack_them() {
        // `%pick` packs the reference beside a value and, past a join with no
        // pair, reads only the value back.
        let (lifetimes, _) = check_f(
            r#"
type @pair = { i64, objref<i64> };
func private %pick(v0.objref<i64>, v1.i1) -> i64 {
block0:
    v2.i64 = obj.load v0;
    v3.@pair = insert_value undef.@pair 0.i64 v2;
    v4.@pair = insert_value v3 1.i64 v0;
    br v1 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v5.@pair = phi (v4 block1) (undef.@pair block2);
    br v1 block4 block5;
block4:
    v6.i64 = extract_value v5 0.i64;
    return v6;
block5:
    return 0.i64;
}
func private %f() -> i64 {
block0:
    v0.objref<i64> = obj.alloc i64;
    obj.store v0 5.i64;
    v1.i64 = call %pick v0 1.i1;
    return v1;
}
"#,
        );
        assert_eq!(lifetimes, Ok(()));
        // `%keep` extracts the packed reference and stores it beyond the frame.
        let (lifetimes, _) = check_f(
            r#"
type @pair = { i64, objref<i64> };
func private %keep(v0.objref<i64>, v1.objref<objref<i64>>) {
block0:
    v2.@pair = insert_value undef.@pair 0.i64 1.i64;
    v3.@pair = insert_value v2 1.i64 v0;
    v4.objref<i64> = extract_value v3 1.i64;
    obj.store v1 v4;
    return;
}
func private %f(v0.objref<objref<i64>>) {
block0:
    v1.objref<i64> = obj.alloc i64;
    call %keep v1 v0;
    return;
}
"#,
        );
        assert!(
            lifetimes
                .as_ref()
                .is_err_and(|error| error.starts_with("unproven escape of local object")),
            "{lifetimes:?}"
        );
    }

    #[test]
    fn heap_exports_reach_references_through_holder_calls_and_nested_holders() {
        for (name, source, roots) in [
            // `%export` exports the holder `v1`, and with it `v0`.
            (
                "holder_call",
                r#"
type @holder = { objref<i64> };
func private %export(v0.objref<@holder>) -> *@holder {
block0:
    v1.*@holder = obj.materialize.heap v0;
    return v1;
}
func private %f() -> *@holder {
block0:
    v0.objref<i64> = obj.alloc i64;
    obj.store v0 5.i64;
    v1.objref<@holder> = obj.alloc @holder;
    v2.objref<objref<i64>> = obj.proj v1 0.i64;
    obj.store v2 v0;
    v3.*@holder = call %export v1;
    return v3;
}
"#,
                [0, 1].as_slice(),
            ),
            // Exporting `v3` exports `v1`, which holds `v0`.
            (
                "nested_holders",
                r#"
type @holder = { objref<i64> };
type @outer = { objref<@holder> };
func private %f() -> *@outer {
block0:
    v0.objref<i64> = obj.alloc i64;
    obj.store v0 5.i64;
    v1.objref<@holder> = obj.alloc @holder;
    v2.objref<objref<i64>> = obj.proj v1 0.i64;
    obj.store v2 v0;
    v3.objref<@outer> = obj.alloc @outer;
    v4.objref<objref<@holder>> = obj.proj v3 0.i64;
    obj.store v4 v1;
    v5.*@outer = obj.materialize.heap v3;
    return v5;
}
"#,
                [0, 1, 3].as_slice(),
            ),
        ] {
            let (lifetimes, heap_roots) = check_f(source);
            assert_eq!(lifetimes, Ok(()), "{name}");
            let expected = roots.iter().copied().map(ValueId::from_u32).collect();
            assert_eq!(heap_roots, expected, "{name}");
        }
    }

    #[test]
    fn local_references_recovered_from_fields_holders_and_calls_cannot_escape() {
        let types = "type @refs = { objref<i64>, objref<i64> };\n\
             type @holder = { objref<i64> };\n\
             type @outer = { i64, objref<@holder> };\n\
             type @slot = enum { #Empty, #Full(objref<i64>) };";
        for (name, helper, body) in [
            // The carrying field of a pair that also holds an argument.
            (
                "field",
                "",
                "v3.@refs = insert_value undef.@refs 0.i64 v1;\n\
                 v4.@refs = insert_value v3 1.i64 v2;\n\
                 v5.objref<i64> = extract_value v4 0.i64;\n\
                 obj.store v0 v5;",
            ),
            // The payload of an enum value.
            (
                "variant",
                "",
                "v3.@slot = enum.make @slot #Full (v1);\n\
                 v4.objref<i64> = enum.extract v3 #Full 0.i8;\n\
                 obj.store v0 v4;",
            ),
            // A holder inside a holder, unpacked again.
            (
                "nested_holders",
                "",
                "v3.objref<@holder> = obj.alloc @holder;\n\
                 v4.objref<objref<i64>> = obj.proj v3 0.i64;\n\
                 obj.store v4 v1;\n\
                 v5.objref<@outer> = obj.alloc @outer;\n\
                 v6.objref<objref<@holder>> = obj.proj v5 1.i64;\n\
                 obj.store v6 v3;\n\
                 v7.objref<@holder> = obj.load v6;\n\
                 v8.objref<objref<i64>> = obj.proj v7 0.i64;\n\
                 v9.objref<i64> = obj.load v8;\n\
                 obj.store v0 v9;",
            ),
            // A read through the holder's raw pointer, which recovers the
            // reference as bits the walk cannot follow.
            (
                "materialized_holder_read",
                "",
                "v3.objref<@holder> = obj.alloc @holder;\n\
                 v4.objref<objref<i64>> = obj.proj v3 0.i64;\n\
                 obj.store v4 v1;\n\
                 v5.*@holder = obj.materialize.stack v3;\n\
                 v6.i64 = mload v5 i64;",
            ),
            // A callee that moves the held reference into another argument.
            (
                "holder_call_capture",
                "func private %move(v0.objref<@holder>, v1.objref<objref<i64>>) {\n\
                 block0:\n\
                     v2.objref<objref<i64>> = obj.proj v0 0.i64;\n\
                     v3.objref<i64> = obj.load v2;\n\
                     obj.store v1 v3;\n\
                     return;\n\
                 }",
                "v3.objref<@holder> = obj.alloc @holder;\n\
                 v4.objref<objref<i64>> = obj.proj v3 0.i64;\n\
                 obj.store v4 v1;\n\
                 call %move v3 v0;",
            ),
            // A projection a callee borrows from the holder.
            (
                "borrowed_holder_projection",
                "func private %slot(v0.objref<@holder>) -> objref<objref<i64>> {\n\
                 block0:\n\
                     v1.objref<objref<i64>> = obj.proj v0 0.i64;\n\
                     return v1;\n\
                 }",
                "v3.objref<@holder> = obj.alloc @holder;\n\
                 v4.objref<objref<i64>> = obj.proj v3 0.i64;\n\
                 obj.store v4 v1;\n\
                 v5.objref<objref<i64>> = call %slot v3;\n\
                 v6.objref<i64> = obj.load v5;\n\
                 obj.store v0 v6;",
            ),
            // A callee that returns the held reference.
            (
                "holder_call_return",
                "func private %unwrap(v0.objref<@holder>) -> objref<i64> {\n\
                 block0:\n\
                     v1.objref<objref<i64>> = obj.proj v0 0.i64;\n\
                     v2.objref<i64> = obj.load v1;\n\
                     return v2;\n\
                 }",
                "v3.objref<@holder> = obj.alloc @holder;\n\
                 v4.objref<objref<i64>> = obj.proj v3 0.i64;\n\
                 obj.store v4 v1;\n\
                 v5.objref<i64> = call %unwrap v3;\n\
                 obj.store v0 v5;",
            ),
        ] {
            let (lifetimes, _) = check_f(&format!(
                "{types}\n{helper}\nfunc private %f(v0.objref<objref<i64>>, v2.objref<i64>) {{\n\
                 block0:\n\
                     v1.objref<i64> = obj.alloc i64;\n\
                     obj.store v1 1.i64;\n\
                     {body}\n\
                     return;\n\
                 }}"
            ));
            assert!(
                lifetimes
                    .as_ref()
                    .is_err_and(|error| error.starts_with("unproven escape of local object")),
                "{name}: {lifetimes:?}"
            );
        }
    }
}
