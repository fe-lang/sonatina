use rustc_hash::FxHashMap;
use sonatina_ir::{
    ControlFlowGraph, Function, Module, ValueId,
    inst::{control_flow, data},
};

use super::{
    ObjectEffectSummaryMap, compute_object_effect_summaries,
    object_tracking::AggregateFacts,
    provenance::{ProvenanceSnapshot, RootValue},
    shape,
};
use crate::{
    cfg_scc::CfgSccAnalysis,
    liveness::{Liveness, phi_args_for_edge},
};

/// Rejects IR that certainly breaks the frame lifetime of `obj.alloc`: an
/// instance lives until its function returns or its allocation runs again.
/// Frontends guarantee the rule, so native code gives each allocation one
/// stack slot without an escape proof. This finds only uses the IR itself
/// commits to: a return of a reference into a local allocation, and a
/// reference to an earlier instance that is still live when its allocation
/// runs again. References with unknown provenance are trusted.
pub(crate) fn check_frame_lifetimes(module: &Module) -> Result<(), String> {
    let effects = compute_object_effect_summaries(module);
    for func in module.funcs() {
        let sig = module.ctx.get_sig(func).expect("function signature exists");
        if sig.linkage().is_external() {
            continue;
        }
        module
            .func_store
            .view(func, |function| check_function(function, &effects))
            .map_err(|error| format!("frame object lifetime in {}: {error}", sig.name()))?;
    }
    Ok(())
}

fn check_function(function: &Function, effects: &ObjectEffectSummaryMap) -> Result<(), String> {
    let mut layout_cache = shape::AggregateLayoutCache::default();
    let mut snapshot = ProvenanceSnapshot::new(function, Some(effects));
    let facts = AggregateFacts::for_all_objref_args(function, &mut layout_cache, &mut snapshot);
    let is_allocation = |root: ValueId| {
        function
            .dfg
            .value_inst(root)
            .is_some_and(|inst| function.dfg.downcast::<&data::ObjAlloc>(inst).is_some())
    };
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
                        && is_allocation(root.value())
                        && sccs.scc_of(function.layout.inst_block(root_inst)) == Some(scc)
                    {
                        loop_roots.insert(root_inst, root.value());
                    }
                }
            }
            if let Some(ret) = function.dfg.downcast::<&control_flow::Return>(inst)
                && let Some(root) = ret.args().iter().find_map(|&value| {
                    facts
                        .may()
                        .may_roots(value)
                        .observed()
                        .iter()
                        .find(|root| is_allocation(root.value()))
                })
            {
                return Err(format!(
                    "{inst:?} returns a reference to local object {:?}",
                    root.value()
                ));
            }
        }
    }
    if loop_roots.is_empty() {
        return Ok(());
    }
    // Scan backward from each block's live-out set to find the values live
    // just before a cyclic allocation. Phi inputs are uses at the
    // predecessor's tail, which block liveness can omit when the input is
    // defined in the predecessor itself, so seed them first.
    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);
    for block in cfg.post_order() {
        let mut live = liveness.block_live_outs(block).clone();
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
                    facts
                        .may()
                        .may_roots(value)
                        .observed()
                        .contains(RootValue::new(root))
                })
            {
                return Err(format!(
                    "{alias:?} refers to an earlier instance of {root:?} when {inst:?} runs again"
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use smallvec::smallvec;
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use super::*;
    use crate::transform::aggregate::ObjectReturnEffect;

    fn verified_module(source: &str) -> Module {
        let module = parse_module(&format!("target = \"aarch64-unknown-native\"\n{source}"))
            .unwrap()
            .module;
        let report = verify_module(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        assert!(!report.has_errors(), "{report}");
        module
    }

    fn assert_earlier_instance_error(result: Result<(), String>, source: &str) {
        let error = result.expect_err(source);
        assert!(error.contains("refers to an earlier instance"), "{error}");
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
        check_frame_lifetimes(&module).unwrap();
    }

    #[test]
    fn borrowed_unions_keep_their_roots_through_calls_and_projections() {
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
        check_frame_lifetimes(&module).unwrap();
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
    fn trusts_references_held_by_holders_and_callees() {
        for source in [
            // A callee stores the reference in a caller's holder.
            r#"func private %retain(v0.objref<i64>, v1.objref<objref<i64>>) {
block0:
    obj.store v1 v0;
    return;
}
func private %f(v0.objref<objref<i64>>) {
block0:
    v1.objref<i64> = obj.alloc i64;
    call %retain v1 v0;
    return;
}"#,
            // The reference rests in an argument through an SSA pair.
            r#"type @pair = { i64, objref<i64> };
func private %f(v0.objref<@pair>) {
block0:
    v1.objref<i64> = obj.alloc i64;
    v2.@pair = insert_value undef.@pair 1.i64 v1;
    obj.store v0 v2;
    return;
}"#,
            // A reference loaded from memory has unknown provenance.
            r#"func private %f(v0.objref<objref<i64>>) -> objref<i64> {
block0:
    v1.objref<i64> = obj.load v0;
    return v1;
}"#,
            // An outer holder keeps the last iteration's allocation, which
            // lives until the function returns.
            r#"type @holder = { objref<i64> };
func private %f(v0.i64) -> i64 {
block0:
    v1.objref<@holder> = obj.alloc @holder;
    v2.objref<objref<i64>> = obj.proj v1 0.i64;
    jump block1;
block1:
    v3.i64 = phi (0.i64 block0) (v5 block1);
    v4.objref<i64> = obj.alloc i64;
    obj.store v4 v3;
    obj.store v2 v4;
    v5.i64 = add v3 1.i64;
    v6.i1 = lt v5 v0;
    br v6 block1 block2;
block2:
    v7.objref<i64> = obj.load v2;
    v8.i64 = obj.load v7;
    return v8;
}"#,
        ] {
            check_frame_lifetimes(&verified_module(source)).unwrap();
        }
    }

    #[test]
    fn rejects_returned_references_to_local_objects() {
        for source in [
            r#"func private %f() -> objref<i64> {
block0:
    v0.objref<i64> = obj.alloc i64;
    return v0;
}"#,
            r#"func private %f() -> objref<i64> {
block0:
    v0.objref<[i64; 2]> = obj.alloc [i64; 2];
    v1.objref<i64> = obj.index v0 1.i64;
    return v1;
}"#,
            r#"func private %f() -> *i64 {
block0:
    v0.objref<i64> = obj.alloc i64;
    v1.*i64 = obj.materialize.stack v0;
    return v1;
}"#,
            r#"func private %f(v0.i1, v1.objref<i64>) -> objref<i64> {
block0:
    br v0 block1 block2;
block1:
    v2.objref<i64> = obj.alloc i64;
    jump block2;
block2:
    v3.objref<i64> = phi (v1 block0) (v2 block1);
    return v3;
}"#,
            r#"func private %f() -> (objref<i64>, objref<i64>) {
block0:
    v0.objref<i64> = obj.alloc i64;
    return (v0, v0);
}"#,
            r#"func private %f(v0.i1) -> objref<i64> {
block0:
    jump block1;
block1:
    v1.objref<i64> = obj.alloc i64;
    br v0 block1 block2;
block2:
    return v1;
}"#,
        ] {
            let error = check_frame_lifetimes(&verified_module(source)).unwrap_err();
            assert!(
                error.starts_with("frame object lifetime in f: ")
                    && error.contains("returns a reference to local object"),
                "{source}: {error}"
            );
        }
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
            let result = check_frame_lifetimes(&verified_module(&source));
            if reads_before_allocation {
                result.unwrap();
            } else {
                assert_earlier_instance_error(result, &source);
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
                let result = check_frame_lifetimes(&verified_module(&source));
                if reads_before_allocation {
                    result.unwrap();
                } else {
                    assert_earlier_instance_error(result, &source);
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
            let result = check_frame_lifetimes(&verified_module(&source));
            if reads_before_allocation {
                result.unwrap();
            } else {
                assert_earlier_instance_error(result, &source);
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
            assert_earlier_instance_error(
                check_frame_lifetimes(&verified_module(&source)),
                &source,
            );
        }
    }
}
