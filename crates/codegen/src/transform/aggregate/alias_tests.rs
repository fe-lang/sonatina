//! Module-aware regression oracles for the shared object-memory contract.

use sonatina_ir::{
    Module,
    inst::{control_flow, data, downcast},
    ir_writer::FuncWriter,
    module::FuncRef,
};
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

use super::{
    ObjectMemoryAnalysis, ObjectReturnEffect, collect_local_object_arg_info_with_effects,
    combine::AggregateCombine, compute_object_effect_summaries,
    object_effects::NonArgObjectEffects, object_tracking::AggregateFacts,
    provenance::ProvenanceSnapshot, shape::AggregateLayoutCache,
};
use crate::optim::{Pass, Step, pipeline::Pipeline};

fn verified_module(source: &str) -> Module {
    let module = parse_module(source).expect("regression must parse").module;
    assert_verified(&module);
    module
}

fn assert_verified(module: &Module) {
    let report = verify_module(module, &VerifierConfig::for_level(VerificationLevel::Full));
    assert!(
        report.is_ok(),
        "regression must satisfy the IR contract: {report}"
    );
}

fn lookup(module: &Module, name: &str) -> FuncRef {
    module
        .funcs()
        .into_iter()
        .find(|&f| module.ctx.func_sig(f, |sig| sig.name() == name))
        .unwrap()
}

#[test]
fn unsupported_pointer_alternatives_survive_provenance_joins() {
    for producer in [
        "v4.*i256 = mload v2 *i256;",
        "v4.*i256 = bitcast 0.i256 *i256;",
    ] {
        let module = verified_module(&format!(
            r#"
target = "evm-ethereum-osaka"
func private %f(v0.i1, v1.objref<i256>, v2.**i256) -> *i256 {{
block0:
    v3.*i256 = obj.materialize.stack v1;
    {producer}
    br v0 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v5.*i256 = phi (v3 block1) (v4 block2);
    return v5;
}}
"#,
        ));
        module.func_store.view(lookup(&module, "f"), |func| {
            let mut snapshot = ProvenanceSnapshot::new(func, None);
            let facts = AggregateFacts::for_all_objref_args(
                func,
                &mut AggregateLayoutCache::default(),
                &mut snapshot,
            );
            let joined = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .unwrap();
            let roots = facts.may().may_roots(joined);
            assert!(
                roots.has_unknown(),
                "missing alternative from {producer}: {roots:?}"
            );
            assert!(
                roots
                    .observed()
                    .iter()
                    .any(|root| root.value() == func.arg_values[1])
            );
            assert!(facts.complete().complete_roots(joined).is_none());
        });
    }
}

#[test]
fn omitted_input_root_is_unknown_in_a_provenance_join() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
func private %f(v0.i1, v1.objref<i256>, v2.objref<i256>) -> objref<i256> {
block0:
    br v0 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v3.objref<i256> = phi (v1 block1) (v2 block2);
    return v3;
}

"#,
    );
    module.func_store.view(lookup(&module, "f"), |func| {
        let mut snapshot = ProvenanceSnapshot::new(func, None);
        let mut cache = AggregateLayoutCache::default();
        let all = AggregateFacts::for_all_objref_args(func, &mut cache, &mut snapshot);
        let mut roots = all.root_slices().clone();
        roots.remove(&func.arg_values[2]);
        let selected =
            AggregateFacts::from_root_slices(func, func.ctx(), roots, &mut cache, &mut snapshot);
        let joined = func
            .layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .find_map(|inst| {
                downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst))
                    .and_then(|_| func.dfg.inst_result(inst))
            })
            .unwrap();
        assert!(selected.may().may_roots(joined).has_unknown());
        assert!(selected.complete().complete_roots(joined).is_none());
    });
}

#[test]
fn ambient_writes_cannot_certify_stale_captured_return_origins() {
    for (effect, expected) in [
        ("call %opaque;", ObjectReturnEffect::Unknown),
        ("mstore v2 0.i256 i256;", ObjectReturnEffect::Unknown),
        (
            "v4.*i256 = alloca i256;\n    mstore v4 0.i256 i256;",
            ObjectReturnEffect::DerivedFromArg { index: 1 },
        ),
    ] {
        let module = verified_module(&format!(
            r#"
target = "evm-ethereum-osaka"
declare external %opaque();
func private %f(v0.objref<objref<i256>>, v1.objref<i256>, v2.*i256) -> objref<i256> {{
block0:
    obj.store v0 v1;
    {effect}
    v3.objref<i256> = obj.load v0;
    return v3;
}}
"#,
        ));
        let summaries = compute_object_effect_summaries(&module);
        assert_eq!(
            summaries[&lookup(&module, "f")].ret_effect,
            expected,
            "ambient replacement must respect the raw allocation boundary: {effect}"
        );
    }
}

#[test]
fn ambient_writes_preserve_unpublished_private_capture_origins() {
    for effect in [
        "call %opaque;",
        "mstore v1 0.i256 i256;",
        "call %write_tag v2;",
    ] {
        let module = verified_module(&format!(
            r#"
target = "evm-ethereum-osaka"
type @Holder = {{ i256, objref<i256> }};
declare external %opaque();
func private %write_tag(v0.objref<@Holder>) {{
block0:
    v1.objref<i256> = obj.proj v0 0.i8;
    obj.store v1 7.i256;
    return;
}}
func private %f(v0.objref<i256>, v1.*i256) -> objref<i256> {{
block0:
    v2.objref<@Holder> = obj.alloc @Holder;
    v3.objref<objref<i256>> = obj.proj v2 1.i8;
    obj.store v3 v0;
    {effect}
    v4.objref<i256> = obj.load v3;
    return v4;
}}
"#,
        ));
        let summaries = compute_object_effect_summaries(&module);
        assert_eq!(
            summaries[&lookup(&module, "f")].ret_effect,
            ObjectReturnEffect::DerivedFromArg { index: 0 },
            "{effect}"
        );
    }
}

#[test]
fn published_private_holder_loses_complete_capture_origin_after_opaque_write() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
type @Holder = { objref<i256> };
declare external %opaque();
func private %f(v0.objref<i256>, v1.objref<objref<@Holder>>) -> objref<i256> {
block0:
    v2.objref<@Holder> = obj.alloc @Holder;
    v3.objref<objref<i256>> = obj.proj v2 0.i8;
    obj.store v3 v0;
    obj.store v1 v2;
    call %opaque;
    v4.objref<i256> = obj.load v3;
    return v4;
}
"#,
    );
    let summaries = compute_object_effect_summaries(&module);
    assert_eq!(
        summaries[&lookup(&module, "f")].ret_effect,
        ObjectReturnEffect::Unknown
    );
}

#[test]
fn aliased_scalar_and_constant_writes_invalidate_captured_reference_origins() {
    for write in [
        "obj.store v1 0.i256;",
        "v4.constref<i256> = const.ref $zero;\n    obj.init.const v1 v4;",
    ] {
        let module = verified_module(&format!(
            r#"
target = "evm-ethereum-osaka"
global private const i256 $zero = 0;
func private %f(v0.objref<objref<i256>>, v1.objref<i256>, v2.objref<i256>) -> objref<i256> {{
block0:
    obj.store v0 v2;
    {write}
    v3.objref<i256> = obj.load v0;
    return v3;
}}
"#
        ));
        let summaries = compute_object_effect_summaries(&module);
        assert_eq!(
            summaries[&lookup(&module, "f")].ret_effect,
            ObjectReturnEffect::Unknown,
            "different incoming pointee types do not prove separation: {write}"
        );
    }
}

#[test]
fn aliased_reference_aggregate_store_retains_unknown_contained_sources() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
type @Holder = { objref<i256> };
func private %f(v0.objref<@Holder>, v1.objref<@Holder>, v2.objref<i256>, v3.@Holder) -> objref<i256> {
block0:
    v4.objref<objref<i256>> = obj.proj v0 0.i8;
    obj.store v4 v2;
    obj.store v1 v3;
    v5.objref<i256> = obj.load v4;
    return v5;
}
"#,
    );
    let summaries = compute_object_effect_summaries(&module);
    assert_eq!(
        summaries[&lookup(&module, "f")].ret_effect,
        ObjectReturnEffect::Unknown
    );
}

#[test]
fn aliased_enum_aggregate_field_write_retains_unknown_contained_sources() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
type @Holder = { objref<i256> };
type @Choice = enum { #None, #Some(@Holder), };
func private %f(v0.objref<@Choice>, v1.objref<@Choice>, v2.objref<i256>, v3.@Holder) -> objref<i256> {
block0:
    v4.objref<@Choice> = enum.assert_variant_ref v0 #Some;
    v5.objref<@Holder> = enum.proj v4 #Some 0.i8;
    v6.objref<objref<i256>> = obj.proj v5 0.i8;
    obj.store v6 v2;
    enum.write_variant v1 #Some (v3);
    v7.objref<@Choice> = enum.assert_variant_ref v0 #Some;
    v8.objref<@Holder> = enum.proj v7 #Some 0.i8;
    v9.objref<objref<i256>> = obj.proj v8 0.i8;
    v10.objref<i256> = obj.load v9;
    return v10;
}
"#,
    );
    let summaries = compute_object_effect_summaries(&module);
    assert_eq!(
        summaries[&lookup(&module, "f")].ret_effect,
        ObjectReturnEffect::Unknown
    );
}

#[test]
fn exact_reference_store_recovers_origin_after_an_aliased_scalar_clobber() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<objref<i256>>, v1.objref<i256>, v2.objref<i256>) -> objref<i256> {
block0:
    obj.store v0 v2;
    obj.store v1 0.i256;
    obj.store v0 v2;
    v3.objref<i256> = obj.load v0;
    return v3;
}
"#,
    );
    let summaries = compute_object_effect_summaries(&module);
    assert_eq!(
        summaries[&lookup(&module, "f")].ret_effect,
        ObjectReturnEffect::DerivedFromArg { index: 2 }
    );
}

#[test]
fn scalar_and_constant_sibling_writes_preserve_captured_origins() {
    for write in [
        "obj.store v2 0.i256;",
        "v4.constref<i256> = const.ref $zero;\n    obj.init.const v2 v4;",
    ] {
        let module = verified_module(&format!(
            r#"
target = "evm-ethereum-osaka"
type @Pair = {{ i256, objref<i256> }};
global private const i256 $zero = 0;
func private %f(v0.objref<@Pair>, v1.objref<i256>) -> objref<i256> {{
block0:
    v2.objref<i256> = obj.proj v0 0.i8;
    v3.objref<objref<i256>> = obj.proj v0 1.i8;
    obj.store v3 v1;
    {write}
    v5.objref<i256> = obj.load v3;
    return v5;
}}
"#
        ));
        let summaries = compute_object_effect_summaries(&module);
        assert_eq!(
            summaries[&lookup(&module, "f")].ret_effect,
            ObjectReturnEffect::DerivedFromArg { index: 1 },
            "{write}"
        );
    }
}

fn run_pass(source: &str, pass: Pass) -> String {
    let mut module = verified_module(source);
    // Pipeline computes module effects/locality outside function mutation locks.
    let mut pipeline = Pipeline::new();
    pipeline.add_step(Step::FuncPasses(vec![pass]));
    pipeline.run(&mut module);
    assert_verified(&module);
    let f = lookup(&module, "f");
    module
        .func_store
        .view(f, |func| FuncWriter::new(f, func).dump_string())
}

#[test]
fn t17_t18_zero_argument_external_effects_propagate_through_wrappers_and_recursion() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
declare external %opaque();
func private %wrapper() {
block0:
    call %opaque;
    return;
}
func private %forward() {
block0:
    call %wrapper;
    return;
}
func private %recursive(v0.i1) {
block0:
    br v0 block1 block2;
block1:
    call %recursive 0.i1;
    return;
block2:
    call %forward;
    return;
}
"#,
    );
    let summaries = compute_object_effect_summaries(&module);
    for name in ["wrapper", "forward", "recursive"] {
        let summary = &summaries[&lookup(&module, name)];
        assert!(summary.non_arg.external.reads, "{name}");
        assert!(summary.non_arg.external.writes, "{name}");
        assert!(summary.non_arg.external.publishes, "{name}");
        assert!(!summary.non_arg.unknown.writes, "{name}");
    }
}

#[test]
fn t24_loaded_referent_effects_survive_summary_composition() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
func private %read_write(v0.objref<i256>) -> i256 {
block0:
    v1.i256 = obj.load v0;
    obj.store v0 42.i256;
    return v1;
}
func private %nested(v0.objref<objref<i256>>) -> i256 {
block0:
    v1.objref<i256> = obj.load v0;
    v2.i256 = call %read_write v1;
    return v2;
}
func private %direct(v0.objref<objref<i256>>) -> i256 {
block0:
    v1.objref<i256> = obj.load v0;
    v2.i256 = obj.load v1;
    obj.store v1 42.i256;
    return v2;
}
func private %private_only() -> i256 {
block0:
    v0.objref<i256> = obj.alloc i256;
    obj.store v0 11.i256;
    v1.i256 = call %read_write v0;
    return v1;
}
"#,
    );
    let summaries = compute_object_effect_summaries(&module);
    for name in ["nested", "direct"] {
        let summary = &summaries[&lookup(&module, name)];
        assert!(summary.non_arg.unknown.reads, "{name}");
        assert!(summary.non_arg.unknown.writes, "{name}");
        assert!(summary.arg_effects[0].writes.is_empty(), "{name}");
    }
    for name in ["read_write", "private_only"] {
        assert_eq!(
            summaries[&lookup(&module, name)].non_arg,
            NonArgObjectEffects::default(),
            "{name}"
        );
    }
}

#[test]
fn raw_effects_respect_target_address_spaces() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
func private %memory(v0.i256) -> i256 {
block0:
    v1.i256 = evm_mload v0;
    evm_mstore v0 42.i256;
    return v1;
}
func private %storage(v0.i256) -> i256 {
block0:
    v1.i256 = evm_sload v0;
    evm_sstore v0 42.i256;
    return v1;
}
"#,
    );
    let summaries = compute_object_effect_summaries(&module);
    let memory = &summaries[&lookup(&module, "memory")].non_arg;
    assert!(memory.external.reads && memory.external.writes);
    assert!(!memory.unknown.reads && !memory.unknown.writes);
    assert_eq!(
        summaries[&lookup(&module, "storage")].non_arg,
        NonArgObjectEffects::default()
    );
}

#[test]
fn reference_publication_through_unmapped_holder_is_not_dropped() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
func private %store(v0.objref<objref<i256>>, v1.objref<i256>) {
block0:
    obj.store v0 v1;
    return;
}
func private %direct(v0.objref<objref<objref<i256>>>, v1.objref<i256>) {
block0:
    v2.objref<objref<i256>> = obj.load v0;
    obj.store v2 v1;
    return;
}
func private %indirect(v0.objref<objref<objref<i256>>>, v1.objref<i256>) {
block0:
    v2.objref<objref<i256>> = obj.load v0;
    call %store v2 v1;
    return;
}
"#,
    );
    let summaries = compute_object_effect_summaries(&module);
    for name in ["direct", "indirect"] {
        let summary = &summaries[&lookup(&module, name)];
        assert!(summary.non_arg.unknown.publishes, "{name}");
        assert!(summary.arg_effects[1].escapes, "{name}");
        assert!(!summary.arg_effects[1].local_only, "{name}");
    }
}

#[test]
fn constant_initialization_summary_writes_only_its_projected_subtree() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
type @Pair = { i256, i256 };
global private const i256 $answer = 42;
func private %initialize(v0.objref<@Pair>) {
block0:
    v1.objref<i256> = obj.proj v0 1.i8;
    v2.constref<i256> = const.ref $answer;
    obj.init.const v1 v2;
    return;
}
"#,
    );
    let summaries = compute_object_effect_summaries(&module);
    let summary = &summaries[&lookup(&module, "initialize")];
    assert_eq!(summary.non_arg, NonArgObjectEffects::default());
    let writes = summary.arg_effects[0].writes.exact_leaves().unwrap();
    assert_eq!(writes.len(), 1);
    assert!(writes.contains(&1));
    assert!(summary.arg_effects[0].reads.is_empty());
}

#[test]
fn untracked_phi_alternative_preserves_its_observable_store() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<i256>, v1.objref<i256>, v2.i1) {
block0:
    v3.*i256 = obj.materialize.heap v1;
    br v2 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v4.objref<i256> = phi (v0 block1) (v1 block2);
    obj.store v4 22.i256;
    obj.store v0 33.i256;
    return;
}
"#,
        Pass::ObjectLoadStore,
    );
    assert!(
        text.contains("22.i256"),
        "untracked destination is observable: {text}"
    );
}

#[test]
fn published_private_object_preserves_writes_after_publication() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<objref<i256>>) {
block0:
    v1.objref<i256> = obj.alloc i256;
    obj.store v1 11.i256;
    obj.store v0 v1;
    obj.store v1 22.i256;
    return;
}
"#,
        Pass::ObjectLoadStore,
    );
    assert!(
        text.contains("22.i256"),
        "published storage remains observable: {text}"
    );
}

#[test]
fn t01_scalar_promotion_keeps_read_after_alias_write() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    obj.store v1 22.i256;
    v2.i256 = obj.load v0;
    return v2;
}
"#,
        Pass::AggregateScalarize,
    );
    let write = text
        .find("obj.store")
        .expect("caller-visible write remains");
    let read = text.find("obj.load").expect("incoming read remains");
    assert!(
        write < read,
        "I9: alias write must precede the read: {text}"
    );
}

#[test]
fn t03_forwarding_invalidates_other_incoming_root() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    obj.store v0 11.i256;
    obj.store v1 22.i256;
    v2.i256 = obj.load v0;
    return v2;
}

"#,
        Pass::ObjectLoadStore,
    );
    assert!(
        text.contains("obj.load"),
        "I4: two formal IDs are not a separation proof: {text}"
    );
}

#[test]
fn t04_alias_read_preserves_observed_store() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    obj.store v0 11.i256;
    v2.i256 = obj.load v1;
    obj.store v0 33.i256;
    return v2;
}
"#,
        Pass::ObjectLoadStore,
    );
    assert!(
        text.contains("11.i256"),
        "I5: the alias read can observe the first store: {text}"
    );
    assert!(
        text.contains("33.i256"),
        "final incoming memory remains caller-visible: {text}"
    );
}

#[test]
fn t05_alias_write_changes_object_memory_read_key() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
func inline(never) private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    v2.i256 = obj.load v0;
    obj.store v1 22.i256;
    v3.i256 = obj.load v0;
    v4.i256 = add v2 v3;
    return v4;
}
"#,
    );
    let effects = compute_object_effect_summaries(&module);
    let local = collect_local_object_arg_info_with_effects(&module, &effects);
    let f = lookup(&module, "f");
    module.func_store.view(f, |func| {
        let mut memory = ObjectMemoryAnalysis::default();
        memory.compute(func, local.get(&f), Some(&effects));
        let keys: Vec<_> = func
            .layout
            .iter_block()
            .flat_map(|b| func.layout.iter_inst(b))
            .filter(|&inst| {
                downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)).is_some()
            })
            .map(|inst| memory.read_state(inst).map(|state| state.key()))
            .collect();
        assert_eq!(keys.len(), 2);
        assert!(
            keys[0].is_none() || keys[1].is_none() || keys[0] != keys[1],
            "I4: clobbered reads must not have the same available key: {keys:?}"
        );
    });
}

#[test]
fn t14_conditional_call_write_does_not_kill_prior_store() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
func inline(never) private %maybe_write(v0.objref<i256>, v1.i1) {
block0:
    br v1 block1 block2;
block1:
    obj.store v0 22.i256;
    jump block2;
block2:
    return;
}
func inline(never) private %f(v0.objref<i256>, v1.i1) -> i256 {
block0:
    obj.store v0 11.i256;
    call %maybe_write v0 v1;
    v2.i256 = obj.load v0;
    return v2;
}
"#,
        Pass::ObjectLoadStore,
    );
    assert!(
        text.contains("11.i256"),
        "I6: a may-write cannot kill a store observed on the false path: {text}"
    );
}

#[test]
fn t25_combine_invalidates_aliased_enum_tag() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
type @Flag = enum { #A, #B, };
func inline(never) private %f(v0.objref<@Flag>, v1.objref<@Flag>) -> enumtag(@Flag) {
block0:
    enum.set_tag v0 #A;
    enum.set_tag v1 #B;
    v2.enumtag(@Flag) = enum.get_tag v0;
    return v2;
}

"#,
        Pass::AggregateCombine,
    );
    assert!(
        text.contains("enum.get_tag"),
        "I4: last actual tag wins when formal arguments alias: {text}"
    );
}

#[test]
fn p03_distinct_fresh_roots_keep_forwarding() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
func private %f() -> i256 {
block0:
    v0.objref<i256> = obj.alloc i256;
    v1.objref<i256> = obj.alloc i256;
    obj.store v0 11.i256;
    obj.store v1 22.i256;
    v2.i256 = obj.load v0;
    return v2;
}
"#,
        Pass::ObjectLoadStore,
    );
    assert!(
        text.contains("return 11.i256"),
        "I12: fresh allocation separation should retain forwarding: {text}"
    );
    assert!(!text.contains("obj.load"), "{text}");
}

#[test]
fn p05_read_only_incoming_scalar_still_promotes() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<i256>) -> i256 {
block0:
    v1.i256 = obj.load v0;
    v2.i256 = obj.load v0;
    v3.i256 = add v1 v2;
    return v3;
}
"#,
        Pass::AggregateScalarize,
    );
    assert_eq!(
        text.matches("obj.load").count(),
        1,
        "I12: one legal entry load should seed both reads: {text}"
    );
}

#[test]
fn t21_conditional_call_retains_old_capture_alternative() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
func inline(never) private %replace(v0.objref<objref<i256>>, v1.i1, v2.objref<i256>) {
block0:
    br v1 block1 block2;
block1:
    obj.store v0 v2;
    jump block2;
block2:
    return;
}
func inline(never) private %f(v0.objref<objref<i256>>, v1.objref<i256>, v2.objref<i256>, v3.i1) {
block0:
    obj.store v0 v1;
    call %replace v0 v3 v2;
    return;
}
"#,
    );
    let effects = compute_object_effect_summaries(&module);
    let summary = &effects[&lookup(&module, "f")];
    for source in [1, 2] {
        assert!(
            summary
                .captures
                .iter()
                .any(|capture| capture.src_arg == source),
            "I7: both old and replacement references can remain captured: {summary:?}"
        );
    }
}

#[test]
fn t22_aliased_holder_stores_preserve_both_reference_candidates() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<objref<i256>>, v1.objref<objref<i256>>, v2.objref<i256>, v3.objref<i256>) -> objref<i256> {
block0:
    obj.store v0 v2;
    obj.store v1 v3;
    v4.objref<i256> = obj.load v0;
    return v4;
}
"#,
    );
    let f = lookup(&module, "f");
    module.func_store.view(f, |func| {
        let mut snapshot = ProvenanceSnapshot::new(func, None);
        let facts = AggregateFacts::for_all_objref_args(
            func,
            &mut AggregateLayoutCache::default(),
            &mut snapshot,
        );
        let loaded = func
            .layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .find_map(|inst| {
                downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                    .and_then(|_| func.dfg.inst_result(inst))
            })
            .unwrap();
        let roots = facts.may().may_roots(loaded);
        for &source in &func.arg_values[2..] {
            assert!(
                roots.observed().iter().any(|root| root.value() == source),
                "I7: direct stores through aliased holders must retain both candidates: {roots:?}"
            );
        }
    });
}

#[test]
fn t23_inactive_enum_slots_retain_reference_containment() {
    for overwrite in ["enum.set_tag v0 #None;", "enum.write_variant v0 #None (); "] {
        let module = verified_module(&format!(
            r#"
target = "evm-ethereum-osaka"
type @Holder = enum {{ #None, #Some(objref<i256>), }};
func private %f(v0.objref<@Holder>, v1.objref<i256>) {{
block0:
    enum.write_variant v0 #Some (v1);
    {overwrite}
    return;
}}
"#
        ));
        let effects = compute_object_effect_summaries(&module);
        let summary = &effects[&lookup(&module, "f")];
        assert!(
            summary.captures.iter().any(|capture| capture.src_arg == 1),
            "I11: selecting None does not overwrite the inactive reference slot: {summary:?}"
        );
    }
}

#[test]
fn t20_holder_without_a_store_on_every_path_keeps_unknown_alternative() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<objref<i256>>, v1.objref<i256>, v2.i1) -> objref<i256> {
block0:
    br v2 block1 block2;
block1:
    obj.store v0 v1;
    jump block2;
block2:
    v3.objref<i256> = obj.load v0;
    return v3;
}
"#,
    );
    let f = lookup(&module, "f");
    module.func_store.view(f, |func| {
        let mut snapshot = ProvenanceSnapshot::new(func, None);
        let facts = AggregateFacts::for_all_objref_args(
            func,
            &mut AggregateLayoutCache::default(),
            &mut snapshot,
        );
        let loaded = func
            .layout
            .iter_block()
            .flat_map(|block| func.layout.iter_inst(block))
            .find_map(|inst| {
                downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
                    .and_then(|_| func.dfg.inst_result(inst))
            })
            .unwrap();
        let roots = facts.may().may_roots(loaded);
        assert!(
            roots.has_unknown(),
            "I7: false path retains unknown incoming contents: {roots:?}"
        );
        assert!(
            roots
                .observed()
                .iter()
                .any(|root| root.value() == func.arg_values[1])
        );
        assert!(facts.complete().complete_roots(loaded).is_none());
    });
}

#[test]
fn t11_untracked_materialized_writer_invalidates_tracked_reader() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
func private %f(v0.objref<i256>, v1.objref<i256>) -> i256 {
block0:
    v2.*i256 = obj.materialize.heap v1;
    obj.store v0 11.i256;
    obj.store v1 22.i256;
    v3.i256 = obj.load v0;
    return v3;
}
"#,
        Pass::ObjectLoadStore,
    );
    assert!(text.contains("obj.load"), "{text}");
    assert!(!text.contains("return 11.i256"), "{text}");
}

#[test]
fn t17_opaque_call_observes_and_invalidates_incoming_contents() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
declare external %opaque();
func private %f(v0.objref<i256>) -> i256 {
block0:
    obj.store v0 11.i256;
    call %opaque;
    v1.i256 = obj.load v0;
    return v1;
}
"#,
        Pass::ObjectLoadStore,
    );
    assert!(text.contains("obj.store v0 11.i256"), "{text}");
    assert!(text.contains("obj.load v0"), "{text}");
}

#[test]
fn p10_opaque_call_does_not_destroy_unpublished_private_contents() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
declare external %opaque();
func private %f() -> i256 {
block0:
    v0.objref<i256> = obj.alloc i256;
    obj.store v0 11.i256;
    call %opaque;
    v1.i256 = obj.load v0;
    return v1;
}
"#,
        Pass::ObjectLoadStore,
    );
    assert!(text.contains("return 11.i256"), "{text}");
    assert!(!text.contains("obj.load"), "{text}");
}

#[test]
fn gvn_uses_shape_definedness_for_reconstructed_aggregate_carriers() {
    for (second, keeps_load) in [("v1", false), ("undef.i256", true)] {
        let text = run_pass(
            &format!(
                r#"
target = "evm-ethereum-osaka"
type @Pair = {{ i256, i256 }};
func private %f(v0.i256, v1.i256) -> @Pair {{
block0:
    v2.objref<@Pair> = obj.alloc @Pair;
    v3.@Pair = insert_value undef.@Pair 0.i8 v0;
    v4.@Pair = insert_value v3 1.i8 {second};
    obj.store v2 v4;
    v5.@Pair = obj.load v2;
    return v5;
}}
"#
            ),
            Pass::Gvn,
        );
        assert_eq!(text.contains("obj.load"), keeps_load, "{text}");
    }
}

#[test]
fn licm_keeps_payload_read_below_the_assumption_establishing_its_guard() {
    for outside_loop in [false, true] {
        let assumption = "v3.objref<@Choice> = enum.assert_variant_ref v0 #Some;";
        let (entry, body) = if outside_loop {
            (assumption, "")
        } else {
            ("", assumption)
        };
        let text = run_pass(
            &format!(
                r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256) }};
func private %f(v0.objref<@Choice>, v1.i1) -> i256 {{
block0:
    v2.objref<i256> = enum.proj v0 #Some 0.i8;
    {entry}
    jump block1;
block1:
    {body}
    v4.i256 = obj.load v2;
    br v1 block1 block2;
block2:
    return v4;
}}
"#
            ),
            Pass::Licm,
        );
        let load = text.find("obj.load").expect("load must remain");
        let header = text.find("block1:").unwrap();
        assert_eq!(load < header, outside_loop, "{text}");
    }
}

#[test]
fn t26_combine_preserves_tag_write_observed_through_an_alias() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
type @Flag = enum { #A, #B };
func private %f(v0.objref<@Flag>, v1.objref<@Flag>) -> enumtag(@Flag) {
block0:
    enum.set_tag v0 #A;
    v2.enumtag(@Flag) = enum.get_tag v1;
    enum.set_tag v0 #B;
    return v2;
}
"#,
        Pass::AggregateCombine,
    );
    assert!(text.contains("enum.set_tag v0 #A"), "{text}");
    assert!(text.contains("enum.set_tag v0 #B"), "{text}");
}

#[test]
fn t27_combine_does_not_apply_saved_tag_to_mutated_memory() {
    for write in ["enum.set_tag v1 #B;", "call %opaque;"] {
        let text = run_pass(
            &format!(
                r#"
target = "evm-ethereum-osaka"
type @Flag = enum {{ #A, #B }};
declare external %opaque();
func private %f(v0.objref<@Flag>, v1.objref<@Flag>) -> enumtag(@Flag) {{
block0:
    v2.enumtag(@Flag) = enum.get_tag v0;
    {write}
    br_table v2 block2 (0.enumtag(@Flag) block1);
block1:
    v3.enumtag(@Flag) = enum.get_tag v0;
    return v3;
block2:
    v4.enumtag(@Flag) = enum.get_tag v0;
    return v4;
}}
"#
            ),
            Pass::AggregateCombine,
        );
        assert_eq!(text.matches("enum.get_tag").count(), 3, "{text}");
    }
}

#[test]
fn combine_default_edge_accounts_for_implicit_and_explicit_variants() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
type @Flag = enum { #A, #B, #C };
func private %f(v0.objref<@Flag>) -> enumtag(@Flag) {
block0:
    v1.enumtag(@Flag) = enum.get_tag v0;
    br_table v1 block1 (0.enumtag(@Flag) block1) (1.enumtag(@Flag) block2);
block1:
    v2.enumtag(@Flag) = enum.get_tag v0;
    return v2;
block2:
    v3.enumtag(@Flag) = enum.get_tag v0;
    return v3;
}
"#,
        Pass::AggregateCombine,
    );
    assert_eq!(
        text.matches("enum.get_tag").count(),
        2,
        "default also admits C: {text}"
    );
    assert!(
        text.contains("return 1.enumtag(@Flag)"),
        "the unique B edge still refines: {text}"
    );
}

#[test]
fn guarded_payload_reads_preserve_their_ancestor_tag_writes() {
    for pass in [Pass::ObjectLoadStore, Pass::AggregateCombine] {
        let text = run_pass(
            r#"
target = "evm-ethereum-osaka"
type @Choice = enum { #None, #Some(i256) };
func private %f(v0.i1, v1.i256, v2.i256) -> i256 {
block0:
    v3.objref<@Choice> = obj.alloc @Choice;
    enum.set_tag v3 #Some;
    v4.objref<i256> = enum.proj v3 #Some 0.i8;
    br v0 block1 block2;
block1:
    obj.store v4 v1;
    jump block3;
block2:
    obj.store v4 v2;
    jump block3;
block3:
    v5.i256 = obj.load v4;
    enum.set_tag v3 #None;
    return v5;
}
"#,
            pass,
        );
        assert!(text.contains("enum.set_tag v3 #Some"), "{text}");
    }
}

#[test]
fn combine_keeps_readability_assumption_for_uninitialized_snapshot() {
    for (source, keeps_assertion) in [
        ("v2.@Inner = obj.load v1;", true),
        ("v2.@Inner = enum.make @Inner #Empty ();", false),
    ] {
        let text = run_pass(
            &format!(
                r#"
target = "evm-ethereum-osaka"
type @Inner = enum {{ #Empty, #Value(i256) }};
type @Outer = enum {{ #None, #Some(@Inner) }};
func private %f() -> @Inner {{
block0:
    v0.objref<@Outer> = obj.alloc @Outer;
    v1.objref<@Inner> = obj.alloc @Inner;
    {source}
    enum.write_variant v0 #Some (v2);
    v3.objref<@Outer> = enum.assert_variant_ref v0 #Some;
    v4.@Outer = obj.load v3;
    v5.@Inner = enum.extract v4 #Some 0.i8;
    return v5;
}}
"#
            ),
            Pass::AggregateCombine,
        );
        assert_eq!(
            text.contains("enum.assert_variant_ref"),
            keeps_assertion,
            "{text}"
        );
    }
}

#[test]
fn combine_keeps_snapshot_read_after_readability_assumption() {
    for (source, loads) in [
        ("v2.@Inner = obj.load v1;", 2),
        ("v2.@Inner = enum.make @Inner #Value (7.i256);", 0),
    ] {
        let source_ir = r#"
target = "evm-ethereum-osaka"
type @Inner = enum { #Empty, #Value(i256) };
type @Outer = enum { #None, #Some(@Inner) };
func private %f() -> i256 {
block0:
    v0.objref<@Outer> = obj.alloc @Outer;
    v1.objref<@Inner> = obj.alloc @Inner;
    SOURCE
    enum.write_variant v0 #Some (v2);
    v3.objref<@Outer> = enum.assert_variant_ref v0 #Some;
    v4.objref<@Inner> = enum.proj v3 #Some 0.i8;
    v5.@Inner = obj.load v4;
    v6.enumtag(@Inner) = enum.tag v5;
    br_table v6 block2 (1.enumtag(@Inner) block1);
block1:
    v7.i256 = enum.extract v5 #Value 0.i8;
    return v7;
block2:
    return 0.i256;
}
"#
        .replace("SOURCE", source);
        let text = run_pass(&source_ir, Pass::AggregateCombine);
        assert_eq!(text.matches("obj.load").count(), loads, "{text}");
    }
}

#[test]
fn combine_uses_read_only_call_effects_and_preserves_private_roots() {
    for (allocation, signature, call) in [
        ("", "v0.objref<@Flag>", "v2.enumtag(@Flag) = call %peek v0;"),
        ("v0.objref<@Flag> = obj.alloc @Flag;", "", "call %opaque;"),
    ] {
        let text = run_pass(
            &format!(
                r#"
target = "evm-ethereum-osaka"
type @Flag = enum {{ #A, #B }};
declare external %opaque();
func private %peek(v0.objref<@Flag>) -> enumtag(@Flag) {{
block0:
    v1.enumtag(@Flag) = enum.get_tag v0;
    return v1;
}}
func private %f({signature}) -> enumtag(@Flag) {{
block0:
    {allocation}
    enum.set_tag v0 #A;
    {call}
    v1.enumtag(@Flag) = enum.get_tag v0;
    return v1;
}}
"#
            ),
            Pass::AggregateCombine,
        );
        assert!(text.contains("return 0.enumtag(@Flag)"), "{text}");
    }
}

#[test]
fn combine_invalidates_helper_and_ambient_writes() {
    for call in ["call %write v1;", "call %ambient;"] {
        let text = run_pass(
            &format!(
                r#"
target = "evm-ethereum-osaka"
type @Flag = enum {{ #A, #B }};
func private %write(v0.objref<@Flag>) {{
block0:
    enum.set_tag v0 #B;
    return;
}}
func private %ambient() {{
block0:
    mstore 0.i256 1.i256 i256;
    return;
}}
func private %f(v0.objref<@Flag>, v1.objref<@Flag>) -> enumtag(@Flag) {{
block0:
    enum.set_tag v0 #A;
    {call}
    v2.enumtag(@Flag) = enum.get_tag v0;
    return v2;
}}
"#
            ),
            Pass::AggregateCombine,
        );
        assert!(text.contains("enum.get_tag"), "{text}");
    }
}

#[test]
fn combine_preserves_current_tag_observations_across_sibling_writes_and_loops() {
    let text = run_pass(
        r#"
target = "evm-ethereum-osaka"
type @Flag = enum { #A, #B };
type @Pair = { @Flag, i256 };
func private %f(v0.objref<@Pair>, v1.i1) -> enumtag(@Flag) {
block0:
    v2.objref<@Flag> = obj.proj v0 0.i8;
    v3.objref<i256> = obj.proj v0 1.i8;
    v4.enumtag(@Flag) = enum.get_tag v2;
    jump block1;
block1:
    obj.store v3 11.i256;
    br v1 block1 block2;
block2:
    br_table v4 block4 (0.enumtag(@Flag) block3);
block3:
    v5.enumtag(@Flag) = enum.get_tag v2;
    return v5;
block4:
    v6.enumtag(@Flag) = enum.get_tag v2;
    return v6;
}
"#,
        Pass::AggregateCombine,
    );
    assert_eq!(text.matches("enum.get_tag").count(), 1, "{text}");
    assert!(text.contains("return 0.enumtag(@Flag)"), "{text}");
    assert!(text.contains("return 1.enumtag(@Flag)"), "{text}");
}

#[test]
fn combine_standalone_call_context_is_conservative() {
    let module = verified_module(
        r#"
target = "evm-ethereum-osaka"
type @Flag = enum { #A, #B };
func private %write(v0.objref<@Flag>) {
block0:
    enum.set_tag v0 #B;
    return;
}
func private %f(v0.objref<@Flag>, v1.objref<@Flag>) -> enumtag(@Flag) {
block0:
    enum.set_tag v0 #A;
    call %write v1;
    v2.enumtag(@Flag) = enum.get_tag v0;
    return v2;
}
"#,
    );
    let f = lookup(&module, "f");
    module.func_store.modify(f, |func| {
        AggregateCombine::default().run(func);
    });
    assert_verified(&module);
    let text = module
        .func_store
        .view(f, |func| FuncWriter::new(f, func).dump_string());
    assert!(text.contains("enum.get_tag"), "{text}");
}
