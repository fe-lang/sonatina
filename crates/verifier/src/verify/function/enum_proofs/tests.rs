use super::{FunctionVerifier, objects::State, solve, transfer};
use crate::VerifierConfig;
use sonatina_ir::{Type, ValueId};
use sonatina_parser::parse_module;

use super::{
    value_state::ValueState,
    views::{Index, References, Root, Step},
};

#[test]
fn value_joins_obey_lattice_laws_and_tag_transfers_are_monotone() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
func private %entry(v0.@E) {
block0:
 return;
}
"#,
    )
    .unwrap();
    let ctx = &parsed.module.ctx;
    let ty = ctx.func_sig(parsed.module.funcs()[0], |sig| sig.args()[0]);
    let mut cases = vec![ValueState::new(ty, false), ValueState::new(ty, true)];
    for initialized in [false, true] {
        for tag in [0, 1] {
            let mut value = ValueState::new(ty, initialized);
            value.set_tag(ctx, tag);
            cases.push(value.clone());
            value.children.insert(
                Step::Payload(1, 0),
                ValueState::new(Type::I256, initialized),
            );
            cases.push(value);
        }
    }
    // Compare observables under possible variants, plus physical containment.
    let equivalent = |a: &ValueState, b: &ValueState| {
        assert_eq!(a.tags, b.tags);
        assert_eq!(a.tag_initialized, b.tag_initialized);
        assert_eq!(a.readable(ctx), b.readable(ctx));
        for tag in [0, 1] {
            assert_eq!(a.active(tag), b.active(tag));
            if a.possible(tag) && tag == 1 {
                assert_eq!(
                    a.child(ctx, Step::Payload(tag, 0)).readable(ctx),
                    b.child(ctx, Step::Payload(tag, 0)).readable(ctx)
                );
            }
        }
        assert_eq!(a.captured(ctx), b.captured(ctx));
    };
    for a in &cases {
        equivalent(a, &a.join(ctx, a));
        for b in &cases {
            let joined = a.join(ctx, b);
            equivalent(&joined, &b.join(ctx, a));
            for c in &cases {
                equivalent(&joined.join(ctx, c), &a.join(ctx, &b.join(ctx, c)));
            }
            for tag in [0, 1] {
                let mut after_a = a.clone();
                after_a.set_tag(ctx, tag);
                let mut after_join = joined.clone();
                after_join.set_tag(ctx, tag);
                equivalent(&after_join, &after_a.join(ctx, &after_join));
            }
        }
    }
}

#[test]
fn may_targets_do_not_establish_view_equality() {
    let a = References::root(Root::Recent(ValueId::from_u32(1)));
    let b = References::root(Root::Recent(ValueId::from_u32(2)));
    let ambiguous = a.join(&b);
    assert!(a.same_location(&a));
    assert!(!ambiguous.same_location(&ambiguous));
    let summary = References::root(Root::Summary(ValueId::from_u32(1)));
    assert!(!summary.same_location(&summary));
    let unknown = a.project(Step::Index(Index::Unknown));
    assert!(!unknown.same_location(&unknown));
}

#[test]
fn worklist_order_does_not_change_the_solution() {
    for source in [
        include_str!("../../../../tests/fixtures/enum_contract/phi-unwritten-scalar.sntn"),
        include_str!("../../../../tests/fixtures/enum_contract/private-container.sntn"),
        include_str!("../../../../tests/fixtures/enum_contract/assertion-revisit.sntn"),
        r#"
target = "evm-ethereum-osaka"
type @E = enum { #None, #Some(i256) };
func private %entry(v100.i1) -> i256 {
block0:
 br v100 block1 block2;
block1:
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 jump block3;
block2:
 v1.objref<@E> = obj.alloc @E;
 enum.write_variant v1 #Some (31.i256);
 jump block3;
block3:
 v2.objref<@E> = phi (v0 block1) (v1 block2);
 v3.objref<i256> = enum.proj v2 #Some 0.i8;
 v4.i256 = obj.load v3;
 return v4;
}
"#,
    ] {
        let parsed = parse_module(source).unwrap();
        let cfg = VerifierConfig::default();
        for func in parsed.module.funcs() {
            parsed.module.func_store.view(func, |body| {
                let mut verifier =
                    FunctionVerifier::new(&parsed.module.ctx, func, body, &cfg, None);
                verifier.run();
                let forward = solve(&verifier);
                verifier.analysis_cfg.blocks.reverse();
                for successors in verifier.analysis_cfg.succs.values_mut() {
                    successors.reverse();
                }
                assert_eq!(forward, solve(&verifier), "{source}");
            });
        }
    }
}

#[test]
fn sparse_array_joins_and_writes_are_monotone() {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"
func private %entry(v0.[i256; 3]) {
block0:
 return;
}
"#,
    )
    .unwrap();
    let ctx = &parsed.module.ctx;
    let ty = ctx.func_sig(parsed.module.funcs()[0], |sig| sig.args()[0]);
    let steps = [
        Step::Index(Index::Constant(0)),
        Step::Index(Index::Constant(1)),
        Step::Index(Index::Symbol(ValueId::from_u32(10))),
        Step::Index(Index::Unknown),
    ];
    let mut cases = vec![];
    for initialized in [false, true] {
        let value = ValueState::new(ty, initialized);
        cases.push(value.clone());
        for &step in &steps {
            for write_initialized in [false, true] {
                let mut value = value.clone();
                value.update(ctx, &[step], step != Step::Index(Index::Unknown), &|v| {
                    *v = ValueState::new(Type::I256, write_initialized)
                });
                cases.push(value);
            }
        }
    }
    let equivalent = |a: &ValueState, b: &ValueState| {
        assert_eq!(a.readable(ctx), b.readable(ctx), "{a:?}\n{b:?}");
        for step in steps.into_iter().chain([Step::Index(Index::Constant(2))]) {
            assert_eq!(
                a.child(ctx, step).readable(ctx),
                b.child(ctx, step).readable(ctx),
                "{step:?}: {a:?}\n{b:?}"
            );
        }
    };
    for a in &cases {
        equivalent(a, &a.join(ctx, a));
        for b in &cases {
            let joined = a.join(ctx, b);
            equivalent(&joined, &b.join(ctx, a));
            for c in &cases {
                equivalent(&joined.join(ctx, c), &a.join(ctx, &b.join(ctx, c)));
            }
            for &step in &steps {
                let mut after_a = a.clone();
                let mut after_join = joined.clone();
                let write = |value: &mut ValueState| *value = ValueState::new(Type::I256, true);
                after_a.update(ctx, &[step], step != Step::Index(Index::Unknown), &write);
                after_join.update(ctx, &[step], step != Step::Index(Index::Unknown), &write);
                equivalent(&after_join, &after_join.join(ctx, &after_a));
            }
        }
    }
}

#[test]
fn assertion_reachability_is_monotone() {
    for variant in ["#None", "#Some"] {
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry(v0.@E, v1.objref<@E>) {{
block0:
 enum.assert_variant v0 {variant};
 v2.objref<@E> = enum.assert_variant_ref v1 {variant};
 return;
}}
"#
        );
        let parsed = parse_module(&source).unwrap();
        let ctx = &parsed.module.ctx;
        let cfg = VerifierConfig::default();
        let func = parsed.module.funcs()[0];
        parsed.module.func_store.view(func, |body| {
            let mut verifier = FunctionVerifier::new(ctx, func, body, &cfg, None);
            verifier.run();
            let ty = body.dfg.value_ty(body.arg_values[0]);
            let states: Vec<_> = [false, true]
                .into_iter()
                .flat_map(|complete| {
                    [None, Some(vec![0]), Some(vec![1]), Some(vec![0, 1])]
                        .into_iter()
                        .map(|tags| {
                            let mut value = ValueState::new(ty, complete);
                            value.tags = tags.map(|tags| tags.into_iter().collect());
                            let mut state = State::boundary(&verifier);
                            state.values.insert(body.arg_values[0], value.clone());
                            let refs = state.reference(&verifier, body.arg_values[1]);
                            state.write(ctx, &refs, ty, false, |target| *target = value.clone());
                            state
                        })
                        .collect::<Vec<_>>()
                })
                .collect();
            for a in &states {
                for b in &states {
                    for &inst in verifier.block_to_insts[&verifier.block_order[0]]
                        .iter()
                        .take(2)
                    {
                        let mut lower = a.clone();
                        let mut upper = a.join(ctx, b);
                        let lower_flows =
                            transfer::instruction(&verifier, &mut lower, inst).is_some();
                        let upper_flows =
                            transfer::instruction(&verifier, &mut upper, inst).is_some();
                        assert!(
                            !lower_flows || upper_flows,
                            "joining cannot turn a feasible assertion into NoFlow"
                        );
                    }
                }
            }
        });
    }
}
