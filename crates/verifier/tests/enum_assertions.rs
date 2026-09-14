//! Assertions restrict execution; contradictory suffixes contribute no state.
#[path = "support/enum_contract.rs"]
mod contract;

use contract::execute;
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

#[test]
fn contradictory_object_and_value_assertions_do_not_reach_joins() {
    for immutable in [false, true] {
        for feasible in [false, true] {
            let variant = if feasible {
                "#Some (31.i256)"
            } else {
                "#None ()"
            };
            let setup = if immutable {
                format!("v2.@E = enum.make @E {variant};\n enum.assert_variant v2 #Some;")
            } else {
                format!(
                    "v2.objref<@E> = obj.alloc @E;\n enum.write_variant v2 {variant};\n v3.objref<@E> = enum.assert_variant_ref v2 #Some;"
                )
            };
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry(v100.i1, v101.*i256) -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.write_variant v0 #Some (17.i256);
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 br v100 block1 block2;
block1:
 {setup}
 v4.*@E = obj.materialize.stack v0;
 mstore v101 0.i256 i256;
 jump block3;
block2:
 jump block3;
block3:
 v5.i256 = obj.load v1;
 return v5;
}}
"#
            );
            let run = execute(&source, 128);
            assert_eq!(run.invalid_reads(), usize::from(feasible));
            assert_eq!(run.assumptions_pruned, usize::from(!feasible));
            assert_eq!(run.exhausted, 0);
            assert!(run.returned > 0);
        }
    }
}

#[test]
fn contradictions_prune_only_the_instruction_suffix() {
    for read_before in [false, true] {
        let prefix = if read_before {
            "v2.i256 = obj.load v1;"
        } else {
            ""
        };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry() -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.set_tag v0 #None;
 v1.objref<i256> = enum.proj v0 #Some 0.i8;
 {prefix}
 v3.objref<@E> = enum.assert_variant_ref v0 #Some;
 enum.set_tag v0 #None;
 v4.objref<i256> = enum.proj v0 #Some 0.i8;
 v5.i256 = obj.load v4;
 return v5;
}}
"#
        );
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), usize::from(read_before));
        assert_eq!(run.reads.len(), usize::from(read_before));
        assert_eq!(run.assumptions_pruned, 1);
        assert_eq!(run.returned, 0);
        assert_eq!(run.exhausted, 0);
    }
}

#[test]
fn unknown_tags_are_not_contradictions() {
    for immutable in [false, true] {
        let (ty, body) = if immutable {
            (
                "@E",
                "enum.assert_variant v100 #Some;\n v1.i256 = enum.extract v100 #Some 0.i8;",
            )
        } else {
            (
                "objref<@E>",
                "v0.objref<@E> = enum.assert_variant_ref v100 #Some;\n v2.objref<i256> = enum.proj v0 #Some 0.i8;\n v1.i256 = obj.load v2;",
            )
        };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry(v100.{ty}) -> i256 {{
block0:
 {body}
 return v1;
}}
"#
        );
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), 0);
        assert_eq!(run.assumptions_pruned, 1);
        assert_eq!(run.returned, 1);
        assert_eq!(run.exhausted, 0);
    }
}

#[test]
fn an_ambiguous_reference_retains_its_feasible_alternative() {
    for retag in [false, true] {
        let mutation = if retag { "enum.set_tag v2 #None;" } else { "" };
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry(v100.i1) -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.set_tag v0 #None;
 v1.objref<@E> = obj.alloc @E;
 enum.write_variant v1 #Some (17.i256);
 br v100 block1 block2;
block1:
 jump block3;
block2:
 jump block3;
block3:
 v2.objref<@E> = phi (v0 block1) (v1 block2);
 v3.objref<@E> = enum.assert_variant_ref v2 #Some;
 {mutation}
 v4.objref<i256> = enum.proj v3 #Some 0.i8;
 v5.i256 = obj.load v4;
 return v5;
}}
"#
        );
        let run = execute(&source, 128);
        assert_eq!(run.invalid_reads(), usize::from(retag));
        assert_eq!(run.assumptions_pruned, 1);
        assert_eq!(run.returned, 1);
        assert_eq!(run.exhausted, 0);
    }
}

const REVISIT: &str = include_str!("fixtures/enum_contract/assertion-revisit.sntn");

#[test]
fn loop_revisitation_can_make_an_assertion_feasible() {
    let run = execute(REVISIT, 128);
    assert_eq!(run.invalid_reads(), 0);
    assert_eq!(run.returned, 1);
    assert_eq!(run.exhausted, 0);
}

#[test]
fn pruned_suffixes_still_receive_type_and_ssa_validation() {
    for invalid in [
        "v2.i256 = obj.load v0;",
        "v2.i256 = add v3 1.i256;\n v3.i256 = add 1.i256 2.i256;",
    ] {
        let source = format!(
            r#"
target = "evm-ethereum-osaka"
type @E = enum {{ #None, #Some(i256) }};
func private %entry() -> i256 {{
block0:
 v0.objref<@E> = obj.alloc @E;
 enum.set_tag v0 #None;
 v1.objref<@E> = enum.assert_variant_ref v0 #Some;
 {invalid}
 return v2;
}}
"#
        );
        let parsed = parse_module(&source).unwrap();
        for level in [VerificationLevel::Standard, VerificationLevel::Full] {
            let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
            assert!(report.has_errors(), "{level:?}: {source}\n{report}");
        }
    }
}
