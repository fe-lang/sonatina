//! Independent finite object executions and transformations of equivalent IR.
//! These tests query the public verifier, never its proof/effect implementation.
use sonatina_parser::parse_module;
use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};
use std::collections::HashSet;

#[derive(Clone, Copy, Debug)]
enum Op {
    Some(usize),
    None(usize),
    Store(usize),
    Expose(usize),
    RawWrite,
    SeparateWrite,
}
const OPS: [Op; 10] = [
    Op::Some(0),
    Op::Some(1),
    Op::None(0),
    Op::None(1),
    Op::Store(0),
    Op::Store(1),
    Op::Expose(0),
    Op::Expose(1),
    Op::RawWrite,
    Op::SeparateWrite,
];
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Cell {
    tag: bool,
    payload: Option<u8>,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct World {
    cells: [Cell; 2],
    addresses: [bool; 2],
}
impl World {
    fn initial() -> Self {
        Self {
            cells: [Cell {
                tag: true,
                payload: Some(17),
            }; 2],
            addresses: [false; 2],
        }
    }
    fn execute(mut self, op: Op) -> Vec<Self> {
        match op {
            Op::Some(i) => {
                self.cells[i] = Cell {
                    tag: true,
                    payload: Some(22),
                }
            }
            Op::None(i) => {
                self.cells[i] = Cell {
                    tag: false,
                    payload: None,
                }
            }
            Op::Store(i) => self.cells[i].payload = Some(33),
            Op::Expose(i) => self.addresses[i] = true,
            Op::SeparateWrite => {}
            Op::RawWrite => {
                // The raw address may miss both objects or hit any exposed
                // object. Enumerate concrete contents, not verifier facts.
                let mut outcomes = vec![self];
                for (i, address) in self.addresses.iter().enumerate() {
                    if !address {
                        continue;
                    }
                    for value in [
                        Cell {
                            tag: false,
                            payload: None,
                        },
                        Cell {
                            tag: true,
                            payload: None,
                        },
                        Cell {
                            tag: true,
                            payload: Some(44),
                        },
                    ] {
                        let mut changed = self;
                        changed.cells[i] = value;
                        outcomes.push(changed);
                    }
                }
                return outcomes;
            }
        }
        vec![self]
    }
}
fn execute(ops: &[Op]) -> HashSet<World> {
    ops.iter()
        .fold(HashSet::from([World::initial()]), |worlds, &op| {
            worlds.into_iter().flat_map(|w| w.execute(op)).collect()
        })
}
fn emit(ops: &[Op], next: &mut usize) -> String {
    let mut source = String::new();
    for &op in ops {
        let instruction = match op {
            Op::Some(i) => format!("enum.write_variant v{i} #Some (22.i256);"),
            Op::None(i) => format!("enum.write_variant v{i} #None;"),
            Op::Store(i) => format!("obj.store v{} 33.i256;", i + 2),
            Op::Expose(i) => {
                *next += 1;
                format!("v{next}.*@Choice = obj.materialize.stack v{i};")
            }
            Op::RawWrite => "mstore v100 0.i256 i256;".to_owned(),
            Op::SeparateWrite => "mstore v4 99.i256 i256;".to_owned(),
        };
        source.push_str(&instruction);
        source.push('\n');
    }
    source
}
const PREFIX: &str = r#"
target = "evm-ethereum-osaka"
type @Choice = enum { #None, #Some(i256) };
func private %entry(v100.*i256, v101.i1) -> i256 {
block0:
 v0.objref<@Choice> = obj.alloc @Choice;
 v1.objref<@Choice> = obj.alloc @Choice;
 enum.write_variant v0 #Some (17.i256);
 enum.write_variant v1 #Some (17.i256);
 v2.objref<i256> = enum.proj v0 #Some 0.i8;
 v3.objref<i256> = enum.proj v1 #Some 0.i8;
 v4.*i256 = alloca i256;
"#;
const LOADS: &str =
    "v5.i256 = obj.load v2;\nv6.i256 = obj.load v3;\nv7.i256 = add v5 v6;\nreturn v7;\n}\n";
fn check(source: &str, worlds: &HashSet<World>) {
    let invalid = [0, 1]
        .into_iter()
        .filter(|&i| {
            worlds
                .iter()
                .any(|w| !w.cells[i].tag || w.cells[i].payload.is_none())
        })
        .count();
    let parsed = parse_module(source).expect("model program parses");
    let report = verify_module(
        &parsed.module,
        &VerifierConfig::for_level(VerificationLevel::Full),
    );
    assert_eq!(report.errors().count(), invalid, "{source}\n{report}");
    if invalid != 0 {
        assert!(report.to_string().contains("IR0600"), "{report}");
    }
}
#[test]
fn finite_object_executions_match_load_acceptance() {
    for a in OPS {
        for b in OPS {
            for c in OPS {
                let ops = [a, b, c];
                let source = format!("{PREFIX}{}{LOADS}", emit(&ops, &mut 110));
                check(&source, &execute(&ops));
            }
        }
    }
}
#[test]
fn path_union_matches_diamond_load_acceptance() {
    for a in OPS {
        for b in OPS {
            for c in OPS {
                let left = [a, b];
                let right = [c];
                let mut worlds = execute(&left);
                worlds.extend(execute(&right));
                let mut next = 110;
                let left = emit(&left, &mut next);
                let right = emit(&right, &mut next);
                let source = format!(
                    "{PREFIX}br v101 block1 block2;\nblock1:\n{left}jump block3;\nblock2:\n{right}jump block3;\nblock3:\n{LOADS}"
                );
                check(&source, &worlds);
            }
        }
    }
}
#[test]
fn concrete_loop_closure_matches_exposure_on_backedges() {
    for a in OPS {
        for b in OPS {
            let ops = [a, b];
            let mut reached = HashSet::from([World::initial()]);
            let mut exits = HashSet::new();
            let mut pending = vec![World::initial()];
            while let Some(world) = pending.pop() {
                let outcomes = ops.iter().fold(vec![world], |states, &op| {
                    states.into_iter().flat_map(|w| w.execute(op)).collect()
                });
                for outcome in outcomes {
                    exits.insert(outcome);
                    if reached.insert(outcome) {
                        pending.push(outcome);
                    }
                }
            }
            let body = emit(&ops, &mut 110);
            let source = format!(
                "{PREFIX}jump block1;\nblock1:\n{body}br v101 block1 block2;\nblock2:\n{LOADS}"
            );
            check(&source, &exits);
        }
    }
}

fn verify_verdict(source: &str, valid: bool) {
    let parsed = parse_module(source).expect("parse");
    for level in [VerificationLevel::Standard, VerificationLevel::Full] {
        let report = verify_module(&parsed.module, &VerifierConfig::for_level(level));
        assert_eq!(!report.has_errors(), valid, "{source}\n{report}");
    }
}
#[test]
fn block_permutations_preserve_disconnected_proofs_and_dominance() {
    for blocks in [
        [
            "block1:\n v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;\n jump block2;",
            "block2:\n v2.objref<i256> = enum.proj v1 #Some 0.i8;\n jump block3;",
            "block3:\n v3.i256 = obj.load v2;\n return v3;",
        ],
        [
            "block1:\n v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;\n jump block3;",
            "block2:\n v2.objref<@Choice> = enum.assert_variant_ref v0 #Some;\n jump block3;",
            "block3:\n v3.objref<i256> = enum.proj v0 #Some 0.i8;\n v4.i256 = obj.load v3;\n return v4;",
        ],
    ] {
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let body = order.map(|i| blocks[i]).join("\n");
            let source = format!(
                "target = \"evm-ethereum-osaka\"\ntype @Choice = enum {{ #None, #Some(i256) }};\nfunc private %entry(v0.objref<@Choice>) -> i256 {{\nblock0:\n return 0.i256;\n{body}\n}}\n"
            );
            verify_verdict(&source, true);
        }
    }
}
#[test]
fn closed_source_cycles_have_no_layout_selected_entry() {
    let blocks = [
        "block1:\n v1.objref<@Choice> = enum.assert_variant_ref v0 #Some;\n jump block2;",
        "block2:\n v2.objref<i256> = enum.proj v0 #Some 0.i8;\n v3.i256 = obj.load v2;\n jump block1;",
    ];
    for order in [[0, 1], [1, 0]] {
        let body = order.map(|i| blocks[i]).join("\n");
        let source = format!(
            "target = \"evm-ethereum-osaka\"\ntype @Choice = enum {{ #None, #Some(i256) }};\nfunc private %entry(v0.objref<@Choice>) {{\nblock0:\n return;\n{body}\n}}\n"
        );
        verify_verdict(&source, false);
    }
}
#[test]
fn payloadless_tag_and_variant_writes_are_equivalent() {
    for write in ["enum.set_tag v2 #None;", "enum.write_variant v2 #None;"] {
        for init in [
            "enum.set_tag v0 #Some;",
            "v1.objref<@Outer> = enum.assert_variant_ref v0 #Some;",
        ] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @Inner = enum {{ #None, #Some(i256) }};
type @Outer = enum {{ #None, #Some(@Inner) }};
func private %entry(v0.objref<@Outer>) -> @Inner {{
block0:
 {init}
 v2.objref<@Inner> = enum.proj v0 #Some 0.i8;
 {write}
 v3.@Inner = obj.load v2;
 return v3;
}}
"#
            );
            verify_verdict(&source, true);
        }
    }
}

#[test]
fn separate_raw_writes_require_proven_bounds() {
    for (write, bounded) in [
        ("mstore v4 99.i256 i256;", true),
        ("memzero v4 0.i256;", true),
        ("memzero v4 31.i256;", true),
        ("memzero v4 32.i256;", true),
        ("memzero v4 33.i256;", false),
        ("v9.i256 = evm_calldata_size;\nmemzero v4 v9;", false),
        ("mstore v100 99.i256 i256;", false),
    ] {
        for expose in [false, true] {
            let materialize = if expose {
                "v8.*@Choice = obj.materialize.stack v0;"
            } else {
                ""
            };
            verify_verdict(
                &format!("{PREFIX}{materialize}\n{write}\n{LOADS}"),
                bounded || !expose,
            );
        }
    }
}

#[test]
fn equivalent_places_share_proofs_and_allocation_exposure() {
    for index in ["0.i8", "0.i256"] {
        for expose in ["", "v6.*@Choice = obj.materialize.stack v2;"] {
            let source = format!(
                r#"
target = "evm-ethereum-osaka"
type @Choice = enum {{ #None, #Some(i256) }};
type @Pair = {{ @Choice, @Choice }};
func private %entry(v100.*i256) -> i256 {{
block0:
 v0.objref<@Pair> = obj.alloc @Pair;
 v1.objref<@Choice> = obj.proj v0 0.i8;
 v2.objref<@Choice> = obj.proj v0 1.i8;
 enum.write_variant v1 #Some (17.i256);
 v3.objref<@Choice> = obj.proj v0 {index};
 v4.objref<i256> = enum.proj v3 #Some 0.i256;
 {expose}
 mstore v100 0.i256 i256;
 v5.i256 = obj.load v4;
 return v5;
}}
"#
            );
            // Materializing a sibling exposes the shared allocation, so an
            // unknown raw address may then overwrite the first object's tag.
            verify_verdict(&source, expose.is_empty());
        }
    }
}
