//! The record of the machine stage (`SectionLowering::machine_steps`): the
//! steps compose to the machine IR the code is emitted from, every snapshot
//! names each instruction once and keeps the instruction of each value, the
//! facts of a step name values of its input and hold of it, the record is the
//! same in every compilation, and recording it changes no byte.

use std::collections::{BTreeMap, BTreeSet};

use dir_test::{Fixture, dir_test};
use rayon::ThreadPoolBuilder;
use sonatina_codegen::{
    EvmCompile, OptLevel,
    analysis::known_bits::KnownBitsQuery,
    object::{
        ObjectArtifact,
        lowering::{
            FuncSnap, GvnOperand, MachinePassKind, MachineSteps, SectionLowering, StepFacts,
        },
    },
};
use sonatina_parser::parse_module;

fn compile(source: &str, opt: OptLevel, record: bool) -> Option<Vec<ObjectArtifact>> {
    EvmCompile::new(parse_module(source).expect("fixture parses").module)
        .with_opt_level(opt)
        .with_lowering_record(record)
        .compile()
        .ok()
}

/// The text of each function of a module's text, by name.
fn func_texts(module: &str) -> BTreeMap<&str, String> {
    let mut funcs = BTreeMap::new();
    let mut current: Option<(&str, String)> = None;
    for line in module.split_inclusive('\n') {
        if line.starts_with("func ") {
            let name = line.split_once('%').unwrap().1.split('(').next().unwrap();
            current = Some((name, String::new()));
        }
        if let Some((name, text)) = &mut current {
            text.push_str(line);
            if line == "}\n" {
                funcs.insert(*name, std::mem::take(text));
                current = None;
            }
        }
    }
    funcs
}

/// The instruction lines of each block of a function's text, with the block.
fn block_lines(text: &str) -> Vec<(u32, Vec<&str>)> {
    let mut blocks: Vec<(u32, Vec<&str>)> = Vec::new();
    for line in text.lines() {
        if let Some(block) = line
            .strip_prefix("    block")
            .and_then(|rest| rest.strip_suffix(':'))
        {
            blocks.push((block.parse().unwrap(), Vec::new()));
        } else if let Some(inst) = line.strip_prefix("        ") {
            blocks.last_mut().unwrap().1.push(inst);
        }
    }
    blocks
}

/// The values an instruction line defines.
fn defined_values(line: &str) -> Vec<u32> {
    let defs = match line.split_once(" = ") {
        Some((defs, _)) if defs.starts_with('v') || defs.starts_with("(v") => defs,
        _ => return Vec::new(),
    };
    defs.trim_matches(|c| c == '(' || c == ')')
        .split(", ")
        .map(|def| def[1..].split('.').next().unwrap().parse().unwrap())
        .collect()
}

/// Each snapshot has one instruction id per instruction line and names no
/// instruction twice, and every value of the function is defined by one
/// instruction in all of them (`defs`).
fn check_snap(snap: &FuncSnap, defs: &mut BTreeMap<u32, u32>) {
    let blocks = block_lines(&snap.text);
    assert_eq!(blocks.len(), snap.insts.len(), "{}: blocks", snap.func);
    let mut seen = BTreeMap::new();
    for ((block, lines), insts) in blocks.iter().zip(&snap.insts) {
        assert_eq!(
            lines.len(),
            insts.len(),
            "{}: block{block} has {} lines and {} instructions",
            snap.func,
            lines.len(),
            insts.len()
        );
        for (line, inst) in lines.iter().zip(insts) {
            let inst = inst.as_u32();
            assert!(
                seen.insert(inst, *line).is_none(),
                "{}: inst {inst} is printed twice",
                snap.func
            );
            for value in defined_values(line) {
                let def = *defs.entry(value).or_insert(inst);
                assert_eq!(
                    def, inst,
                    "{}: v{value} is defined by inst {def} and by inst {inst}",
                    snap.func
                );
            }
        }
    }
}

/// The arguments of a function's text and the values its instruction lines
/// define.
fn func_values(text: &str) -> BTreeSet<u32> {
    let header = text.lines().next().unwrap();
    let args = header.split_once('(').unwrap().1.split(')').next().unwrap();
    let args = args.split(", ").filter_map(|arg| {
        let arg = arg.rsplit(' ').next()?.strip_prefix('v')?;
        arg.split('.').next()?.parse().ok()
    });
    block_lines(text)
        .iter()
        .flat_map(|(_, lines)| lines.iter().flat_map(|line| defined_values(line)))
        .chain(args)
        .collect()
}

/// The number of destinations of each block's terminator in a function's
/// text.
fn block_dests(text: &str) -> BTreeMap<u32, u32> {
    block_lines(text)
        .iter()
        .map(|(block, lines)| {
            let term = lines.last().unwrap();
            let dests = term
                .split([' ', ';', ')'])
                .filter(|word| word.starts_with("block"));
            (*block, dests.count() as u32)
        })
        .collect()
}

/// The facts of a step name values, edges and instructions of its input,
/// or for value phis of its output, and its known bits are no more than the
/// analysis finds of the input, parsed in the section's machine IR
/// (`machine`) in place of the function's final text (`last`).
fn check_facts(input: &FuncSnap, output: &FuncSnap, facts: &StepFacts, machine: &str, last: &str) {
    let name = input.func.as_str();
    let values = func_values(&input.text);
    let gvn = facts.gvn.iter();
    let operands = gvn
        .clone()
        .flat_map(|gvn| {
            let preds = gvn.preds.iter().flat_map(|(_, _, lhs, rhs)| [lhs, rhs]);
            gvn.class.iter().map(|(_, rep)| rep).chain(preds)
        })
        .filter_map(|operand| match operand {
            GvnOperand::Value(value) => Some(value),
            GvnOperand::Imm(_) => None,
        });
    let classes = gvn
        .clone()
        .flat_map(|gvn| gvn.class.iter().map(|(value, _)| value));
    for value in operands.chain(classes) {
        assert!(
            values.contains(&value.as_u32()),
            "{name}: a GVN fact of v{} not in the step input",
            value.as_u32()
        );
    }
    let output_blocks = block_lines(&output.text);
    for &(value, block, phi) in gvn.clone().flat_map(|gvn| &gvn.value_phis) {
        assert!(values.contains(&value.as_u32()));
        let phi = format!("v{}.", phi.as_u32());
        assert!(
            output_blocks.iter().any(|(id, lines)| *id == block.0
                && lines
                    .iter()
                    .any(|line| line.starts_with(&phi) && line.contains(" = phi "))),
            "{name}: no inserted phi {phi} in block{}",
            block.0
        );
    }
    let demanded = facts.demanded_bits.iter().flatten();
    let consts = facts.sccp.iter().flat_map(|sccp| &sccp.consts);
    for value in facts
        .known_bits
        .iter()
        .map(|(value, ..)| value)
        .chain(demanded.map(|(value, _)| value))
        .chain(consts.map(|(value, _)| value))
    {
        assert!(
            values.contains(&value.as_u32()),
            "{name}: a fact of v{} not defined in the step input",
            value.as_u32()
        );
    }
    let dests = block_dests(&input.text);
    if let Some(ranges) = &facts.ranges {
        let mut entry_values = ranges
            .entry
            .iter()
            .flat_map(|(_, env)| env.iter().map(|range| range.value));
        assert!(
            entry_values.all(|value| values.contains(&value.as_u32())),
            "{name}: a range fact of a value not in the step input"
        );
        let blocks: BTreeSet<_> = ranges
            .unreachable
            .iter()
            .chain(ranges.entry.iter().map(|(block, _)| block))
            .map(|block| block.0)
            .collect();
        assert!(
            blocks.iter().eq(dests.keys()),
            "{name}: range facts are not of the blocks of the step input"
        );
        let insts: BTreeSet<_> = input.insts.iter().flatten().collect();
        assert!(ranges.guarded_subs.iter().all(|inst| insts.contains(inst)));
    }
    let gvn_edges = gvn.flat_map(|gvn| {
        let preds = gvn.preds.iter().map(|&(block, slot, ..)| (block, slot));
        gvn.dead_edges.iter().copied().chain(preds)
    });
    let sccp_edges = facts
        .sccp
        .iter()
        .flat_map(|sccp| sccp.dead_edges.iter().copied());
    for (block, slot) in sccp_edges.chain(gvn_edges) {
        assert!(
            dests.get(&block.0).is_some_and(|&dests| slot < dests),
            "{name}: an edge from slot {slot} of block{}, which the step input lacks",
            block.0
        );
    }
    for finite in &facts.finite_loops {
        let blocks = block_lines(&input.text);
        let header = blocks.iter().find(|(block, _)| *block == finite.header.0);
        let iv = format!("v{}.", finite.iv.as_u32());
        assert!(
            header.is_some_and(|(_, lines)| lines
                .iter()
                .any(|line| line.starts_with(&iv) && line.contains(" = phi "))),
            "{name}: v{} is not a phi of block{}",
            finite.iv.as_u32(),
            finite.header.0
        );
        assert!(values.contains(&finite.step.as_u32()));
        for block in [finite.latch, finite.exit] {
            assert!(dests.contains_key(&block.0), "{name}: no block{}", block.0);
        }
    }
    if facts.known_bits.is_empty() {
        return;
    }
    let parsed = parse_module(&machine.replace(last, &input.text)).expect("a step input parses");
    let func = parsed
        .module
        .funcs()
        .into_iter()
        .find(|&func| parsed.module.ctx.func_sig(func, |sig| sig.name() == name))
        .unwrap();
    parsed.module.func_store.view(func, |function| {
        let known = KnownBitsQuery::new(function);
        for &(value, known_zero, known_one) in &facts.known_bits {
            let parsed_value = parsed
                .debug
                .value(func, &format!("v{}", value.as_u32()))
                .unwrap();
            let bits = known.for_value(function, parsed_value);
            assert!(
                bits.known_zero & known_zero == known_zero
                    && bits.known_one & known_one == known_one,
                "{name}: v{} is claimed {known_zero:#x}/{known_one:#x}, analysis finds {:#x}/{:#x}",
                value.as_u32(),
                bits.known_zero,
                bits.known_one
            );
        }
    });
}

/// Composing `lowered` with the steps gives the functions of `machine_ir`,
/// every snapshot passes `check_snap`, the facts of each step pass
/// `check_facts`, and the passes that read function behavior list it for
/// every function of the section.
fn check_steps(lowering: &SectionLowering) {
    let steps = &lowering.machine_steps;
    let mut current: BTreeMap<_, _> = steps
        .lowered
        .iter()
        .map(|snap| (snap.func.as_str(), snap))
        .collect();
    let mut defs: BTreeMap<_, BTreeMap<_, _>> = BTreeMap::new();
    for snap in &steps.lowered {
        check_snap(snap, defs.entry(snap.func.as_str()).or_default());
    }
    let machine = func_texts(&lowering.machine_ir);
    for pass in &steps.passes {
        let reads_behavior = matches!(
            pass.kind,
            MachinePassKind::CfgCleanup
                | MachinePassKind::ScalarCanonicalize
                | MachinePassKind::Sccp
                | MachinePassKind::Gvn
                | MachinePassKind::Adce
        );
        assert_eq!(
            pass.func_behavior.is_some(),
            reads_behavior,
            "{:?}",
            pass.kind
        );
        if let Some(summaries) = &pass.func_behavior {
            let listed: BTreeSet<_> = summaries
                .iter()
                .map(|summary| summary.func.as_str())
                .collect();
            assert!(current.keys().all(|name| listed.contains(name)));
            assert!(
                summaries
                    .iter()
                    .all(|summary| !(summary.noreturn && summary.will_return))
            );
        }
        for step in &pass.steps {
            assert!(!step.funcs.is_empty(), "{:?}: an empty step", pass.kind);
            for func in &step.funcs {
                let name = func.out.func.as_str();
                let input = current.get_mut(name).expect("a function of the section");
                assert_ne!(
                    input.text, func.out.text,
                    "{name}: {:?} lists it unchanged",
                    step.kind
                );
                check_facts(
                    input,
                    &func.out,
                    &func.facts,
                    &lowering.machine_ir,
                    &machine[name],
                );
                *input = &func.out;
                check_snap(&func.out, defs.get_mut(name).unwrap());
            }
        }
    }
    assert_eq!(
        current.keys().collect::<Vec<_>>(),
        machine.keys().collect::<Vec<_>>()
    );
    for (name, snap) in current {
        assert_eq!(snap.text, machine[name], "{name}: the composed steps");
    }
}

/// The machine steps of each section of `artifacts`.
fn machine_steps(artifacts: &[ObjectArtifact]) -> Vec<&MachineSteps> {
    artifacts
        .iter()
        .flat_map(|artifact| artifact.sections.values())
        .map(|section| &section.lowering.as_ref().unwrap().machine_steps)
        .collect()
}

#[dir_test(dir: "$CARGO_MANIFEST_DIR/test_files/evm", glob: "*.sntn")]
fn machine_steps_compose_to_the_machine_ir(fixture: Fixture<&str>) {
    let source = fixture.content();
    if !source.contains("\nobject ") {
        return;
    }
    let one_thread = ThreadPoolBuilder::new().num_threads(1).build().unwrap();
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::Os, OptLevel::O2] {
        let Some(plain) = compile(source, opt, false) else {
            assert!(compile(source, opt, true).is_none());
            continue;
        };
        let recorded = compile(source, opt, true).expect("fixture compiles");
        for (plain, recorded) in plain.iter().zip(&recorded) {
            for ((name, plain), (_, recorded)) in plain.sections.iter().zip(&recorded.sections) {
                assert_eq!(plain.bytes, recorded.bytes, "{name:?} at {opt:?}");
                check_steps(recorded.lowering.as_ref().unwrap());
            }
        }
        let again = one_thread
            .install(|| compile(source, opt, true))
            .expect("fixture compiles");
        assert_eq!(
            machine_steps(&recorded),
            machine_steps(&again),
            "{opt:?}: the record differs between compilations"
        );
    }
}
