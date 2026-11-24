//! The record of the machine stage (`SectionLowering::machine_steps`): the
//! steps compose to the machine IR the code is emitted from, every snapshot
//! names each instruction once and keeps the instruction of each value, the
//! record is the same in every compilation, and recording it changes no byte.

use std::collections::BTreeMap;

use dir_test::{Fixture, dir_test};
use rayon::ThreadPoolBuilder;
use sonatina_codegen::{
    EvmCompile, OptLevel,
    object::{
        ObjectArtifact,
        lowering::{FuncSnap, MachineSteps, SectionLowering},
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

/// Composing `lowered` with the steps gives the functions of `machine_ir`,
/// and every snapshot passes `check_snap`.
fn check_steps(lowering: &SectionLowering) {
    let steps = &lowering.machine_steps;
    let mut current: BTreeMap<_, _> = steps
        .lowered
        .iter()
        .map(|snap| (snap.func.as_str(), &snap.text))
        .collect();
    let mut defs: BTreeMap<_, BTreeMap<_, _>> = BTreeMap::new();
    for snap in &steps.lowered {
        check_snap(snap, defs.entry(snap.func.as_str()).or_default());
    }
    let machine = func_texts(&lowering.machine_ir);
    for pass in &steps.passes {
        for step in &pass.steps {
            assert!(!step.funcs.is_empty(), "{:?}: an empty step", pass.kind);
            for func in &step.funcs {
                let name = func.out.func.as_str();
                let text = current.get_mut(name).expect("a function of the section");
                assert_ne!(
                    *text, &func.out.text,
                    "{name}: {:?} lists it unchanged",
                    step.kind
                );
                *text = &func.out.text;
                check_snap(&func.out, defs.get_mut(name).unwrap());
            }
        }
    }
    assert_eq!(
        current.keys().collect::<Vec<_>>(),
        machine.keys().collect::<Vec<_>>()
    );
    for (name, text) in current {
        assert_eq!(text, &machine[name], "{name}: the composed steps");
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
