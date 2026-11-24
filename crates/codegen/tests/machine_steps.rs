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
use sonatina_ir::{
    Function, InstId, U256, ValueId,
    inst::{BinaryInstKind, InstClassKind, UnaryInstKind, evm::EvmMstore8},
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
    if facts.known_bits.is_empty() && facts.demanded_bits.is_none() {
        return;
    }
    let parsed = parse_module(&machine.replace(last, &input.text)).expect("a step input parses");
    let func = parsed
        .module
        .funcs()
        .into_iter()
        .find(|&func| parsed.module.ctx.func_sig(func, |sig| sig.name() == name))
        .unwrap();
    let parsed_value = |value: ValueId| {
        parsed
            .debug
            .value(func, &format!("v{}", value.as_u32()))
            .unwrap()
    };
    parsed.module.func_store.view(func, |function| {
        if let Some(demanded) = &facts.demanded_bits {
            let demanded = demanded
                .iter()
                .map(|&(value, bits)| (parsed_value(value), bits))
                .collect();
            check_demanded(name, function, &demanded);
        }
        let known = KnownBitsQuery::new(function);
        for &(value, known_zero, known_one) in &facts.known_bits {
            let bits = known.for_value(function, parsed_value(value));
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

/// The bits of operand `index` of `inst` its result needs when uses read
/// `demand` of the result, on `i256`.
fn operand_demand(function: &Function, inst: InstId, index: usize, demand: U256) -> U256 {
    let args = function.dfg.inst(inst).collect_values();
    let count = function.dfg.value_imm(args[0]);
    let count = count
        .map(|count| count.as_i256().to_u256())
        .filter(|_| index == 1);
    match (function.dfg.inst(inst).kind(), count) {
        (InstClassKind::Unary(UnaryInstKind::Not), _)
        | (
            InstClassKind::Binary(BinaryInstKind::And | BinaryInstKind::Or | BinaryInstKind::Xor),
            _,
        ) => demand,
        (InstClassKind::Binary(BinaryInstKind::Shl), Some(count)) if count < U256::from(256) => {
            demand >> count.as_usize()
        }
        (InstClassKind::Binary(BinaryInstKind::Shr), Some(count)) if count < U256::from(256) => {
            demand << count.as_usize()
        }
        (InstClassKind::Binary(BinaryInstKind::Shl | BinaryInstKind::Shr), Some(_)) => U256::zero(),
        (InstClassKind::Binary(BinaryInstKind::Sar), Some(count)) => {
            // The top `count` bits of the result copy the sign bit.
            let (shifted, fill) = match count.min(U256::from(256)).as_usize() {
                256 => (U256::zero(), U256::MAX),
                count => (demand << count, !(U256::MAX >> count)),
            };
            let sign = if demand & fill == U256::zero() {
                U256::zero()
            } else {
                U256::one() << 255
            };
            shifted | sign
        }
        (InstClassKind::Binary(BinaryInstKind::EvmSignExtend), Some(byte))
            if byte < U256::from(31) =>
        {
            let width = (byte.as_usize() + 1) * 8;
            let low = (U256::one() << width) - 1;
            let sign = if demand & !low == U256::zero() {
                U256::zero()
            } else {
                U256::one() << (width - 1)
            };
            (demand & low) | sign
        }
        (InstClassKind::Binary(BinaryInstKind::EvmSignExtend), Some(_)) => demand,
        _ => U256::MAX,
    }
}

/// The demanded bits of a step, missing ones none, are a post-fixpoint of
/// the backward demanded-bits condition on its input `function`: an
/// instruction used outside values demands all of its operands (`mstore8`
/// only the low byte of its value), a pure one what its result needs of
/// each operand, and a phi its result's demand of each incoming value.
fn check_demanded(name: &str, function: &Function, demanded: &BTreeMap<ValueId, U256>) {
    let of = |value| demanded.get(&value).copied().unwrap_or_default();
    let needs = |inst: InstId, value: ValueId, need: U256| {
        assert!(
            function.dfg.value_is_imm(value) || of(value) & need == need,
            "{name}: inst {} needs {need:#x} of v{}, claimed {:#x}",
            inst.as_u32(),
            value.as_u32(),
            of(value)
        );
    };
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let args = function.dfg.inst(inst).collect_values();
            let results = function.dfg.inst_results(inst);
            if let Some(phi) = function.dfg.cast_phi(inst) {
                for &(incoming, _) in phi.args() {
                    needs(inst, incoming, of(results[0]));
                }
            } else if function.dfg.branch_info(inst).is_some()
                || function.dfg.inst(inst).kind() == InstClassKind::Opaque
                || !function.dfg.can_drop_if_unused(inst)
            {
                let mstore8 = function.dfg.downcast::<&EvmMstore8>(inst).is_some();
                for (index, &arg) in args.iter().enumerate() {
                    // Operand 1 of `mstore8` is the value.
                    let byte = mstore8 && index == 1;
                    needs(inst, arg, if byte { U256::from(255) } else { U256::MAX });
                }
            } else {
                for (result_index, &result) in results.iter().enumerate() {
                    let demand = of(result);
                    if demand.is_zero() {
                        continue;
                    }
                    for (index, &arg) in args.iter().enumerate() {
                        let need = if result_index == 0 {
                            operand_demand(function, inst, index, demand)
                        } else {
                            U256::MAX
                        };
                        needs(inst, arg, need);
                    }
                }
            }
        }
    }
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

/// `check_demanded` on the function `machine_steps_record_demanded_bits_of_dropped_mask`
/// records a demand round of, with the demanded bits of `v0`, `v1` and `v2`.
fn check_masked_byte_store(demanded: [u64; 3]) {
    let parsed = parse_module(
        r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256, v1.i256) {
    block0:
        v2.i256 = and v1 255.i256;
        evm_mstore8 v0 v2;
        return;
}
"#,
    )
    .unwrap();
    let func = parsed.module.funcs()[0];
    let demanded = demanded
        .iter()
        .enumerate()
        .map(|(value, &bits)| {
            let bits = if bits == u64::MAX {
                U256::MAX
            } else {
                U256::from(bits)
            };
            (
                parsed.debug.value(func, &format!("v{value}")).unwrap(),
                bits,
            )
        })
        .collect();
    parsed
        .module
        .func_store
        .view(func, |function| check_demanded("f", function, &demanded));
}

#[test]
fn demanded_bits_of_a_masked_byte_store_are_a_post_fixpoint() {
    check_masked_byte_store([u64::MAX, 255, 255]);
}

/// The record omitted the arguments, which read as demanding nothing.
#[test]
#[should_panic(expected = "needs 0xff")]
fn demanded_bits_without_the_arguments_are_not() {
    check_masked_byte_store([0, 0, 255]);
}
