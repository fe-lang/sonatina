//! Value labels and operand stack plans, driven as an external front end drives them: through
//! `EvmCompile`, `EvmBackend` and the observability data.
//!
//! One test follows labels from the IR through the optimization and lowering of a small function,
//! and one checks the exported plan of it. The corpus tests compile every fixture of
//! `test_files/evm` and show two things. First, that attaching labels, and attaching labels and
//! capturing stack plans, change neither the section bytes nor the PC map, at every optimization
//! level. Second, that the stack plan of every machine instruction is structurally consistent with
//! the opcodes that the backend emits for it at level 0. That second check does not run the code
//! and cannot see a wrong order of the words that an instruction consumes. The comparison with
//! executed code is in `tests/evm.rs`.

use dir_test::{Fixture, dir_test};

use sonatina_codegen::{
    Compile, EvmCompile, EvmCompiler, OptLevel,
    isa::evm::{
        EvmBackend, ImmediateMaterializationMode, LateCleanupProfile,
        opcode::OpCode,
        stack_plan::{InstStack, StackEntry},
    },
    machinst::{lower::SectionWorkModule, vcode::SectionCodeUnitId},
    object::{MachineInstId, ObjectArtifact, PcMapUnit, SectionArtifact, SectionObservability},
    stackalloc::StackifySearchProfile,
};
use sonatina_ir::{
    Module, ObjectName, SectionName, ValueId, ValueLabel, isa::evm::Evm, module::FuncRef,
};
use sonatina_parser::parse_module;
use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

/// `%combine` computes `(a + b) * (a + b)` with two separate additions. The additions are equal
/// values, so the machine passes keep one of them, and the labels of both must end up on it.
const COMBINE: &str = r#"
target = "evm-ethereum-osaka"

func private %combine(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = add v0 v1;
        v3.i256 = add v0 v1;
        v4.i256 = mul v2 v3;
        return v4;
}

func public %runtime() {
    block0:
        v0.i256 = evm_calldata_load 0.i32;
        v1.i256 = evm_calldata_load 32.i32;
        v2.i256 = call %combine v0 v1;
        mstore 0.i256 v2 i256;
        evm_return 0.i256 32.i256;
}

object @Contract {
  section runtime {
    entry %runtime;
  }
}
"#;

// ---- helpers -------------------------------------------------------------

fn osaka() -> TargetTriple {
    TargetTriple::new(
        Architecture::Evm,
        Vendor::Ethereum,
        OperatingSystem::Evm(EvmVersion::Osaka),
    )
}

/// The backend that `EvmCompile` builds at `opt`, with trace capture as asked.
fn backend_at(opt: OptLevel, capture: bool) -> EvmBackend {
    let (late_cleanup, search, immediates) = match opt {
        OptLevel::O0 => (
            LateCleanupProfile::Off,
            StackifySearchProfile::Fast,
            ImmediateMaterializationMode::Gas,
        ),
        OptLevel::O1 => (
            LateCleanupProfile::Speed,
            StackifySearchProfile::GreedyWide,
            ImmediateMaterializationMode::Gas,
        ),
        OptLevel::Os => (
            LateCleanupProfile::Size,
            StackifySearchProfile::Exact,
            ImmediateMaterializationMode::Size,
        ),
        OptLevel::O2 => (
            LateCleanupProfile::Speed,
            StackifySearchProfile::Exact,
            ImmediateMaterializationMode::Balanced,
        ),
    };
    EvmBackend::new(Evm::new(osaka()))
        .with_late_cleanup_profile(late_cleanup)
        .with_stackify_search_profile(search)
        .with_immediate_materialization_mode(immediates)
        .with_stackify_trace_capture(capture)
}

fn o0_backend(capture: bool) -> EvmBackend {
    backend_at(OptLevel::O0, capture)
}

/// Fixtures that are meant to fail compiling say so with an `evm.error` directive. Any other
/// fixture that fails is a failure of the test, not something to skip.
fn assert_expected_error(name: &str, source: &str, error: &str) {
    assert!(
        source.contains("evm.error"),
        "{name}: fails to compile without an `evm.error` directive: {error}"
    );
}

fn func_named(module: &Module, name: &str) -> FuncRef {
    module
        .funcs()
        .into_iter()
        .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == name))
        .unwrap_or_else(|| panic!("function `{name}` not found"))
}

/// Gives every value of every function the label `function * 100000 + value`.
fn label_every_value(module: &Module) {
    for func in module.funcs() {
        module.func_store.modify(func, |function| {
            let values: Vec<ValueId> = function.dfg.value_ids().collect();
            for value in values {
                function
                    .dfg
                    .add_value_label(value, ValueLabel(func.as_u32() * 100_000 + value.as_u32()));
            }
        });
    }
}

fn compile(module: Module, opt: OptLevel, plans: bool) -> Result<Vec<ObjectArtifact>, String> {
    EvmCompile::new(module)
        .with_opt_level(opt)
        .with_observability(true)
        .with_stack_plans(plans)
        .compile()
        .map_err(|errors| format!("{errors:?}"))
}

fn section_artifact<'a>(artifacts: &'a [ObjectArtifact], name: &str) -> &'a SectionArtifact {
    artifacts[0]
        .sections
        .iter()
        .find(|(section, _)| section.0.as_str() == name)
        .map(|(_, artifact)| artifact)
        .expect("section artifact")
}

fn section_obs<'a>(artifacts: &'a [ObjectArtifact], name: &str) -> &'a SectionObservability {
    section_artifact(artifacts, name)
        .observability
        .as_ref()
        .expect("section observability")
}

// ---- labels survive the pipeline -------------------------------------------

/// Labels attached to the source function of `COMBINE`, by source value.
const LABEL_A: ValueLabel = ValueLabel(10);
const LABEL_B: ValueLabel = ValueLabel(11);
const LABEL_SUM: ValueLabel = ValueLabel(12);
const LABEL_SUM_AGAIN: ValueLabel = ValueLabel(13);
const LABEL_PRODUCT: ValueLabel = ValueLabel(14);

/// Parses `COMBINE` and labels the values of `%combine`: the two arguments, the two equal sums and
/// the product.
fn labelled_combine() -> Module {
    let parsed = parse_module(COMBINE).expect("fixture parses");
    let module = parsed.module;
    let combine = func_named(&module, "combine");
    module.func_store.modify(combine, |function| {
        let args = function.arg_values.clone();
        let results: Vec<ValueId> = function
            .dfg
            .value_ids()
            .filter(|&value| function.dfg.value_inst(value).is_some())
            .collect();
        assert_eq!((args.len(), results.len()), (2, 3));
        for (value, label) in args.into_iter().chain(results).zip([
            LABEL_A,
            LABEL_B,
            LABEL_SUM,
            LABEL_SUM_AGAIN,
            LABEL_PRODUCT,
        ]) {
            function.dfg.add_value_label(value, label);
        }
    });
    module
}

#[test]
fn labels_survive_machine_lowering_and_merge_when_equal_values_are_merged() {
    let module = labelled_combine();
    let runtime = func_named(&module, "runtime");
    let combine = func_named(&module, "combine");
    let prepared = o0_backend(false)
        .prepare_section(SectionWorkModule::from_roots(
            &module,
            runtime,
            &[combine],
            &[],
        ))
        .expect("section prepares");

    let machine_labels: Vec<Vec<ValueLabel>> =
        prepared.module().func_store.view(combine, |function| {
            function
                .dfg
                .value_ids()
                .map(|value| function.dfg.value_labels(value).to_vec())
                .filter(|labels| !labels.is_empty())
                .collect()
        });

    // The arguments and the product keep their labels. The two additions compute one value, which
    // the machine passes keep once, so the survivor carries the labels of both.
    assert!(
        machine_labels.contains(&vec![LABEL_A]),
        "{machine_labels:?}"
    );
    assert!(
        machine_labels.contains(&vec![LABEL_B]),
        "{machine_labels:?}"
    );
    assert!(
        machine_labels.contains(&vec![LABEL_SUM, LABEL_SUM_AGAIN]),
        "{machine_labels:?}"
    );
    assert!(
        machine_labels.contains(&vec![LABEL_PRODUCT]),
        "{machine_labels:?}"
    );
    assert_eq!(machine_labels.len(), 4, "{machine_labels:?}");

    // Functions that were never labelled stay free of labels.
    let unlabelled = prepared.module().func_store.view(runtime, |function| {
        function
            .dfg
            .value_ids()
            .all(|value| function.dfg.value_labels(value).is_empty())
    });
    assert!(unlabelled);
}

// ---- the exported plan ---------------------------------------------------

/// The machine instruction whose first emitted opcode in `func_name` is `opcode`, with the unit
/// of its PC map entry.
fn first_inst_emitting(
    obs: &SectionObservability,
    bytes: &[u8],
    func_name: &str,
    opcode: OpCode,
) -> (PcMapUnit, MachineInstId) {
    obs.pc_map
        .iter()
        .filter(|entry| entry.func_name == func_name)
        .filter(|entry| bytes[entry.pc_start as usize] == opcode as u8)
        .find_map(|entry| Some((entry.unit.clone(), entry.attribution.machine_inst()?)))
        .unwrap_or_else(|| panic!("no instruction of `{func_name}` emits {opcode:?}"))
}

fn value_labels(entry: &StackEntry) -> &[ValueLabel] {
    match entry {
        StackEntry::Value(value) => &value.labels,
        other => panic!("expected a value, found {other:?}"),
    }
}

#[test]
fn exported_plan_shows_labelled_values_at_the_planned_positions() {
    let artifacts = compile(labelled_combine(), OptLevel::O0, true).expect("compiles");
    let section = section_artifact(&artifacts, "runtime");
    let obs = section.observability.as_ref().expect("observability");
    assert_eq!(obs.schema_version, "0.4.0");

    // `add` reads both arguments from the top of the stack, above the return address.
    let (unit, add) = first_inst_emitting(obs, &section.bytes, "combine", OpCode::ADD);
    let stack = &obs.stack_before(&unit, add).expect("plan for add").stack;
    assert_eq!(stack.len(), 3);
    assert_eq!(value_labels(&stack[0]), &[LABEL_A]);
    assert_eq!(value_labels(&stack[1]), &[LABEL_B]);
    assert_eq!(stack[2], StackEntry::ReturnAddress);

    // The merged sum is the only value below the return address when `mul` starts, and it
    // carries the labels of both source additions. The arguments are gone: no label, no position.
    let (unit, mul) = first_inst_emitting(obs, &section.bytes, "combine", OpCode::MUL);
    let stack = &obs.stack_before(&unit, mul).expect("plan for mul").stack;
    assert_eq!(stack.len(), 2);
    assert_eq!(value_labels(&stack[0]), &[LABEL_SUM, LABEL_SUM_AGAIN]);
    assert_eq!(stack[1], StackEntry::ReturnAddress);
    let StackEntry::Value(sum) = &stack[0] else {
        unreachable!()
    };
    assert!(!sum.dead && !sum.constant);

    // The return reads the product, which has its own label.
    let (unit, ret) = first_inst_emitting(obs, &section.bytes, "combine", OpCode::JUMP);
    let stack = &obs.stack_before(&unit, ret).expect("plan for return").stack;
    assert_eq!(value_labels(&stack[0]), &[LABEL_PRODUCT]);

    // Values of an unlabelled function carry no labels, and a synthetic unit has no plan.
    let (unit, mstore) = first_inst_emitting(obs, &section.bytes, "runtime", OpCode::MSTORE);
    let stack = &obs
        .stack_before(&unit, mstore)
        .expect("plan for mstore")
        .stack;
    assert!(stack.iter().all(|entry| value_labels(entry).is_empty()));
    assert!(
        obs.stack_before(
            &PcMapUnit::Synthetic {
                object: ObjectName("Contract".into()),
                section: SectionName("runtime".into()),
                unit: SectionCodeUnitId(0),
            },
            mstore
        )
        .is_none()
    );

    // The renderings carry the plan.
    let text = obs.to_text();
    assert!(text.contains("stack_plan func=combine"), "{text}");
    assert!(text.contains("@12@13, <RET>]"), "{text}");
    assert!(!text.contains("spill"), "{text}");
    let json = obs.to_json();
    assert!(json.contains("\"stack_plans\":[{"), "{json}");
    assert!(json.contains("\"labels\":[12,13]"), "{json}");
    assert!(!json.contains("spill"), "{json}");
}

#[test]
fn plans_are_absent_unless_requested() {
    let off = compile(labelled_combine(), OptLevel::O0, false).expect("compiles");
    let obs = section_obs(&off, "runtime");
    assert!(obs.stack_plans.is_empty());
    assert!(!obs.to_text().contains("stack_plan"));
    assert!(obs.to_json().contains("\"stack_plans\":[]"));
}

// ---- byte identity over the corpus ---------------------------------------

/// Checks that brackets and braces of `json` nest and close outside strings, and that no comma
/// dangles. The crate has no JSON parser to check more.
fn assert_json_nests(name: &str, json: &str) {
    let mut open = Vec::new();
    let mut in_string = false;
    let mut escaped = false;
    for (idx, ch) in json.char_indices() {
        if in_string {
            match (escaped, ch) {
                (true, _) => escaped = false,
                (false, '\\') => escaped = true,
                (false, '"') => in_string = false,
                _ => {}
            }
            continue;
        }
        match ch {
            '"' => in_string = true,
            '{' | '[' => open.push(ch),
            '}' => assert_eq!(open.pop(), Some('{'), "{name}: unbalanced `}}` at {idx}"),
            ']' => assert_eq!(open.pop(), Some('['), "{name}: unbalanced `]` at {idx}"),
            ',' => {
                let next = json[idx + 1..].chars().next();
                assert!(
                    next.is_some_and(|next| !matches!(next, ',' | ']' | '}')),
                    "{name}: dangling comma at {idx}"
                );
            }
            _ => {}
        }
    }
    assert!(open.is_empty() && !in_string, "{name}: JSON does not close");
}

/// Asserts that `other` has the bytes, the PC map and the byte totals of `plain`.
fn assert_same_code(
    name: &str,
    what: &str,
    plain: &[ObjectArtifact],
    other: &[ObjectArtifact],
) -> usize {
    assert_eq!(plain.len(), other.len(), "{name}: {what}");
    let mut planned_insts = 0;
    for (plain, other) in plain.iter().zip(other) {
        assert_eq!(plain.object, other.object, "{name}: {what}");
        assert_eq!(plain.sections.len(), other.sections.len(), "{name}: {what}");
        for ((plain_name, plain), (other_name, other)) in plain.sections.iter().zip(&other.sections)
        {
            assert_eq!(plain_name, other_name, "{name}: {what}");
            assert_eq!(
                plain.bytes, other.bytes,
                "{name}: {what}: bytes of {plain_name:?}"
            );
            let plain = plain.observability.as_ref().expect("observability");
            let other = other.observability.as_ref().expect("observability");
            assert_eq!(
                plain.pc_map, other.pc_map,
                "{name}: {what}: PC map of {plain_name:?}"
            );
            assert_eq!(
                (plain.code_bytes, plain.data_bytes, plain.embed_bytes),
                (other.code_bytes, other.data_bytes, other.embed_bytes),
                "{name}: {what}"
            );
            assert_eq!(
                (plain.mapped_code_bytes, plain.unmapped_code_bytes),
                (other.mapped_code_bytes, other.unmapped_code_bytes),
                "{name}: {what}"
            );
            assert!(
                plain.stack_plans.is_empty(),
                "{name}: plans were not requested"
            );
            planned_insts += other
                .stack_plans
                .iter()
                .map(|function| function.plan.insts.len())
                .sum::<usize>();
        }
    }
    planned_insts
}

/// Compiles `source` three times: with no labels and no plans, with every value labelled and no
/// plans, and with every value labelled and plans on. Section bytes and PC maps of the second
/// and the third must equal the first, so labels alone and labels with plans are each shown not
/// to change generated code. With plans off no plan may appear, and with them on some must.
/// Returns whether the fixture compiled.
fn assert_byte_identity(name: &str, source: &str, opt: OptLevel) -> bool {
    let parsed = parse_module(source).unwrap_or_else(|error| panic!("{name}: {error:?}"));
    let plain = match compile(parsed.module, opt, false) {
        Ok(plain) => plain,
        Err(error) => {
            assert_expected_error(name, source, &error);
            return false;
        }
    };

    let labelled_module = parse_module(source).expect("parses again").module;
    label_every_value(&labelled_module);
    let labelled = compile(labelled_module, opt, false)
        .unwrap_or_else(|error| panic!("{name}: fails with labels only: {error}"));
    let unplanned = assert_same_code(name, "labels, plans off", &plain, &labelled);
    assert_eq!(unplanned, 0, "{name}: plans were not requested");

    let planned_module = parse_module(source).expect("parses again").module;
    label_every_value(&planned_module);
    let planned = compile(planned_module, opt, true)
        .unwrap_or_else(|error| panic!("{name}: fails with labels and plans: {error}"));
    let planned_insts = assert_same_code(name, "labels, plans on", &plain, &planned);
    // The comparison is not vacuous: the third compile did export plans.
    assert!(planned_insts > 0, "{name}: no plan was exported");
    for artifact in &planned {
        for section in artifact.sections.values() {
            let obs = section.observability.as_ref().expect("observability");
            assert_json_nests(name, &obs.to_json());
        }
    }
    true
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm",
    glob: "*.sntn"
)]
fn labels_and_plans_keep_bytes_and_pc_map_at_o0(fixture: Fixture<&str>) {
    assert_byte_identity(fixture.path(), fixture.content(), OptLevel::O0);
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm",
    glob: "*.sntn"
)]
fn labels_and_plans_keep_bytes_and_pc_map_at_o1(fixture: Fixture<&str>) {
    assert_byte_identity(fixture.path(), fixture.content(), OptLevel::O1);
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm",
    glob: "*.sntn"
)]
fn labels_and_plans_keep_bytes_and_pc_map_at_os(fixture: Fixture<&str>) {
    assert_byte_identity(fixture.path(), fixture.content(), OptLevel::Os);
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm",
    glob: "*.sntn"
)]
fn labels_and_plans_keep_bytes_and_pc_map_at_o2(fixture: Fixture<&str>) {
    assert_byte_identity(fixture.path(), fixture.content(), OptLevel::O2);
}

// ---- the plan against the emitted opcodes --------------------------------

/// A word of a replayed stack. Planned entries keep their identity; a word that an emitted
/// `PUSH` made has none beyond being a constant.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Slot {
    Value(ValueId),
    Constant(ValueId),
    Pushed,
    ReturnAddress,
    CallContinuation,
}

impl Slot {
    fn is_constant(&self) -> bool {
        matches!(self, Slot::Constant(_) | Slot::Pushed)
    }

    /// Two words are the same word when they are the same value, or when both are constants: a
    /// constant that an opcode pushed and a copy of the same immediate that the allocator kept
    /// are indistinguishable without reading the immediate bytes.
    fn same_word(&self, other: &Slot) -> bool {
        self == other || (self.is_constant() && other.is_constant())
    }
}

fn slots(record: &InstStack) -> Vec<Slot> {
    record
        .stack
        .iter()
        .map(|entry| match entry {
            StackEntry::Value(value) if value.constant => Slot::Constant(value.value),
            StackEntry::Value(value) => Slot::Value(value.value),
            StackEntry::ReturnAddress => Slot::ReturnAddress,
            StackEntry::CallContinuation => Slot::CallContinuation,
        })
        .collect()
}

/// Applies the leading `PUSH`, `DUP`, `SWAP` and `POP` opcodes of a group, which are the stack
/// opcodes the emitter adds before an instruction's own operation. Returns the stack after them
/// and the number of opcodes applied, or `None` when an opcode needs more words than the stack
/// has. A `NOT` directly after a `PUSH` is part of building one constant (`PUSH0 NOT` is -1).
fn replay_prefix(mut stack: Vec<Slot>, ops: &[OpCode]) -> Option<(Vec<Slot>, usize)> {
    for (idx, &op) in ops.iter().enumerate() {
        let byte = op as u8;
        if byte == OpCode::PUSH0 as u8
            || (OpCode::PUSH1 as u8..=OpCode::PUSH32 as u8).contains(&byte)
        {
            stack.insert(0, Slot::Pushed);
        } else if (OpCode::DUP1 as u8..=OpCode::DUP16 as u8).contains(&byte) {
            let depth = usize::from(byte - OpCode::DUP1 as u8) + 1;
            let word = stack.get(depth - 1)?.clone();
            stack.insert(0, word);
        } else if (OpCode::SWAP1 as u8..=OpCode::SWAP16 as u8).contains(&byte) {
            let depth = usize::from(byte - OpCode::SWAP1 as u8) + 1;
            if stack.len() <= depth {
                return None;
            }
            stack.swap(0, depth);
        } else if byte == OpCode::POP as u8 {
            if stack.is_empty() {
                return None;
            }
            stack.remove(0);
        } else if byte == OpCode::NOT as u8 && stack.first() == Some(&Slot::Pushed) {
        } else {
            return Some((stack, idx));
        }
    }
    Some((stack, ops.len()))
}

/// What the replay checked in one fixture.
#[derive(Default, Debug)]
struct ReplayStats {
    groups: usize,
    prefix_replays: usize,
    next_stack_checks: usize,
}

/// For every machine instruction that emits opcodes in `source`, compares its plan with the
/// opcodes that the backend lowers it to. This is a structural check, not a comparison with
/// executed code.
///
/// Three things are asserted, each of which holds by construction:
///
/// 1. Every instruction that emits an opcode has a plan record.
/// 2. The leading stack opcodes of an instruction apply to its planned stack without needing a
///    word below it. The planned stack is the whole of the function's own stack, so a `DUP` or
///    `SWAP` that reached below it would show a plan that omits a word.
/// 3. When an instruction is a prefix of stack opcodes followed by one operation opcode, and the
///    next instruction of the block follows directly, the next instruction's planned stack is the
///    instruction's results on top of what the prefix left below the operands. That is, once the
///    results are removed from the top of the next stack, what remains is the bottom of the stack
///    after the prefix. Instructions with more than one non-stack opcode (calls, branches) and
///    instructions that are the last of their block are not compared.
fn replay_source(name: &str, source: &str) -> Option<ReplayStats> {
    let mut stats = ReplayStats::default();
    let parsed =
        parse_module(source).unwrap_or_else(|error| panic!("{name}: does not parse: {error:?}"));
    let module = parsed.module;
    let order: Vec<FuncRef> = parsed
        .debug
        .func_order
        .iter()
        .copied()
        .filter(|func| {
            module.ctx.declared_funcs.contains_key(func)
                && module
                    .ctx
                    .func_sig(*func, |sig| sig.linkage().has_definition())
        })
        .collect();
    let backend = o0_backend(true);
    let prepared = match backend.prepare_section(SectionWorkModule::from_roots(
        &module,
        order[0],
        &order[1..],
        &[],
    )) {
        Ok(prepared) => prepared,
        Err(error) => {
            assert_expected_error(name, source, &error);
            return None;
        }
    };

    for &func in prepared.funcs() {
        let plan = prepared.stack_plan(func).expect("plan was captured");
        let lowered = backend.lower_function(&prepared, func).expect("lowers");
        let vcode = &lowered.vcode;
        for &block in &lowered.block_order {
            // The opcodes of the block, grouped by the machine instruction that emitted them.
            let mut groups: Vec<(Option<sonatina_ir::InstId>, Vec<OpCode>)> = Vec::new();
            for insn in vcode.block_insns(block) {
                let inst = vcode.inst_ir[insn].expand();
                match groups.last_mut() {
                    Some((last, ops)) if *last == inst && inst.is_some() => {
                        ops.push(vcode.insts[insn])
                    }
                    _ => groups.push((inst, vec![vcode.insts[insn]])),
                }
            }
            for (idx, (inst, ops)) in groups.iter().enumerate() {
                let Some(inst) = *inst else { continue };
                stats.groups += 1;
                let record = plan
                    .stack_before(MachineInstId(inst))
                    .unwrap_or_else(|| panic!("{name}: no plan for {inst:?} in {func:?}"));
                let Some((after_prefix, applied)) = replay_prefix(slots(record), ops) else {
                    panic!(
                        "{name}: stack opcodes of {inst:?} in {func:?} need words the plan lacks: {ops:?} on {record:?}"
                    );
                };
                stats.prefix_replays += 1;

                if ops.len() != applied + 1 {
                    continue;
                }
                let Some((Some(next), _)) = groups.get(idx + 1) else {
                    continue;
                };
                // An instruction between the two that emits no opcode may rename a value, so the
                // pair is compared only when the two are adjacent in the block.
                let adjacent = prepared.module().func_store.view(func, |function| {
                    function.layout.next_inst_of(inst) == Some(*next)
                });
                if !adjacent {
                    continue;
                }
                let Some(next_record) = plan.stack_before(MachineInstId(*next)) else {
                    continue;
                };
                let results: Vec<ValueId> = prepared
                    .module()
                    .func_store
                    .view(func, |function| function.dfg.inst_results(inst).to_vec());
                let next_slots = slots(next_record);
                assert!(
                    next_slots.len() >= results.len()
                        && next_slots[..results.len()]
                            .iter()
                            .all(|slot| matches!(slot, Slot::Value(v) if results.contains(v))),
                    "{name}: results {results:?} of {inst:?} in {func:?} are not on top of {next_record:?}"
                );
                let below = &next_slots[results.len()..];
                assert!(
                    after_prefix.len() >= below.len()
                        && after_prefix[after_prefix.len() - below.len()..]
                            .iter()
                            .zip(below)
                            .all(|(a, b)| a.same_word(b)),
                    "{name}: below the results of {inst:?} in {func:?} the next stack {next_record:?} is not the bottom of {after_prefix:?} (opcodes {ops:?})"
                );
                stats.next_stack_checks += 1;
            }
        }
    }
    Some(stats)
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm",
    glob: "*.sntn"
)]
fn plan_records_are_consistent_with_the_emitted_opcodes(fixture: Fixture<&str>) {
    if let Some(stats) = replay_source(fixture.path(), fixture.content()) {
        assert!(stats.groups > 0, "{stats:?}");
    }
}

// ---- a block with one predecessor and a phi ------------------------------

/// `%f` has a block with one predecessor and a phi. The allocator plans such a block by giving
/// its first instruction an entry shuffle, which would make that instruction's record differ
/// from the stack that the planner continues from.
const SINGLE_PREDECESSOR_PHI: &str = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = add v0 v1;
        jump block1;
    block1:
        v3.i256 = phi (v1 block0);
        v4.i256 = sub v3 v2;
        return v4;
}

func public %runtime() {
    block0:
        v0.i256 = evm_calldata_load 0.i32;
        v1.i256 = evm_calldata_load 32.i32;
        v2.i256 = call %f v0 v1;
        mstore 0.i256 v2 i256;
        evm_return 0.i256 32.i256;
}

object @Contract {
  section runtime {
    entry %runtime;
  }
}
"#;

/// The machine pipeline removes the phi of a one-predecessor block before planning, at every
/// level, so no function that `EvmCompile` plans has an entry shuffle at a block start. The
/// shuffle is reachable only by planning a function directly, which a test in the allocator does.
#[test]
fn a_phi_in_a_block_with_one_predecessor_is_removed_before_planning() {
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::Os, OptLevel::O2] {
        let parsed = parse_module(SINGLE_PREDECESSOR_PHI).expect("fixture parses");
        let has_phi = |module: &Module| {
            module.funcs().into_iter().any(|func| {
                module.func_store.view(func, |function| {
                    function.layout.iter_block().any(|block| {
                        function
                            .layout
                            .iter_inst(block)
                            .any(|inst| function.dfg.is_phi(inst))
                    })
                })
            })
        };
        assert!(has_phi(&parsed.module), "the input has the phi");

        let mut compile = Compile::new(parsed.module, EvmCompiler::default()).with_opt_level(opt);
        let module = compile.optimize();
        let runtime = func_named(module, "runtime");
        let others: Vec<FuncRef> = module
            .funcs()
            .into_iter()
            .filter(|&func| func != runtime)
            .filter(|&func| {
                module
                    .ctx
                    .func_sig(func, |sig| sig.linkage().has_definition())
            })
            .collect();
        let prepared = backend_at(opt, true)
            .prepare_section(SectionWorkModule::from_roots(module, runtime, &others, &[]))
            .expect("section prepares");

        for &func in prepared.funcs() {
            let trace = prepared.stackify_trace(func).expect("trace was captured");
            assert!(!trace.contains("prologue:"), "{opt:?}: {trace}");
            assert!(!has_phi(prepared.module()), "{opt:?}: a phi was planned");
        }
    }
}
