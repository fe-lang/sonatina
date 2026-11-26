//! The operand stack plan against executed code.
//!
//! The plan of a machine instruction says what the EVM operand stack holds before the first
//! opcode of the instruction. These tests run the compiled code in REVM, record the program
//! counter and the whole stack before every opcode, and compare each step that is the first opcode
//! of an instruction with the plan of that instruction. The comparison does not depend on how
//! the allocator reached the plan, so it detects a plan that lists the right words in the wrong
//! order, which a comparison with the emitted opcodes cannot.
//!
//! What is compared at such a step, with `real` the stack of the executing frame and `plan` the
//! record, entry 0 being the top:
//!
//! - The plan is not longer than `real`.
//! - Entries above the return address are the words at the same distance from the top of
//!   `real`. Entries that name the same value hold equal words, and every sighting of one
//!   constant value in one run holds the same word.
//! - In a function that returns, the return address is the last entry. At the first record of an
//!   activation the word is a `JUMPDEST` address. For the later records of the activation the
//!   word at the listed place is that same address and the number of words below it is the same,
//!   except in a block that never returns, where the plan does not list the words that the
//!   function left on the stack and the activation must not return afterwards.
//! - No record lists a call continuation.
//! - When the test supplies the value of a label, every entry that carries the label holds that
//!   value.
//!
//! What is not compared:
//!
//! - An instruction whose PC map entries in a block are not one run, because the emitter's
//!   peephole pass moved opcodes of a neighbouring instruction between them, is not compared.
//!   The documentation of `InstStack` says why its record does not apply. The tests count these
//!   instructions.
//! - The value of a constant is not known to the test, only that one constant holds one word.
//! - Two fixtures are excluded or relaxed for the reasons given at their lists below.
//!
//! Fixtures with `evm.case` directives run at optimization level 0, the level for which the plans
//! are meant. The hand-written functions at the end label specific values whose run-time values
//! are known.

use std::collections::{HashMap, HashSet};

use dir_test::{Fixture, dir_test};
use revm::{
    EvmContext, Inspector,
    interpreter::Interpreter,
    primitives::{ExecutionResult, Output, U256},
};
use sonatina_codegen::{
    EvmCompile, OptLevel,
    isa::evm::stack_plan::{InstStack, StackEntry},
    object::{MachineInstId, ObjectArtifact, PcMapUnit, SectionArtifact},
};
use sonatina_ir::{BlockId, ValueId, ValueLabel, module::FuncRef};

use super::{EvmHarness, assert_case, calldata_words, evm_directives, parse_sona};

const JUMPDEST: u8 = 0x5b;

/// The record of an instruction and the function it belongs to.
struct Located {
    func: FuncRef,
    func_name: String,
    inst: u32,
    block: BlockId,
    record: InstStack,
}

/// What the checker knows about one section: its bytes, and the record of each instruction at the
/// program counter of the instruction's first opcode.
struct SectionPlans {
    code: Vec<u8>,
    first_op: HashMap<usize, Located>,
    /// The program counter of the first instruction of each function that has a record.
    entry_pc: HashMap<FuncRef, usize>,
    /// Instructions that are not compared, because their opcodes are interleaved with another
    /// instruction's.
    interleaved: usize,
}

impl SectionPlans {
    fn new(section: &SectionArtifact) -> Self {
        let obs = section.observability.as_ref().expect("observability");
        assert!(!obs.stack_plans.is_empty(), "plans were not captured");

        // An instruction whose PC map entries are not one run, because the emitter's peephole pass
        // moved opcodes between it and its neighbours, is not described at its first opcode.
        let mut sequences: HashMap<(FuncRef, BlockId), Vec<u32>> = HashMap::new();
        for entry in &obs.pc_map {
            let (PcMapUnit::Function(func), Some(inst)) =
                (&entry.unit, entry.attribution.machine_inst())
            else {
                continue;
            };
            let sequence = sequences.entry((*func, entry.block)).or_default();
            let inst = inst.raw().as_u32();
            if sequence.last() != Some(&inst) {
                sequence.push(inst);
            }
        }
        let mut interleaved: HashSet<(FuncRef, u32)> = HashSet::new();
        for ((func, _), sequence) in &sequences {
            let mut runs: HashMap<u32, Vec<usize>> = HashMap::new();
            for (position, inst) in sequence.iter().enumerate() {
                runs.entry(*inst).or_default().push(position);
            }
            for positions in runs.values().filter(|positions| positions.len() > 1) {
                let (first, last) = (positions[0], positions[positions.len() - 1]);
                for inst in &sequence[first..=last] {
                    interleaved.insert((*func, *inst));
                }
            }
        }

        // The first opcode of an instruction is its PC map entry with the lowest program counter.
        let mut first_pc: HashMap<(FuncRef, u32), (usize, String, MachineInstId, BlockId)> =
            HashMap::new();
        for entry in &obs.pc_map {
            let PcMapUnit::Function(func) = &entry.unit else {
                continue;
            };
            let Some(inst) = entry.attribution.machine_inst() else {
                continue;
            };
            if obs.stack_before(&entry.unit, inst).is_none() {
                continue;
            }
            if interleaved.contains(&(*func, inst.raw().as_u32())) {
                continue;
            }
            let pc = entry.pc_start as usize;
            first_pc
                .entry((*func, inst.raw().as_u32()))
                .and_modify(|first| {
                    if pc < first.0 {
                        *first = (pc, entry.func_name.clone(), inst, entry.block);
                    }
                })
                .or_insert((pc, entry.func_name.clone(), inst, entry.block));
        }

        let mut first_op = HashMap::new();
        let mut entry_pc: HashMap<FuncRef, usize> = HashMap::new();
        for ((func, inst), (pc, func_name, machine_inst, block)) in first_pc {
            let unit = PcMapUnit::Function(func);
            let record = obs
                .stack_before(&unit, machine_inst)
                .expect("record exists")
                .clone();
            entry_pc
                .entry(func)
                .and_modify(|min| *min = (*min).min(pc))
                .or_insert(pc);
            let previous = first_op.insert(
                pc,
                Located {
                    func,
                    func_name,
                    inst,
                    block,
                    record,
                },
            );
            assert!(previous.is_none(), "two instructions start at pc {pc}");
        }
        let interleaved = interleaved.len();
        Self {
            code: section.bytes.clone(),
            first_op,
            entry_pc,
            interleaved,
        }
    }
}

/// One activation of a function that has a plan.
struct Frame {
    func: FuncRef,
    /// The number of words below the function's own words.
    base: usize,
    return_address: Option<U256>,
    /// A record of the activation was taken in a block that never returns, with words that the
    /// plan does not list.
    leftover: bool,
    /// The block, program counter and value words of the activation's latest record.
    latest: Option<(BlockId, usize, HashMap<ValueId, U256>)>,
}

#[derive(Default, Debug, Clone)]
struct Stats {
    /// Steps of the top-level frame.
    steps: usize,
    /// Steps that are the first opcode of an instruction with a record.
    records: usize,
    /// Stack words compared with the plan.
    words: usize,
    /// Pairs of entries of one record that name one value and were compared.
    duplicates: usize,
    /// Words of constants compared with an earlier sighting of the same constant.
    constants: usize,
    /// Return addresses compared.
    return_addresses: usize,
    /// Records of blocks that never return, for which the plan lists fewer words than are there.
    leftover_records: usize,
    /// Entries with a label whose value the test supplied.
    label_checks: usize,
    /// Values that appear in two consecutive records of one pass through a block, compared.
    pass_comparisons: usize,
    /// Transactions whose code was not the section's, and so were not compared.
    skipped_frames: usize,
    /// Instructions with a record whose first opcode can be compared.
    eligible_instructions: usize,
    /// Instructions with a record that are not compared, because their opcodes are interleaved
    /// with another instruction's.
    interleaved_instructions: usize,
}

impl Stats {
    fn add(&mut self, other: &Stats) {
        self.steps += other.steps;
        self.records += other.records;
        self.words += other.words;
        self.duplicates += other.duplicates;
        self.constants += other.constants;
        self.return_addresses += other.return_addresses;
        self.leftover_records += other.leftover_records;
        self.label_checks += other.label_checks;
        self.pass_comparisons += other.pass_comparisons;
        self.skipped_frames += other.skipped_frames;
        self.eligible_instructions += other.eligible_instructions;
        self.interleaved_instructions += other.interleaved_instructions;
    }
}

/// The inspector: compares the stack before each opcode with the plan.
struct Checker<'a> {
    plans: &'a SectionPlans,
    /// The value of each label for this run, when the test knows it.
    label_words: &'a HashMap<u32, U256>,
    top_depth: Option<u64>,
    enabled: bool,
    frames: Vec<Frame>,
    constants: HashMap<(FuncRef, ValueId), U256>,
    observed_labels: HashSet<u32>,
    stats: Stats,
    failures: Vec<String>,
}

impl<'a> Checker<'a> {
    fn new(plans: &'a SectionPlans, label_words: &'a HashMap<u32, U256>) -> Self {
        Self {
            plans,
            label_words,
            top_depth: None,
            enabled: false,
            frames: Vec::new(),
            constants: HashMap::new(),
            observed_labels: HashSet::new(),
            stats: Stats::default(),
            failures: Vec::new(),
        }
    }

    fn fail(&mut self, at: &Located, pc: usize, real: &[U256], message: String) {
        if self.failures.len() >= 8 {
            return;
        }
        let top: Vec<String> = real
            .iter()
            .rev()
            .take(8)
            .map(|w| format!("{w:#x}"))
            .collect();
        self.failures.push(format!(
            "{message}\n  function `{}` instruction {} at pc {pc}\n  plan: {:?}\n  real stack ({} words), top first: {top:?}",
            at.func_name,
            at.inst,
            at.record.stack,
            real.len(),
        ));
    }

    fn pop_frames_above(&mut self, index: usize, at: &Located, pc: usize, real: &[U256]) {
        while self.frames.len() > index + 1 {
            let frame = self.frames.pop().expect("frame");
            if frame.leftover {
                self.fail(
                    at,
                    pc,
                    real,
                    format!(
                        "an activation of {:?} returned after a record that was taken in a block that never returns",
                        frame.func
                    ),
                );
            }
        }
    }

    fn check(&mut self, pc: usize, at: &Located, real: &[U256]) {
        let plan = &at.record.stack;
        let len = plan.len();
        let n = real.len();
        self.stats.records += 1;
        if len > n {
            self.fail(
                at,
                pc,
                real,
                format!("the plan has {len} entries but the stack has {n} words"),
            );
            return;
        }
        let word = |i: usize| real[n - 1 - i];

        let return_index = plan
            .iter()
            .position(|entry| matches!(entry, StackEntry::ReturnAddress));
        if let Some(index) = return_index
            && index + 1 != len
        {
            self.fail(
                at,
                pc,
                real,
                "the return address is not the last entry".to_string(),
            );
        }
        let above = return_index.unwrap_or(len);

        let mut seen: HashMap<ValueId, U256> = HashMap::new();
        for (i, entry) in plan.iter().take(above).enumerate() {
            self.stats.words += 1;
            let value = match entry {
                StackEntry::Value(value) => value,
                other => {
                    self.fail(at, pc, real, format!("entry {i} is {other:?}"));
                    continue;
                }
            };
            match seen.get(&value.value) {
                Some(&earlier) => {
                    self.stats.duplicates += 1;
                    if earlier != word(i) {
                        self.fail(
                            at,
                            pc,
                            real,
                            format!(
                                "{:?} is listed twice with different words {earlier:#x} and {:#x}",
                                value.value,
                                word(i)
                            ),
                        );
                    }
                }
                None => {
                    seen.insert(value.value, word(i));
                }
            }
            if value.constant {
                self.stats.constants += 1;
                match self.constants.get(&(at.func, value.value)) {
                    Some(&earlier) if earlier != word(i) => self.fail(
                        at,
                        pc,
                        real,
                        format!(
                            "the constant {:?} held {earlier:#x} before and holds {:#x} now",
                            value.value,
                            word(i)
                        ),
                    ),
                    Some(_) => {}
                    None => {
                        self.constants.insert((at.func, value.value), word(i));
                    }
                }
            }
            for label in &value.labels {
                self.observed_labels.insert(label.0);
                if let Some(&expected) = self.label_words.get(&label.0) {
                    self.stats.label_checks += 1;
                    if expected != word(i) {
                        self.fail(
                            at,
                            pc,
                            real,
                            format!(
                                "label {} at entry {i} should be {expected:#x} and the stack holds {:#x}",
                                label.0,
                                word(i)
                            ),
                        );
                    }
                }
            }
        }

        let Some(frame) = self.track_activation(pc, at, real, return_index.map(|_| n - len), len)
        else {
            return;
        };

        // A value is one word for as long as it is defined. Two records of one frame that are
        // taken in one pass through a block (the second at a higher program counter) must
        // show every value that they share as the same word.
        let latest = self.frames[frame].latest.take();
        if let Some((block, earlier_pc, earlier)) = latest
            && block == at.block
            && earlier_pc < pc
        {
            for (value, word) in &seen {
                if let Some(earlier_word) = earlier.get(value) {
                    self.stats.pass_comparisons += 1;
                    if earlier_word != word {
                        self.fail(
                            at,
                            pc,
                            real,
                            format!(
                                "{value:?} held {earlier_word:#x} at pc {earlier_pc} of the same pass and holds {word:#x} here"
                            ),
                        );
                    }
                }
            }
        }
        self.frames[frame].latest = Some((at.block, pc, seen));
    }

    /// Follows the activations of functions, to compare the words below the listed ones.
    fn track_activation(
        &mut self,
        pc: usize,
        at: &Located,
        real: &[U256],
        return_slot: Option<usize>,
        len: usize,
    ) -> Option<usize> {
        let base = real.len() - len;
        let return_address = return_slot.map(|slot| real[slot]);

        if self.plans.entry_pc.get(&at.func) == Some(&pc) {
            if let Some(address) = return_address {
                self.stats.return_addresses += 1;
                let valid = usize::try_from(address)
                    .ok()
                    .and_then(|address| self.plans.code.get(address))
                    == Some(&JUMPDEST);
                if !valid {
                    self.fail(
                        at,
                        pc,
                        real,
                        format!("the return address {address:#x} is not a JUMPDEST"),
                    );
                }
            }
            self.frames.push(Frame {
                func: at.func,
                base,
                return_address,
                leftover: false,
                latest: None,
            });
            return Some(self.frames.len() - 1);
        }

        if let Some(index) = self
            .frames
            .iter()
            .rposition(|frame| frame.func == at.func && frame.base == base)
        {
            self.pop_frames_above(index, at, pc, real);
            if let Some(address) = return_address {
                self.stats.return_addresses += 1;
                if self.frames[index].return_address != Some(address) {
                    self.fail(
                        at,
                        pc,
                        real,
                        format!("the return address at the listed place is {address:#x}, not the activation's"),
                    );
                }
            }
            return Some(index);
        }

        if let Some(index) = self
            .frames
            .iter()
            .rposition(|frame| frame.func == at.func && frame.base < base)
        {
            self.pop_frames_above(index, at, pc, real);
            self.frames[index].leftover = true;
            self.stats.leftover_records += 1;
            return Some(index);
        }

        self.fail(
            at,
            pc,
            real,
            format!(
                "no activation of this function with {base} words below the listed ones (frames: {:?})",
                self.frames
                    .iter()
                    .map(|frame| (frame.func, frame.base))
                    .collect::<Vec<_>>()
            ),
        );
        None
    }

    /// Panics with the failures, if any.
    fn finish(self, name: &str, what: &str) -> Stats {
        assert!(
            self.failures.is_empty(),
            "{name}: {what}: the stack plan disagrees with the executed stack:\n{}",
            self.failures.join("\n")
        );
        self.stats
    }
}

impl<DB: revm::Database> Inspector<DB> for Checker<'_> {
    fn initialize_interp(&mut self, interp: &mut Interpreter, context: &mut EvmContext<DB>) {
        if self.top_depth.is_none() {
            self.top_depth = Some(context.journaled_state.depth());
            self.enabled = interp.contract.bytecode.original_byte_slice() == self.plans.code;
            if !self.enabled {
                self.stats.skipped_frames += 1;
            }
        }
    }

    fn step(&mut self, interp: &mut Interpreter, context: &mut EvmContext<DB>) {
        if !self.enabled || Some(context.journaled_state.depth()) != self.top_depth {
            return;
        }
        self.stats.steps += 1;
        let plans = self.plans;
        let pc = interp.program_counter();
        if let Some(at) = plans.first_op.get(&pc) {
            self.check(pc, at, interp.stack().data());
        }
    }
}

fn section<'a>(artifact: &'a ObjectArtifact, name: &str) -> Option<&'a SectionArtifact> {
    artifact
        .sections
        .iter()
        .find(|(section, _)| section.0.as_str() == name)
        .map(|(_, section)| section)
}

fn compile_with_plans(name: &str, module: sonatina_ir::Module) -> Vec<ObjectArtifact> {
    EvmCompile::new(module)
        .with_opt_level(OptLevel::O0)
        .with_observability(true)
        .with_stack_plans(true)
        .compile()
        .unwrap_or_else(|errors| panic!("{name}: does not compile: {errors:?}"))
}

/// Fixtures whose entry function is also called from inside the section. The plan of that
/// function lists a return address, which the activation that the section starts does not have.
const SECTION_ENTRY_ALSO_CALLED: &[&str] = &["heap_malloc_free_ptr_entry_reentry.sntn"];

/// Fixtures whose expected result depends on the optimization pipeline of their `evm.opt`
/// directive (a measurement of gas). They run at level 0 for the plan check only.
const RESULT_DEPENDS_ON_LEVEL: &[&str] = &["black_box_gas_measurement.sntn"];

/// Runs the `evm.case` directives of a fixture at level 0 with plans captured and compares every
/// step that starts an instruction with its plan. Returns `None` for a fixture that has no cases
/// or is meant to fail compiling.
fn check_fixture(name: &str, source: &str) -> Option<Stats> {
    let parsed = parse_sona(source);
    let cases = evm_directives::parse_evm_cases(&parsed.debug.module_comments)
        .unwrap_or_else(|error| panic!("{name}: {error}"));
    let expects_error = evm_directives::parse_evm_error(&parsed.debug.module_comments)
        .unwrap_or_else(|error| panic!("{name}: {error}"))
        .is_some();
    if cases.is_empty()
        || expects_error
        || SECTION_ENTRY_ALSO_CALLED
            .iter()
            .any(|file| name.ends_with(file))
    {
        return None;
    }

    let artifacts = compile_with_plans(name, parsed.module);
    let artifact = artifacts
        .iter()
        .find(|artifact| artifact.object.0.as_str() == "Contract")
        .unwrap_or_else(|| panic!("{name}: missing `Contract` object"));
    let runtime = section(artifact, "runtime").unwrap_or_else(|| panic!("{name}: no runtime"));
    let runtime_plans = SectionPlans::new(runtime);
    let no_labels = HashMap::new();

    let mut total = Stats::default();
    total.eligible_instructions += runtime_plans.first_op.len();
    total.interleaved_instructions += runtime_plans.interleaved;
    let mut harness = match section(artifact, "init") {
        Some(init) => {
            let init_plans = SectionPlans::new(init);
            total.eligible_instructions += init_plans.first_op.len();
            total.interleaved_instructions += init_plans.interleaved;
            let checker = Checker::new(&init_plans, &no_labels);
            let (res, checker, harness) = EvmHarness::deploy_with_inspector(&init.bytes, checker);
            assert!(
                matches!(res, ExecutionResult::Success { .. }),
                "{name}: deployment failed: {res:?}"
            );
            total.add(&checker.finish(name, "deployment"));
            harness
        }
        None => EvmHarness::from_runtime(&runtime.bytes),
    };

    for case in &cases {
        let checker = Checker::new(&runtime_plans, &no_labels);
        let (res, checker) = harness.call_with_inspector(&case.calldata, checker);
        if !RESULT_DEPENDS_ON_LEVEL
            .iter()
            .any(|file| name.ends_with(file))
        {
            assert_case(case, &res, name);
        }
        total.add(&checker.finish(name, &format!("case `{}`", case.name)));
    }
    Some(total)
}

fn record_stats(name: &str, stats: &Stats) {
    // The comparison is not vacuous.
    assert!(stats.records > 0, "{name}: no step was compared: {stats:?}");
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm",
    glob: "*.sntn"
)]
fn stack_plans_match_execution_of_evm_fixtures(fixture: Fixture<&str>) {
    if let Some(stats) = check_fixture(fixture.path(), fixture.content()) {
        record_stats(fixture.path(), &stats);
    }
}

#[dir_test(
    dir: "$CARGO_MANIFEST_DIR/test_files/evm_execution",
    glob: "*.sntn"
)]
fn stack_plans_match_execution_of_evm_execution_fixtures(fixture: Fixture<&str>) {
    let stats = check_fixture(fixture.path(), fixture.content())
        .unwrap_or_else(|| panic!("{}: has no evm.case directives", fixture.path()));
    record_stats(fixture.path(), &stats);
}

// ---- values whose run-time values are known ------------------------------

/// A run of a hand-written function: the calldata words, the expected return word, and the value
/// that each label has in the run.
struct Run {
    calldata: [u64; 2],
    returns: u64,
    labels: Vec<(u32, u64)>,
}

/// Labels the named values of `source`, runs each of `runs` with the plans captured, and asserts
/// that wherever a plan lists a label the real word at that place is the label's value in the
/// run. Every label that a run supplies must be listed by some plan during the run.
fn check_labelled(name: &str, source: &str, labelled: &[(&str, &str, u32)], runs: &[Run]) -> Stats {
    let parsed = parse_sona(source);
    for &(func, value, label) in labelled {
        let func = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&f| parsed.module.ctx.func_sig(f, |sig| sig.name() == func))
            .unwrap_or_else(|| panic!("{name}: no function `{func}`"));
        let value = parsed
            .debug
            .value(func, value)
            .unwrap_or_else(|| panic!("{name}: no value `{value}`"));
        parsed.module.func_store.modify(func, |function| {
            function.dfg.add_value_label(value, ValueLabel(label));
        });
    }

    let artifacts = compile_with_plans(name, parsed.module);
    let artifact = &artifacts[0];
    let runtime = section(artifact, "runtime").expect("runtime section");
    let plans = SectionPlans::new(runtime);

    let mut total = Stats::default();
    for (idx, run) in runs.iter().enumerate() {
        let label_words: HashMap<u32, U256> = run
            .labels
            .iter()
            .map(|&(label, value)| (label, U256::from(value)))
            .collect();
        let checker = Checker::new(&plans, &label_words);
        let mut harness = EvmHarness::from_runtime(&runtime.bytes);
        let (res, checker) = harness.call_with_inspector(&calldata_words(&run.calldata), checker);
        let ExecutionResult::Success {
            output: Output::Call(output),
            ..
        } = &res
        else {
            panic!("{name} run {idx}: unexpected result {res:?}");
        };
        assert_eq!(
            output.as_ref(),
            calldata_words(&[run.returns]).as_slice(),
            "{name} run {idx}: wrong result"
        );
        let missing: Vec<u32> = label_words
            .keys()
            .copied()
            .filter(|label| !checker.observed_labels.contains(label))
            .collect();
        assert!(
            missing.is_empty(),
            "{name} run {idx}: labels {missing:?} were never listed by a plan\n{}",
            runtime
                .observability
                .as_ref()
                .expect("observability")
                .to_text()
        );
        total.add(&checker.finish(name, &format!("run {idx}")));
    }
    total
}

/// Values with several uses, so the allocator duplicates and reorders them.
const ARITHMETIC: &str = r#"
target = "evm-ethereum-osaka"

func public %runtime() {
    block0:
        v0.i256 = evm_calldata_load 0.i32;
        v1.i256 = evm_calldata_load 32.i32;
        v2.i256 = add v0 v1;
        v3.i256 = mul v2 v0;
        v4.i256 = sub v3 v1;
        v5.i256 = add v4 v2;
        mstore 0.i256 v5 i256;
        evm_return 0.i256 32.i256;
}

object @Contract {
  section runtime {
    entry %runtime;
  }
}
"#;

#[test]
fn labelled_arithmetic_values_are_where_the_plan_lists_them() {
    // a = 7, b = 5: sum 12, product 84, difference 79, total 91.
    let stats = check_labelled(
        "arithmetic",
        ARITHMETIC,
        &[
            ("runtime", "v0", 1),
            ("runtime", "v1", 2),
            ("runtime", "v2", 3),
            ("runtime", "v3", 4),
            ("runtime", "v4", 5),
            ("runtime", "v5", 6),
        ],
        &[Run {
            calldata: [7, 5],
            returns: 91,
            labels: vec![(1, 7), (2, 5), (3, 12), (4, 84), (5, 79), (6, 91)],
        }],
    );
    assert!(stats.label_checks >= 6, "{stats:?}");
}

/// A call: the callee's plan lists the callee's own words above the return address.
const CALL: &str = r#"
target = "evm-ethereum-osaka"

func private %combine(v0.i256, v1.i256) -> i256 {
    block0:
        v2.i256 = mul v0 v1;
        v3.i256 = add v2 v0;
        v4.i256 = sub v3 v1;
        return v4;
}

func public %runtime() {
    block0:
        v0.i256 = evm_calldata_load 0.i32;
        v1.i256 = evm_calldata_load 32.i32;
        v2.i256 = call %combine v0 v1;
        v3.i256 = add v2 v0;
        mstore 0.i256 v3 i256;
        evm_return 0.i256 32.i256;
}

object @Contract {
  section runtime {
    entry %runtime;
  }
}
"#;

#[test]
fn labelled_values_of_a_callee_and_its_caller_are_where_the_plans_list_them() {
    // a = 7, b = 5: the callee computes 35, 42 and 37, and the caller adds a: 44.
    let stats = check_labelled(
        "call",
        CALL,
        &[
            ("combine", "v0", 11),
            ("combine", "v1", 12),
            ("combine", "v2", 13),
            ("combine", "v3", 14),
            ("combine", "v4", 15),
            ("runtime", "v0", 21),
            ("runtime", "v1", 22),
            ("runtime", "v2", 23),
            ("runtime", "v3", 24),
        ],
        &[Run {
            calldata: [7, 5],
            returns: 44,
            labels: vec![
                (11, 7),
                (12, 5),
                (13, 35),
                (14, 42),
                (15, 37),
                (21, 7),
                (22, 5),
                (23, 37),
                (24, 44),
            ],
        }],
    );
    assert!(stats.label_checks >= 9, "{stats:?}");
    assert!(stats.return_addresses > 0, "{stats:?}");
}

/// A branch and a phi at a block with two predecessors.
const BRANCH: &str = r#"
target = "evm-ethereum-osaka"

func public %runtime() {
    block0:
        v0.i256 = evm_calldata_load 0.i32;
        v1.i256 = evm_calldata_load 32.i32;
        v2.i1 = lt v0 v1;
        br v2 block1 block2;
    block1:
        v3.i256 = sub v1 v0;
        jump block3;
    block2:
        v4.i256 = sub v0 v1;
        jump block3;
    block3:
        v5.i256 = phi (v3 block1) (v4 block2);
        v6.i256 = mul v5 v5;
        v7.i256 = add v6 v0;
        mstore 0.i256 v7 i256;
        evm_return 0.i256 32.i256;
}

object @Contract {
  section runtime {
    entry %runtime;
  }
}
"#;

#[test]
fn labelled_values_across_a_branch_and_a_phi_are_where_the_plans_list_them() {
    let labelled = [
        ("runtime", "v0", 1),
        ("runtime", "v1", 2),
        ("runtime", "v3", 3),
        ("runtime", "v4", 4),
        ("runtime", "v5", 5),
        ("runtime", "v6", 6),
        ("runtime", "v7", 7),
    ];
    let stats = check_labelled(
        "branch",
        BRANCH,
        &labelled,
        &[
            // a = 7, b = 5: a is not below b, so block2 computes 2, then 4 and 11. The difference
            // (label 4) is the phi input; its jump emits no opcode, so no step lists it.
            Run {
                calldata: [7, 5],
                returns: 11,
                labels: vec![(1, 7), (2, 5), (5, 2), (6, 4), (7, 11)],
            },
            // a = 3, b = 10: block1 computes 7, then 49 and 52.
            Run {
                calldata: [3, 10],
                returns: 52,
                labels: vec![(1, 3), (2, 10), (3, 7), (5, 7), (6, 49), (7, 52)],
            },
        ],
    );
    assert!(stats.label_checks >= 12, "{stats:?}");
}
