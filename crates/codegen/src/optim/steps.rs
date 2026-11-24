//! The steps a pass reports while it transforms a function, for the record
//! of the machine stage (`object::lowering::MachineSteps`).

use std::{collections::BTreeMap, mem};

use sonatina_ir::{Function, Module, ir_writer::FuncWriter, module::FuncRef};

use super::pipeline::Pass;
use crate::{
    analysis::func_behavior,
    isa::evm::LateCleanupProfile,
    object::lowering::{
        FuncSnap, FuncStep, FuncSummary, MachinePass, MachinePassKind, MachineStep, MachineSteps,
        StepFacts, StepKind,
    },
};

impl FuncSnap {
    pub(crate) fn capture(func_ref: FuncRef, func: &Function) -> Self {
        Self {
            func: func.ctx().func_sig(func_ref, |sig| sig.name().to_string()),
            func_ref,
            text: FuncWriter::new(func_ref, func).dump_string(),
            insts: func
                .layout
                .iter_block()
                .map(|block| func.layout.iter_inst(block).collect())
                .collect(),
        }
    }
}

/// The steps of one pass on one function.
pub(crate) struct StepLog {
    /// The function as the last step left it.
    pub(crate) snap: FuncSnap,
    /// Each step as `(kind, group, round, step)`, with `step` only if it
    /// changed the function. The rounds of a step that repeats share a group.
    pub(crate) steps: Vec<(StepKind, usize, usize, Option<FuncStep>)>,
}

impl StepLog {
    pub(crate) fn new(snap: FuncSnap) -> Self {
        Self {
            snap,
            steps: Vec::new(),
        }
    }

    /// Records, if `log` records, a step of `kind` that left `func` as it
    /// is, relying on `facts`.
    pub(crate) fn step(
        log: &mut Option<&mut Self>,
        kind: StepKind,
        func: &Function,
        facts: Option<StepFacts>,
    ) {
        let Some(log) = log else {
            return;
        };
        let (group, round) = match log.steps.last() {
            Some(&(last, group, round, _)) if last == kind && kind.repeats() => (group, round + 1),
            Some(&(_, group, ..)) => (group + 1, 0),
            None => (0, 0),
        };
        let out = FuncSnap::capture(log.snap.func_ref, func);
        let step = (out != log.snap).then(|| {
            log.snap = out.clone();
            FuncStep {
                out,
                facts: facts.unwrap_or_default(),
            }
        });
        log.steps.push((kind, group, round, step));
    }
}

/// Records the passes over a section's functions (`MachineSteps`) as they
/// run.
pub(crate) struct StepRecorder {
    lowered: Vec<FuncSnap>,
    passes: Vec<MachinePass>,
    /// Each function as the last pass left it, in the section's order.
    current: Vec<FuncSnap>,
    /// The pass running, and the function behavior it reads.
    running: Option<(MachinePassKind, Option<Vec<FuncSummary>>)>,
}

impl StepRecorder {
    /// Starts the record of `funcs` of `module` as they are.
    pub(crate) fn new(module: &Module, funcs: &[FuncRef]) -> Self {
        let lowered: Vec<_> = funcs
            .iter()
            .map(|&func| {
                module
                    .func_store
                    .view(func, |function| FuncSnap::capture(func, function))
            })
            .collect();
        Self {
            current: lowered.clone(),
            lowered,
            passes: Vec::new(),
            running: None,
        }
    }

    pub(crate) fn finish(self, profile: LateCleanupProfile) -> MachineSteps {
        MachineSteps {
            profile,
            lowered: self.lowered,
            passes: self.passes,
        }
    }

    /// Starts the pass `kind` over `module`: the log of each function, in
    /// the section's order.
    pub(crate) fn begin_pass(&mut self, module: &Module, kind: MachinePassKind) -> Vec<StepLog> {
        // The passes that read function effects, of calls in particular.
        let reads_behavior = matches!(
            kind,
            MachinePassKind::CfgCleanup
                | MachinePassKind::ScalarCanonicalize
                | MachinePassKind::Sccp
                | MachinePassKind::Gvn
                | MachinePassKind::Adce
        );
        self.running = Some((kind, reads_behavior.then(|| func_behavior::export(module))));
        mem::take(&mut self.current)
            .into_iter()
            .map(StepLog::new)
            .collect()
    }

    /// Ends the running pass with the logs of the functions, in the
    /// section's order: the steps of a group and round of every function
    /// are one step.
    pub(crate) fn end_pass(&mut self, logs: Vec<StepLog>) {
        let (kind, func_behavior) = self.running.take().expect("a pass is running");
        let mut steps = BTreeMap::<_, MachineStep>::new();
        for log in logs {
            for (step_kind, group, round, step) in log.steps {
                let merged = steps.entry((group, round)).or_insert_with(|| MachineStep {
                    kind: step_kind,
                    funcs: Vec::new(),
                });
                assert_eq!(
                    merged.kind, step_kind,
                    "{kind:?}: functions disagree on the kind of a step"
                );
                merged.funcs.extend(step);
            }
            self.current.push(log.snap);
        }
        self.passes.push(MachinePass {
            kind,
            func_behavior,
            steps: steps
                .into_values()
                .filter(|step| !step.funcs.is_empty())
                .collect(),
        });
    }

    /// Runs `run` on each of `funcs` of `module` in turn, recorded, if
    /// `recorder` records, as the pass `kind` of one step of kind `step`.
    pub(crate) fn run_pass(
        recorder: Option<&mut Self>,
        module: &Module,
        funcs: &[FuncRef],
        (kind, step): (MachinePassKind, StepKind),
        run: impl Fn(&mut Function),
    ) {
        let Some(recorder) = recorder else {
            for &func in funcs {
                module.func_store.modify(func, &run);
            }
            return;
        };
        let logs = recorder
            .begin_pass(module, kind)
            .into_iter()
            .map(|mut log| {
                module.func_store.modify(log.snap.func_ref, |function| {
                    run(function);
                    StepLog::step(&mut Some(&mut log), step, function, None);
                });
                log
            })
            .collect();
        recorder.end_pass(logs);
    }
}

impl From<Pass> for MachinePassKind {
    fn from(pass: Pass) -> Self {
        match pass {
            Pass::CfgCleanup => Self::CfgCleanup,
            Pass::BranchCanonicalize => Self::BranchCanonicalize,
            Pass::ScalarCanonicalize => Self::ScalarCanonicalize,
            Pass::KnownBitsSimplify => Self::KnownBitsSimplify,
            Pass::Sccp => Self::Sccp,
            Pass::Gvn => Self::Gvn,
            Pass::Adce => Self::Adce,
            _ => unreachable!("{pass:?} reports no steps"),
        }
    }
}
