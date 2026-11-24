//! Records the machine stage of a section (`MachineSteps`) as it runs.

use std::{collections::BTreeMap, mem};

use sonatina_ir::{Function, Module, module::FuncRef, parallel};

use super::super::LateCleanupProfile;
use crate::{
    object::lowering::{
        FuncSnap, MachinePass, MachinePassKind, MachineStep, MachineSteps, StepKind,
    },
    optim::steps::StepLog,
};

pub(crate) struct MachineRecorder {
    profile: LateCleanupProfile,
    lowered: Vec<FuncSnap>,
    passes: Vec<MachinePass>,
    /// Each function as the last pass left it, in the section's order.
    current: Vec<FuncSnap>,
}

impl MachineRecorder {
    /// Starts the record of `funcs` of `module` as lowering built them.
    pub(crate) fn new(module: &Module, funcs: &[FuncRef], profile: LateCleanupProfile) -> Self {
        let lowered: Vec<_> = funcs
            .iter()
            .map(|&func| {
                module
                    .func_store
                    .view(func, |function| FuncSnap::capture(func, function))
            })
            .collect();
        Self {
            profile,
            current: lowered.clone(),
            lowered,
            passes: Vec::new(),
        }
    }

    pub(crate) fn finish(self) -> MachineSteps {
        MachineSteps {
            profile: self.profile,
            lowered: self.lowered,
            passes: self.passes,
        }
    }

    /// Records the pass `kind`, which changed `module` to what it is, as one
    /// step of the same kind.
    pub(crate) fn record_done_pass(
        &mut self,
        module: &Module,
        kind: MachinePassKind,
        step: StepKind,
    ) {
        let logs = mem::take(&mut self.current)
            .into_iter()
            .map(|snap| {
                let mut log = StepLog::new(snap);
                module.func_store.view(log.snap.func_ref, |function| {
                    StepLog::step(&mut Some(&mut log), step, function, None)
                });
                log
            })
            .collect();
        self.push_pass(kind, logs);
    }

    /// Merges the logs of the functions, in the section's order, into the
    /// pass `kind`: the steps of a group and round of every function are one
    /// step.
    fn push_pass(&mut self, kind: MachinePassKind, logs: Vec<StepLog>) {
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
            steps: steps
                .into_values()
                .filter(|step| !step.funcs.is_empty())
                .collect(),
        });
    }
}

/// Runs `run` on each of `funcs`, in parallel for a large module, with the
/// function's step log when `recorder` records, which then records the logs
/// as the pass `kind`. Returns whether `run` reported a change.
pub(crate) fn run_machine_pass(
    module: &Module,
    funcs: &[FuncRef],
    mut recorder: Option<&mut MachineRecorder>,
    kind: MachinePassKind,
    run: impl Fn(FuncRef, &mut Function, Option<&mut StepLog>) -> bool + Sync + Send,
) -> bool {
    let logs: Vec<_> = match recorder.as_deref_mut() {
        Some(recorder) => mem::take(&mut recorder.current)
            .into_iter()
            .map(|snap| Some(StepLog::new(snap)))
            .collect(),
        None => funcs.iter().map(|_| None).collect(),
    };
    let results = parallel::map_owned(
        &module.func_store,
        funcs.iter().copied().zip(logs).collect(),
        |(func, mut log): (FuncRef, Option<StepLog>)| {
            let changed = module
                .func_store
                .modify(func, |function| run(func, function, log.as_mut()));
            (changed, log)
        },
    );
    let changed = results.iter().any(|(changed, _)| *changed);
    if let Some(recorder) = recorder {
        let logs = results.into_iter().filter_map(|(_, log)| log).collect();
        recorder.push_pass(kind, logs);
    }
    changed
}
