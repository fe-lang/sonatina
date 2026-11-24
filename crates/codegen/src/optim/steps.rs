//! The steps a pass reports while it transforms a function, for the record
//! of the machine stage (`object::lowering::MachineSteps`).

use sonatina_ir::{Function, ir_writer::FuncWriter, module::FuncRef};

use crate::object::lowering::{FuncSnap, FuncStep, StepFacts, StepKind};

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
