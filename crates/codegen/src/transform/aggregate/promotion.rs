pub use sonatina_ir::builder::SsaBuilder;

use rustc_hash::FxHashSet;
use sonatina_ir::{
    ControlFlowGraph, Function, InstId,
    inst::{control_flow, downcast},
};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReadPrefixRequirement {
    Unconditional,
    SingleExecution,
}

/// Reads guaranteed to execute before any non-speculatable instruction. This
/// proves placement only; consumers must separately establish unchanged contents.
pub(crate) fn unconditional_read_prefix(
    func: &Function,
    requirement: ReadPrefixRequirement,
    is_read: impl Fn(InstId) -> bool,
) -> Vec<InstId> {
    let Some(mut block) = func.layout.entry_block() else {
        return Vec::new();
    };
    let mut cfg = ControlFlowGraph::new();
    if requirement == ReadPrefixRequirement::SingleExecution {
        cfg.compute(func);
        if cfg.pred_num_of(block) != 0 {
            return Vec::new();
        }
    }
    let mut reads = Vec::new();
    let mut visited = FxHashSet::default();
    'prefix: while visited.insert(block) {
        for inst in func.layout.iter_inst(block) {
            if is_read(inst) {
                reads.push(inst);
            } else if let Some(jump) =
                downcast::<&control_flow::Jump>(func.inst_set(), func.dfg.inst(inst))
            {
                // A backedge would repeat these reads after later effects.
                if requirement == ReadPrefixRequirement::SingleExecution
                    && cfg.preds_as_slice(*jump.dest()) != [block]
                {
                    break 'prefix;
                }
                block = *jump.dest();
                continue 'prefix;
            } else if !func.dfg.can_speculate(inst) {
                break 'prefix;
            }
        }
        break;
    }
    reads
}
