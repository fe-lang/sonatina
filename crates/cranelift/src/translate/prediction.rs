//! Static branch prediction for block layout.
//!
//! Cranelift emits a branch's last target right after the branch when nothing
//! else claims that place, and moves cold blocks to the end of the function.
//! With no profile, the likely paths come from what a block does (Ball and
//! Larus, "Branch Prediction for Free", 1993). Code that ends in a panic is
//! cold, and so is any arm of a loop that can reach a call its cheapest path
//! around the loop avoids. A branch then prefers its side that isn't cold, and
//! its side that stays in the loop.

use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap, HashSet},
};

use cranelift_codegen::{flowgraph, ir as clif};
use sonatina_codegen::{
    domtree::DomTree,
    loop_analysis::{Loop, LoopTree},
};
use sonatina_ir::{BlockId, ControlFlowGraph, Function, inst::control_flow};

pub(super) struct BranchPrediction {
    cold: HashSet<BlockId>,
    loops: LoopTree,
}

impl BranchPrediction {
    pub(super) fn new(function: &Function, cfg: &ControlFlowGraph) -> Self {
        let mut domtree = DomTree::new();
        domtree.compute(cfg);
        let mut loops = LoopTree::new();
        loops.compute(cfg, &domtree);

        let rpo: Vec<_> = domtree.rpo().to_vec();
        let mut cold: HashSet<_> = rpo
            .iter()
            .copied()
            .filter(|&block| ends_in_unreachable(function, block))
            .collect();
        for lp in loops.loops() {
            cold.extend(cold_arms(function, cfg, &loops, lp));
        }

        // A block whose paths all lead to cold blocks, or all come from them,
        // is cold too. The entry block runs whatever follows it, and Cranelift
        // rejects a cold entry.
        let entry = function.layout.entry_block();
        cold.retain(|&block| Some(block) != entry);
        let mut changed = true;
        while changed {
            changed = false;
            for &block in &rpo {
                if Some(block) != entry
                    && !cold.contains(&block)
                    && (all_in(cfg.succs_of(block), &cold) || all_in(cfg.preds_of(block), &cold))
                {
                    cold.insert(block);
                    changed = true;
                }
            }
        }
        Self { cold, loops }
    }

    pub(super) fn is_cold(&self, block: BlockId) -> bool {
        self.cold.contains(&block)
    }

    /// Whether a branch from `block` should put `nz`, taken when its condition
    /// holds, right after it: `z` is cold, or leaves the loop that `nz` stays
    /// in. Otherwise `z` keeps that place, the side a guard's check for a
    /// failure falls through to.
    pub(super) fn prefers_true(&self, block: BlockId, nz: BlockId, z: BlockId) -> bool {
        if self.is_cold(nz) || self.is_cold(z) {
            return self.is_cold(z) && !self.is_cold(nz);
        }
        self.loops
            .loop_of_block(block)
            .is_some_and(|lp| self.leaves(lp, z) && !self.leaves(lp, nz))
    }

    fn leaves(&self, lp: Loop, block: BlockId) -> bool {
        !self.loops.is_in_loop(block, lp)
    }
}

fn all_in<'a>(mut blocks: impl Iterator<Item = &'a BlockId>, set: &HashSet<BlockId>) -> bool {
    let mut any = false;
    let all = blocks.all(|block| {
        any = true;
        set.contains(block)
    });
    any && all
}

fn ends_in_unreachable(function: &Function, block: BlockId) -> bool {
    function.layout.last_inst_of(block).is_some_and(|inst| {
        function
            .dfg
            .downcast::<&control_flow::Unreachable>(inst)
            .is_some()
    })
}

fn has_call(function: &Function, block: BlockId) -> bool {
    function
        .layout
        .iter_inst(block)
        .any(|inst| function.dfg.is_call(inst))
}

/// The blocks of `lp` on its cheapest path around, by fewest calls and then
/// fewest instructions.
fn hot_trace(
    function: &Function,
    cfg: &ControlFlowGraph,
    loops: &LoopTree,
    lp: Loop,
) -> HashSet<BlockId> {
    let cost = |block| {
        let insts = function.layout.iter_inst(block).count();
        (usize::from(has_call(function, block)), insts)
    };
    let header = loops.loop_header(lp);
    let mut best = HashMap::from([(header, (cost(header), header))]);
    let mut queue = BinaryHeap::from([Reverse((cost(header), header))]);
    let mut latch = None;
    'search: while let Some(Reverse((reached, block))) = queue.pop() {
        if reached > best[&block].0 {
            continue;
        }
        for &succ in cfg.succs_of(block) {
            if succ == header {
                latch = Some(block);
                break 'search;
            }
            if loops.is_in_loop(succ, lp) {
                let (calls, insts) = cost(succ);
                let total = (reached.0 + calls, reached.1 + insts);
                if best.get(&succ).is_none_or(|&(known, _)| total < known) {
                    best.insert(succ, (total, block));
                    queue.push(Reverse((total, succ)));
                }
            }
        }
    }
    let mut trace = HashSet::new();
    let mut current = latch;
    while let Some(block) = current {
        trace.insert(block);
        current = (block != header).then(|| best[&block].1);
    }
    trace
}

/// The blocks of `lp` off its hot trace that can reach a call before they
/// rejoin the trace.
fn cold_arms(
    function: &Function,
    cfg: &ControlFlowGraph,
    loops: &LoopTree,
    lp: Loop,
) -> HashSet<BlockId> {
    let trace = hot_trace(function, cfg, loops, lp);
    let mut arms: HashSet<_> = loops
        .iter_blocks_post_order(cfg, lp)
        .filter(|block| !trace.contains(block) && has_call(function, *block))
        .collect();
    let mut stack: Vec<_> = arms.iter().copied().collect();
    while let Some(block) = stack.pop() {
        for &pred in cfg.preds_of(block) {
            if loops.is_in_loop(pred, lp) && !trace.contains(&pred) && arms.insert(pred) {
                stack.push(pred);
            }
        }
    }
    arms
}

/// Marks each block Cranelift's front end made for a cold block's switch or phi
/// edge cold too: one whose predecessors are all cold.
pub(super) fn propagate_cold_blocks(func: &mut clif::Function) {
    let cfg = flowgraph::ControlFlowGraph::with_function(func);
    let blocks: Vec<_> = func.layout.blocks().collect();
    let entry = func.layout.entry_block();
    let mut changed = true;
    while changed {
        changed = false;
        for &block in &blocks {
            let mut preds = cfg.pred_iter(block).peekable();
            if Some(block) != entry
                && !func.layout.is_cold(block)
                && preds.peek().is_some()
                && preds.all(|pred| func.layout.is_cold(pred.block))
            {
                func.layout.set_cold(block);
                changed = true;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use sonatina_ir::{BlockId, ControlFlowGraph};

    use super::BranchPrediction;

    /// The cold blocks of function `f`, and whether each `(block, nz, z)` branch
    /// prefers its true side.
    fn predict(body: &str, branches: &[(u32, u32, u32)]) -> (HashSet<u32>, Vec<bool>) {
        let source = format!("target = \"x86_64-unknown-native\"\n{body}");
        let module = sonatina_parser::parse_module(&source).unwrap().module;
        let func = module
            .funcs()
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == "f"))
            .unwrap();
        module.func_store.view(func, |function| {
            let mut cfg = ControlFlowGraph::default();
            cfg.compute(function);
            let prediction = BranchPrediction::new(function, &cfg);
            let cold = function
                .layout
                .iter_block()
                .filter(|&block| prediction.is_cold(block))
                .map(|block| block.0)
                .collect();
            let prefers = branches
                .iter()
                .map(|&(block, nz, z)| {
                    prediction.prefers_true(BlockId(block), BlockId(nz), BlockId(z))
                })
                .collect();
            (cold, prefers)
        })
    }

    #[test]
    fn a_panic_is_cold_and_a_guard_falls_through_past_it() {
        let (cold, prefers) = predict(
            r#"
func public %f(v0.i1, v1.i1) -> i64 {
block0:
    br v0 block1 block2;
block1:
    unreachable;
block2:
    br v1 block3 block1;
block3:
    return 1.i64;
}
"#,
            &[(0, 1, 2), (2, 3, 1)],
        );
        assert_eq!(cold, HashSet::from([1]));
        assert_eq!(prefers, [false, true]);
    }

    #[test]
    fn the_entry_block_is_never_cold() {
        let (cold, _) = predict(
            r#"
func public %f() {
block0:
    unreachable;
}
"#,
            &[],
        );
        assert!(cold.is_empty());
    }

    #[test]
    fn a_loop_arm_that_reaches_a_call_is_cold_through_to_its_rejoin() {
        // block2 starts the arm and only its successor calls. block4 is the
        // cheapest way round, and block5, the join, stays hot.
        let (cold, prefers) = predict(
            r#"
func private %g() {
block0:
    return;
}

func public %f(v0.i1, v1.i1, v2.i1) -> i64 {
block0:
    jump block1;
block1:
    br v0 block2 block4;
block2:
    v3.i1 = is_zero v1;
    br v3 block3 block5;
block3:
    call %g;
    jump block5;
block4:
    jump block5;
block5:
    br v2 block1 block6;
block6:
    return 1.i64;
}
"#,
            &[(1, 2, 4), (5, 1, 6)],
        );
        assert_eq!(cold, HashSet::from([2, 3]));
        // The arm is cold, so the branch keeps its false side next; the latch
        // stays in the loop, whose exit is the false side.
        assert_eq!(prefers, [false, true]);
    }

    #[test]
    fn a_call_every_iteration_stays_hot() {
        let (cold, _) = predict(
            r#"
func private %g() {
block0:
    return;
}

func public %f(v0.i1) -> i64 {
block0:
    jump block1;
block1:
    call %g;
    br v0 block1 block2;
block2:
    return 1.i64;
}
"#,
            &[],
        );
        assert!(cold.is_empty());
    }

    #[test]
    fn with_no_evidence_a_branch_keeps_its_false_side_next() {
        let (cold, prefers) = predict(
            r#"
func public %f(v0.i1) -> i64 {
block0:
    br v0 block1 block2;
block1:
    return 1.i64;
block2:
    return 2.i64;
}
"#,
            &[(0, 1, 2)],
        );
        assert!(cold.is_empty());
        assert_eq!(prefers, [false]);
    }
}
