use std::collections::BTreeSet;

use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, ControlFlowGraph, Function};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode},
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
};

/// Establishes the edge preconditions of the stackify allocator (`stackalloc::stackify`).
///
/// It runs [`CriticalEdgeSplitter`] and, in addition, splits every *multiway* edge whose target
/// is planned no later than the branching block itself.
///
/// Stackify plans blocks in dominator-tree RPO, threading a symbolic stack forward, and marks a
/// block planned before simulating its terminator. A multiway terminator whose target is a block
/// already planned at that point (a retreating edge in planning order: a self-loop, or a backedge
/// into a dominating block such as a multiway self-loop on the entry block) would have to fix up
/// the stack into an already-planned block, which the planner cannot express — it either asserts
/// or silently drops the fixup. Splitting the edge inserts a single-jump block that carries the
/// fixup instead.
///
/// Forward multiway edges — the common in-loop conditional branch, whose target is planned after
/// the branch — are handled by the planner directly and are deliberately left intact, so block
/// layout (and emitted bytecode) is unchanged for functions without a retreating multiway edge.
pub struct StackifyEdgeSplitter;

impl StackifyEdgeSplitter {
    pub fn run(func: &mut Function, cfg: &mut ControlFlowGraph) {
        CriticalEdgeSplitter::new().run(func, cfg);

        // Rank reachable blocks by stackify's planning order (dominator-tree RPO).
        let mut dom = DomTree::new();
        dom.compute(cfg);
        let mut plan_rank: SecondaryMap<BlockId, Option<u32>> = SecondaryMap::default();
        for (rank, &block) in dom.rpo().iter().enumerate() {
            plan_rank[block] = Some(rank as u32);
        }

        let mut edges = BTreeSet::<(BlockId, BlockId)>::new();
        for from in func.layout.iter_block() {
            if cfg.succ_num_of(from) < 2 {
                continue;
            }
            let Some(from_rank) = plan_rank[from] else {
                continue;
            };
            for &to in cfg.succs_of(from) {
                // Retreating edge: `to` is planned before (backedge) or together with (self-loop)
                // `from`, so `to` is already planned when `from`'s terminator is simulated.
                if plan_rank[to].is_some_and(|to_rank| to_rank <= from_rank) {
                    edges.insert((from, to));
                }
            }
        }

        if edges.is_empty() {
            return;
        }

        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        for (from, to) in edges {
            editor.split_edge(from, to);
        }
        cfg.compute(editor.func());
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::cfg::ControlFlowGraph;
    use sonatina_parser::parse_module;

    use super::StackifyEdgeSplitter;

    #[test]
    fn splits_multiway_self_loop_edge() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1) {
block0:
    br v0 block0 block1;

block1:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func = parsed.module.funcs()[0];

        parsed.module.func_store.modify(func, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            let entry = cfg.entry().expect("missing entry");
            assert!(cfg.succs_of(entry).any(|&succ| succ == entry));

            StackifyEdgeSplitter::run(function, &mut cfg);

            // The split block must not displace the entry: stackify plans the entry first, so a
            // split block inserted before it would reintroduce a multiway edge into an
            // already-planned block.
            assert_eq!(cfg.entry(), Some(entry));
            assert!(!cfg.succs_of(entry).any(|&succ| succ == entry));
            assert!(cfg.preds_of(entry).any(|&pred| cfg.succ_num_of(pred) == 1));
        });
    }
}
