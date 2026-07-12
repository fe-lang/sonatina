use std::collections::BTreeMap;

use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, ControlFlowGraph, Function};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode},
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
};

/// Establishes the edge preconditions of the stackify allocator (`stackalloc::stackify`).
///
/// It canonicalizes all-identical multiway terminators to jumps, runs
/// [`CriticalEdgeSplitter`], and then splits each remaining duplicate-target edge slot and every
/// *multiway* edge whose target is planned no later than the branching block itself.
///
/// Stackify plans blocks in dominator-tree RPO, threading a symbolic stack forward, and marks a
/// block planned before simulating its terminator. A multiway terminator whose target is a block
/// already planned at that point (a retreating edge in planning order: a self-loop, or a backedge
/// into a dominating block such as a multiway self-loop on the entry block) would have to fix up
/// the stack into an already-planned block, which the planner cannot express — it either asserts
/// or silently drops the fixup. Splitting the edge inserts a single-jump block that carries the
/// fixup instead.
///
/// Forward multiway edges with distinct targets — the common in-loop conditional branch, whose
/// target is planned after the branch — are handled by the planner directly and are deliberately
/// left intact, so block layout (and emitted bytecode) is unchanged for functions without a
/// retreating or duplicate-target multiway edge.
pub struct StackifyEdgeSplitter;

impl StackifyEdgeSplitter {
    pub fn run(func: &mut Function, cfg: &mut ControlFlowGraph) {
        // An all-identical multiway terminator has one semantic destination and needs no per-edge
        // stack state. Canonicalize it before classifying critical or retreating edges; duplicate
        // destinations that remain (e.g. a subset of br_table cases) do require distinct bridges.
        let redundant_terms: Vec<_> = func
            .layout
            .iter_block()
            .filter_map(|block| {
                let edge_count = cfg.succ_edges_as_slice(block).len();
                (edge_count > 1 && cfg.succ_num_of(block) == 1)
                    .then(|| (func.layout.last_inst_of(block).unwrap(), edge_count))
            })
            .collect();
        for &(term, edge_count) in &redundant_terms {
            // Retaining every edge invokes the branch instruction's canonical representation:
            // `Br` and `BrTable` both collapse an all-identical destination set to `Jump`.
            let keep_mask = vec![true; edge_count];
            func.dfg.retain_branch_edges(term, &keep_mask);
        }
        if !redundant_terms.is_empty() {
            cfg.compute(func);
        }

        CriticalEdgeSplitter::new().run(func, cfg);

        // Rank reachable blocks by stackify's planning order (dominator-tree RPO).
        let mut dom = DomTree::new();
        dom.compute(cfg);
        let mut plan_rank: SecondaryMap<BlockId, Option<u32>> = SecondaryMap::default();
        for (rank, &block) in dom.rpo().iter().enumerate() {
            plan_rank[block] = Some(rank as u32);
        }

        let mut edges = Vec::<(BlockId, BlockId, usize)>::new();
        for from in func.layout.iter_block() {
            let outgoing = cfg.succ_edges_as_slice(from);
            if outgoing.len() < 2 {
                continue;
            }
            let Some(from_rank) = plan_rank[from] else {
                continue;
            };

            let mut dest_counts = BTreeMap::<BlockId, usize>::new();
            for &edge in outgoing {
                *dest_counts.entry(cfg.edge_data(edge).to).or_default() += 1;
            }

            for &edge in outgoing {
                let edge = cfg.edge_data(edge);
                let to = edge.to;
                // Retreating edge: `to` is planned before (backedge) or together with (self-loop)
                // `from`, so `to` is already planned when `from`'s terminator is simulated.
                // Duplicate-target edge slots also need separate bridges: br_table cases can
                // reach the same block with different post-comparison symbolic stacks.
                let duplicate = dest_counts[&to] > 1;
                let retreating = plan_rank[to].is_some_and(|to_rank| to_rank <= from_rank);
                if duplicate || retreating {
                    edges.push((from, to, edge.branch_slot));
                }
            }
        }

        if edges.is_empty() {
            return;
        }

        // Preserve the old `(from, to)` bridge-creation order for distinct edges; use the branch
        // slot only to order parallel edges that previously collapsed into one operation.
        edges.sort_unstable();
        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        for (from, _, branch_slot) in edges {
            editor.split_out_edge(from, branch_slot);
        }
        cfg.clone_from(editor.cfg());
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

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

    #[test]
    fn canonicalizes_all_duplicate_self_loop_targets() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1) {
block0:
    br v0 block0 block0;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func = parsed.module.funcs()[0];

        parsed.module.func_store.modify(func, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            let entry = cfg.entry().expect("missing entry");
            assert_eq!(cfg.succ_edges_as_slice(entry).len(), 2);

            StackifyEdgeSplitter::run(function, &mut cfg);

            assert_eq!(cfg.entry(), Some(entry));
            assert_eq!(cfg.succ_edges_as_slice(entry).len(), 1);
            let term = function.layout.last_inst_of(entry).unwrap();
            let jump = function.dfg.cast_jump(term).expect("branch becomes jump");
            assert_eq!(*jump.dest(), entry);
        });
    }

    #[test]
    fn splits_duplicate_br_table_targets_per_edge_slot() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i8) {
block0:
    br_table v0 block1 (0.i8 block1) (1.i8 block2);

block1:
    return;

block2:
    return;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func = parsed.module.funcs()[0];

        parsed.module.func_store.modify(func, |function| {
            let blocks: Vec<_> = function.layout.iter_block().collect();
            let [entry, duplicate_target, other_target] = blocks.as_slice() else {
                panic!("expected three blocks");
            };
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            StackifyEdgeSplitter::run(function, &mut cfg);

            let term = function.layout.last_inst_of(*entry).unwrap();
            let dests = function.dfg.branch_info(term).unwrap().dests();
            assert_eq!(dests.len(), 3);
            assert_eq!(dests.iter().copied().collect::<BTreeSet<_>>().len(), 3);
            assert_eq!(dests[2], *other_target);
            assert!(
                dests[..2]
                    .iter()
                    .all(|&mid| { cfg.succs_of(mid).eq(std::iter::once(duplicate_target)) })
            );
            assert_eq!(cfg.pred_num_of(*duplicate_target), 2);
        });
    }
}
