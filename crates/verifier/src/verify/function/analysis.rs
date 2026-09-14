use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::BlockId;

pub(super) fn compute_reachable(
    entry: BlockId,
    succs: &FxHashMap<BlockId, Vec<BlockId>>,
) -> FxHashSet<BlockId> {
    let mut seen = FxHashSet::default();
    let mut queue = VecDeque::new();

    seen.insert(entry);
    queue.push_back(entry);

    while let Some(block) = queue.pop_front() {
        let mut targets = succs.get(&block).cloned().unwrap_or_default();
        targets.sort_by_key(|b| b.as_u32());

        for target in targets {
            if seen.insert(target) {
                queue.push_back(target);
            }
        }
    }

    seen
}

/// Verification uses a virtual entry for disconnected code. Its edges reach
/// every block of each source SCC: a DAG starts at its source blocks, while a
/// closed source cycle has no privileged first block. Dead-to-live edges are
/// excluded so unreachable code cannot change executable dominance or proofs.
#[derive(Default)]
pub(super) struct AnalysisCfg {
    pub blocks: Vec<BlockId>,
    pub entries: FxHashSet<BlockId>,
    pub preds: FxHashMap<BlockId, Vec<BlockId>>,
    pub succs: FxHashMap<BlockId, Vec<BlockId>>,
}

impl AnalysisCfg {
    pub fn new(
        entry: Option<BlockId>,
        blocks: &[BlockId],
        succs: &FxHashMap<BlockId, Vec<BlockId>>,
        reachable: &FxHashSet<BlockId>,
    ) -> Self {
        let nodes: FxHashSet<_> = blocks.iter().copied().collect();
        let mut cfg = Self {
            blocks: blocks.to_vec(),
            ..Self::default()
        };
        for &block in blocks {
            for &succ in succs.get(&block).into_iter().flatten() {
                if nodes.contains(&succ)
                    && (reachable.contains(&block) || !reachable.contains(&succ))
                {
                    cfg.succs.entry(block).or_default().push(succ);
                    cfg.preds.entry(succ).or_default().push(block);
                }
            }
        }
        cfg.entries
            .extend(entry.filter(|entry| nodes.contains(entry)));
        let dead: FxHashSet<_> = nodes.difference(reachable).copied().collect();
        let order = postorder(blocks, &dead, &cfg.succs);
        let mut component = FxHashMap::default();
        for block in order.into_iter().rev() {
            if component.contains_key(&block) {
                continue;
            }
            let mut pending = vec![block];
            component.insert(block, block);
            while let Some(node) = pending.pop() {
                for &pred in cfg.preds.get(&node).into_iter().flatten() {
                    if dead.contains(&pred) && !component.contains_key(&pred) {
                        component.insert(pred, block);
                        pending.push(pred);
                    }
                }
            }
        }
        let mut non_sources = FxHashSet::default();
        for (&block, &source) in &component {
            for succ in cfg.succs.get(&block).into_iter().flatten() {
                if let Some(&target) = component.get(succ)
                    && target != source
                {
                    non_sources.insert(target);
                }
            }
        }
        cfg.entries.extend(
            component
                .iter()
                .filter_map(|(&block, source)| (!non_sources.contains(source)).then_some(block)),
        );
        cfg
    }
}

fn postorder(
    roots: &[BlockId],
    nodes: &FxHashSet<BlockId>,
    succs: &FxHashMap<BlockId, Vec<BlockId>>,
) -> Vec<BlockId> {
    let mut order = Vec::new();
    let mut seen = FxHashSet::default();
    for &root in roots {
        let mut pending = vec![(root, false)];
        while let Some((block, expanded)) = pending.pop() {
            if !nodes.contains(&block) {
                continue;
            }
            if expanded {
                order.push(block);
                continue;
            }
            if !seen.insert(block) {
                continue;
            }
            pending.push((block, true));
            pending.extend(
                succs
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .map(|&succ| (succ, false)),
            );
        }
    }
    order
}

pub(super) fn compute_idom(
    cfg: &AnalysisCfg,
    nodes: &FxHashSet<BlockId>,
) -> FxHashMap<BlockId, BlockId> {
    let roots: Vec<_> = cfg
        .blocks
        .iter()
        .copied()
        .filter(|b| cfg.entries.contains(b))
        .collect();
    let mut rpo = postorder(&roots, nodes, &cfg.succs);
    rpo.reverse();
    // Index zero is an internal virtual entry, never an IR entity.
    let index: FxHashMap<_, _> = rpo.iter().enumerate().map(|(i, &b)| (b, i + 1)).collect();
    let mut parents = vec![None; rpo.len() + 1];
    parents[0] = Some(0);
    let mut changed = true;
    while changed {
        changed = false;
        for &block in &rpo {
            let next = if cfg.entries.contains(&block) {
                Some(0)
            } else {
                cfg.preds
                    .get(&block)
                    .into_iter()
                    .flatten()
                    .filter_map(|p| index.get(p).copied())
                    .filter(|&p| parents[p].is_some())
                    .reduce(|mut lhs, mut rhs| {
                        while lhs != rhs {
                            if lhs > rhs {
                                lhs = parents[lhs].expect("known dominator");
                            } else {
                                rhs = parents[rhs].expect("known dominator");
                            }
                        }
                        lhs
                    })
            };
            let slot = &mut parents[index[&block]];
            if *slot != next {
                *slot = next;
                changed = true;
            }
        }
    }
    rpo.iter()
        .filter_map(|&block| {
            parents[index[&block]]
                .map(|parent| (block, if parent == 0 { block } else { rpo[parent - 1] }))
        })
        .collect()
}

pub(super) fn dominates(
    dom: BlockId,
    block: BlockId,
    idom: &FxHashMap<BlockId, BlockId>,
    block_order: &FxHashMap<BlockId, usize>,
) -> bool {
    if dom == block {
        return true;
    }

    let mut current = block;
    let mut steps = 0usize;
    let step_limit = block_order.len().saturating_add(1);
    while let Some(parent) = idom.get(&current).copied() {
        if parent == dom {
            return true;
        }
        if parent == current {
            return false;
        }
        current = parent;
        steps += 1;
        if steps > step_limit {
            break;
        }
    }

    false
}
