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

pub(super) fn compute_idom(
    root: BlockId,
    nodes: &FxHashSet<BlockId>,
    succs: &FxHashMap<BlockId, Vec<BlockId>>,
    preds: &FxHashMap<BlockId, Vec<BlockId>>,
    block_order: &FxHashMap<BlockId, usize>,
) -> FxHashMap<BlockId, BlockId> {
    let mut rpo = compute_rpo(root, nodes, succs, block_order);
    if rpo.is_empty() {
        rpo.push(root);
    }

    let rpo_index: FxHashMap<_, _> = rpo
        .iter()
        .enumerate()
        .map(|(idx, block)| (*block, idx))
        .collect();

    let mut idom = FxHashMap::default();
    idom.insert(root, root);

    let mut changed = true;
    while changed {
        changed = false;

        for block in rpo.iter().copied().skip(1) {
            let mut pred_candidates: Vec<_> = preds
                .get(&block)
                .into_iter()
                .flatten()
                .copied()
                .filter(|pred| nodes.contains(pred) && idom.contains_key(pred))
                .collect();
            pred_candidates.sort_by_key(|pred| pred.as_u32());

            let Some(mut new_idom) = pred_candidates.first().copied() else {
                continue;
            };

            for pred in pred_candidates.into_iter().skip(1) {
                new_idom = intersect_idom(pred, new_idom, &idom, &rpo_index);
            }

            if idom.get(&block).copied() != Some(new_idom) {
                idom.insert(block, new_idom);
                changed = true;
            }
        }
    }

    idom
}

fn compute_rpo(
    root: BlockId,
    nodes: &FxHashSet<BlockId>,
    succs: &FxHashMap<BlockId, Vec<BlockId>>,
    block_order: &FxHashMap<BlockId, usize>,
) -> Vec<BlockId> {
    let mut order = Vec::new();
    let mut seen = FxHashSet::default();
    let mut stack = vec![(root, false)];

    while let Some((block, expanded)) = stack.pop() {
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

        stack.push((block, true));

        let mut children = succs.get(&block).cloned().unwrap_or_default();
        children.retain(|child| nodes.contains(child));
        children.sort_by_key(|child| {
            (
                block_order.get(child).copied().unwrap_or(usize::MAX),
                child.as_u32(),
            )
        });

        for child in children.into_iter().rev() {
            stack.push((child, false));
        }
    }

    order.reverse();
    order
}

fn intersect_idom(
    mut lhs: BlockId,
    mut rhs: BlockId,
    idom: &FxHashMap<BlockId, BlockId>,
    rpo_index: &FxHashMap<BlockId, usize>,
) -> BlockId {
    while lhs != rhs {
        while rpo_index.get(&lhs).copied().unwrap_or(usize::MAX)
            > rpo_index.get(&rhs).copied().unwrap_or(usize::MAX)
        {
            lhs = idom[&lhs];
        }

        while rpo_index.get(&rhs).copied().unwrap_or(usize::MAX)
            > rpo_index.get(&lhs).copied().unwrap_or(usize::MAX)
        {
            rhs = idom[&rhs];
        }
    }

    lhs
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
