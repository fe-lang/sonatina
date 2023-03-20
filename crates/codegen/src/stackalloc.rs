use crate::{
    cfg::ControlFlowGraph,
    liveness::Liveness,
    loop_analysis::{Loop, LoopTree},
};
use cranelift_entity::SecondaryMap;
use sonatina_ir::Function;

mod edge_sets;
use edge_sets::EdgeSets;

pub struct StackAlloc {}

impl StackAlloc {
    pub fn compute(
        &mut self,
        _func: &Function,
        cfg: &ControlFlowGraph,
        _looptree: &LoopTree,
        _liveness: &Liveness,
    ) {
        let mut edgesets = EdgeSets::default();
        edgesets.compute(cfg);
    }
}

fn loop_depth(tree: &LoopTree, mut lp: Loop) -> u32 {
    let mut depth = 0;
    while let Some(parent) = tree.parent_loop(lp) {
        depth += 1;
        lp = parent;
    }
    depth
}

fn loops_by_depth(tree: &LoopTree) -> Vec<(Loop, u32)> {
    // This could be shorter if we used insider knowledge about the
    // implementation of LoopTree, but we'll avoid that.
    let mut depths = SecondaryMap::<Loop, u32>::new();
    for lp in tree.loops() {
        if let Some(parent) = tree.parent_loop(lp) {
            depths[lp] = depths[parent] + 1
        } else {
            depths[lp] = 0;
        }
    }
    let mut sorted = depths.iter().map(|(l, d)| (l, *d)).collect::<Vec<_>>();
    sorted.sort_by(|(_, a), (_, b)| a.cmp(b));
    sorted
}
