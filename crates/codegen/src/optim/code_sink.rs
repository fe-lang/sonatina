use rustc_hash::FxHashSet;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, Value, ValueId,
    inst::{downcast, evm},
};

use crate::{domtree::DomTree, loop_analysis::LoopTree};

#[derive(Debug, Default)]
pub struct CodeSink;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SinkPlan {
    inst: InstId,
    before: InstId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct UseSite {
    block: BlockId,
    anchor: InstId,
}

impl CodeSink {
    pub fn new() -> Self {
        Self
    }

    pub fn run(
        &mut self,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        domtree: &mut DomTree,
        lpt: &mut LoopTree,
    ) -> bool {
        cfg.compute(func);
        domtree.compute(cfg);
        lpt.compute(cfg, domtree);
        let facts = SinkFacts::compute(func, cfg);

        let mut changed = false;
        while let Some(plan) = find_sink_plan(func, cfg, domtree, lpt, &facts) {
            func.layout.remove_inst(plan.inst);
            func.layout.insert_inst_before(plan.inst, plan.before);
            changed = true;
        }

        changed
    }
}

#[derive(Debug, Default)]
struct SinkFacts {
    normal_exit_reachable: FxHashSet<BlockId>,
}

impl SinkFacts {
    fn compute(func: &Function, cfg: &ControlFlowGraph) -> Self {
        let mut facts = Self::default();
        let mut worklist = Vec::new();

        for block in func.layout.iter_block() {
            if is_normal_exit_block(func, block) {
                facts.normal_exit_reachable.insert(block);
                worklist.push(block);
            }
        }

        while let Some(block) = worklist.pop() {
            for &pred in cfg.preds_of(block) {
                if facts.normal_exit_reachable.insert(pred) {
                    worklist.push(pred);
                }
            }
        }

        facts
    }

    fn can_reach_normal_exit(&self, block: BlockId) -> bool {
        self.normal_exit_reachable.contains(&block)
    }
}

fn is_normal_exit_block(func: &Function, block: BlockId) -> bool {
    let Some(term) = func.layout.last_inst_of(block) else {
        return false;
    };
    let inst = func.dfg.inst(term);
    func.dfg.is_return(term)
        || downcast::<&evm::EvmReturn>(func.inst_set(), inst).is_some()
        || downcast::<&evm::EvmSelfDestruct>(func.inst_set(), inst).is_some()
}

fn find_sink_plan(
    func: &Function,
    cfg: &ControlFlowGraph,
    domtree: &DomTree,
    lpt: &LoopTree,
    facts: &SinkFacts,
) -> Option<SinkPlan> {
    let blocks: Vec<_> = func.layout.iter_block().collect();
    for block in blocks.into_iter().rev() {
        let insts: Vec<_> = func.layout.iter_inst(block).collect();
        for inst in insts.into_iter().rev() {
            if !func.dfg.can_speculate(inst) || func.dfg.inst_results(inst).is_empty() {
                continue;
            }
            if let Some(plan) = plan_sink_inst(func, cfg, domtree, lpt, facts, inst) {
                return Some(plan);
            }
        }
    }

    None
}

fn plan_sink_inst(
    func: &Function,
    cfg: &ControlFlowGraph,
    domtree: &DomTree,
    lpt: &LoopTree,
    facts: &SinkFacts,
    inst: InstId,
) -> Option<SinkPlan> {
    let source_block = func.layout.inst_block(inst);
    let use_sites = collect_use_sites(func, inst)?;
    let dest_block = nearest_common_dominator(domtree, use_sites.iter().map(|site| site.block))?;

    if dest_block == source_block
        || !domtree.dominates(source_block, dest_block)
        || lpt.loop_of_block(source_block) != lpt.loop_of_block(dest_block)
        || crosses_cold_guard_to_hot_continuation(cfg, domtree, facts, source_block, dest_block)
    {
        return None;
    }

    let before = insertion_anchor(func, dest_block, &use_sites)?;
    if operands_available_at(func, domtree, inst, dest_block, before) {
        Some(SinkPlan { inst, before })
    } else {
        None
    }
}

fn crosses_cold_guard_to_hot_continuation(
    cfg: &ControlFlowGraph,
    domtree: &DomTree,
    facts: &SinkFacts,
    source: BlockId,
    dest: BlockId,
) -> bool {
    if !facts.can_reach_normal_exit(dest) {
        return false;
    }

    let mut child = dest;
    while let Some(parent) = domtree.idom_of(child) {
        let succs = cfg.succs_as_slice(parent);
        if succs.len() > 1 {
            // Avoid moving work from before a guard into the normal continuation
            // when the only skipped paths are non-committing exits.
            let mut path_can_reach_normal_exit = false;
            let mut saw_off_path = false;
            let mut off_path_succs_are_cold = true;
            for &succ in succs {
                let is_path_succ = succ == child || succ == dest || domtree.dominates(succ, dest);
                if is_path_succ {
                    path_can_reach_normal_exit |= facts.can_reach_normal_exit(succ);
                } else {
                    saw_off_path = true;
                    off_path_succs_are_cold &= !facts.can_reach_normal_exit(succ);
                }
            }

            if path_can_reach_normal_exit && saw_off_path && off_path_succs_are_cold {
                return true;
            }
        }
        if parent == source {
            return false;
        }
        child = parent;
    }

    false
}

fn collect_use_sites(func: &Function, inst: InstId) -> Option<Vec<UseSite>> {
    let mut sites = Vec::new();
    for &result in func.dfg.inst_results(inst) {
        for &user in func.dfg.users(result) {
            if !func.dfg.has_inst(user) || !func.layout.is_inst_inserted(user) {
                continue;
            }
            if user == inst {
                return None;
            }

            if let Some(phi) = func.dfg.cast_phi(user) {
                for &(arg, pred) in phi.args() {
                    if arg == result {
                        let anchor = func.layout.last_inst_of(pred)?;
                        sites.push(UseSite {
                            block: pred,
                            anchor,
                        });
                    }
                }
            } else {
                sites.push(UseSite {
                    block: func.layout.inst_block(user),
                    anchor: user,
                });
            }
        }
    }

    if sites.is_empty() { None } else { Some(sites) }
}

fn nearest_common_dominator(
    domtree: &DomTree,
    mut blocks: impl Iterator<Item = BlockId>,
) -> Option<BlockId> {
    let mut common = blocks.next()?;
    for block in blocks {
        common = common_dominator(domtree, common, block)?;
    }
    Some(common)
}

fn common_dominator(domtree: &DomTree, a: BlockId, b: BlockId) -> Option<BlockId> {
    let mut ancestors = FxHashSet::default();
    let mut cursor = Some(a);
    while let Some(block) = cursor {
        ancestors.insert(block);
        cursor = domtree.idom_of(block);
    }

    let mut cursor = Some(b);
    while let Some(block) = cursor {
        if ancestors.contains(&block) {
            return Some(block);
        }
        cursor = domtree.idom_of(block);
    }

    None
}

fn insertion_anchor(func: &Function, block: BlockId, use_sites: &[UseSite]) -> Option<InstId> {
    let anchors: FxHashSet<_> = use_sites
        .iter()
        .filter(|site| site.block == block)
        .map(|site| site.anchor)
        .collect();

    if anchors.is_empty() {
        return func.layout.last_inst_of(block);
    }

    func.layout
        .iter_inst(block)
        .find(|inst| anchors.contains(inst))
}

fn operands_available_at(
    func: &Function,
    domtree: &DomTree,
    inst: InstId,
    block: BlockId,
    before: InstId,
) -> bool {
    let mut available = true;
    func.dfg.inst(inst).for_each_value(&mut |value| {
        available &= value_available_at(func, domtree, inst, value, block, before);
    });
    available
}

fn value_available_at(
    func: &Function,
    domtree: &DomTree,
    moving_inst: InstId,
    value: ValueId,
    block: BlockId,
    before: InstId,
) -> bool {
    match func.dfg.value(value) {
        Value::Inst { inst, .. } => {
            if *inst == moving_inst
                || !func.dfg.has_inst(*inst)
                || !func.layout.is_inst_inserted(*inst)
            {
                return false;
            }
            let def_block = func.layout.inst_block(*inst);
            if def_block == block {
                inst_strictly_precedes(func, *inst, before)
            } else {
                domtree.dominates(def_block, block)
            }
        }
        Value::Arg { .. }
        | Value::Immediate { .. }
        | Value::Global { .. }
        | Value::Undef { .. } => true,
    }
}

fn inst_strictly_precedes(func: &Function, before: InstId, after: InstId) -> bool {
    if before == after || func.layout.inst_block(before) != func.layout.inst_block(after) {
        return false;
    }

    let block = func.layout.inst_block(before);
    let mut cursor = func.layout.first_inst_of(block);
    while let Some(inst) = cursor {
        if inst == before {
            return true;
        }
        if inst == after {
            return false;
        }
        cursor = func.layout.next_inst_of(inst);
    }

    false
}
