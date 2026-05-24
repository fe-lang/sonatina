use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, Value, ValueId,
    inst::{downcast, evm},
};

use crate::{bitset::BitSet, domtree::DomTree, loop_analysis::LoopTree};

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
        let mut worklist = SinkWorklist::new(func, &facts);
        let mut use_sites = Vec::new();

        let mut changed = false;
        while let Some(inst) = worklist.pop() {
            if !func.layout.is_inst_inserted(inst) {
                continue;
            }
            let Some(plan) = plan_sink_inst(func, cfg, domtree, lpt, &facts, inst, &mut use_sites)
            else {
                continue;
            };
            requeue_operand_defs(func, &facts, plan.inst, &mut worklist);
            func.layout.remove_inst(plan.inst);
            func.layout.insert_inst_before(plan.inst, plan.before);
            changed = true;
        }

        changed
    }
}

#[derive(Debug, Default)]
struct SinkFacts {
    normal_exit_reachable: BitSet<BlockId>,
    sink_candidates: BitSet<InstId>,
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

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if func.dfg.can_speculate(inst) && !func.dfg.inst_results(inst).is_empty() {
                    facts.sink_candidates.insert(inst);
                }
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
        self.normal_exit_reachable.contains(block)
    }

    fn is_sink_candidate(&self, inst: InstId) -> bool {
        self.sink_candidates.contains(inst)
    }
}

#[derive(Debug, Default)]
struct SinkWorklist {
    insts: Vec<InstId>,
    queued: BitSet<InstId>,
}

impl SinkWorklist {
    fn new(func: &Function, facts: &SinkFacts) -> Self {
        let mut worklist = Self::default();
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if facts.is_sink_candidate(inst) {
                    worklist.push(inst);
                }
            }
        }
        worklist
    }

    fn push(&mut self, inst: InstId) {
        if self.queued.insert(inst) {
            self.insts.push(inst);
        }
    }

    fn pop(&mut self) -> Option<InstId> {
        let inst = self.insts.pop()?;
        self.queued.remove(inst);
        Some(inst)
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

fn plan_sink_inst(
    func: &Function,
    cfg: &ControlFlowGraph,
    domtree: &DomTree,
    lpt: &LoopTree,
    facts: &SinkFacts,
    inst: InstId,
    use_sites: &mut Vec<UseSite>,
) -> Option<SinkPlan> {
    let source_block = func.layout.inst_block(inst);
    if !collect_use_sites(func, inst, use_sites) {
        return None;
    }
    let dest_block = nearest_common_dominator(domtree, use_sites.iter().map(|site| site.block))?;

    if dest_block == source_block
        || !domtree.dominates(source_block, dest_block)
        || lpt.loop_of_block(source_block) != lpt.loop_of_block(dest_block)
        || crosses_cold_guard_to_hot_continuation(cfg, domtree, facts, source_block, dest_block)
    {
        return None;
    }

    let before = insertion_anchor(func, dest_block, use_sites)?;
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

fn requeue_operand_defs(
    func: &Function,
    facts: &SinkFacts,
    inst: InstId,
    worklist: &mut SinkWorklist,
) {
    func.dfg.inst(inst).for_each_value(&mut |value| {
        if let Value::Inst { inst: def_inst, .. } = func.dfg.value(value)
            && *def_inst != inst
            && facts.is_sink_candidate(*def_inst)
            && func.layout.is_inst_inserted(*def_inst)
        {
            worklist.push(*def_inst);
        }
    });
}

fn collect_use_sites(func: &Function, inst: InstId, sites: &mut Vec<UseSite>) -> bool {
    sites.clear();
    for &result in func.dfg.inst_results(inst) {
        for &user in func.dfg.users(result) {
            if !func.dfg.has_inst(user) || !func.layout.is_inst_inserted(user) {
                continue;
            }
            if user == inst {
                return false;
            }

            if let Some(phi) = func.dfg.cast_phi(user) {
                for &(arg, pred) in phi.args() {
                    if arg == result {
                        let Some(anchor) = func.layout.last_inst_of(pred) else {
                            return false;
                        };
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

    !sites.is_empty()
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
    let mut a = a;
    let mut b = b;
    let mut a_depth = domtree.depth_of(a)?;
    let mut b_depth = domtree.depth_of(b)?;

    while a_depth > b_depth {
        a = domtree.idom_of(a)?;
        a_depth -= 1;
    }
    while b_depth > a_depth {
        b = domtree.idom_of(b)?;
        b_depth -= 1;
    }
    while a != b {
        a = domtree.idom_of(a)?;
        b = domtree.idom_of(b)?;
    }

    Some(a)
}

fn insertion_anchor(func: &Function, block: BlockId, use_sites: &[UseSite]) -> Option<InstId> {
    if !use_sites.iter().any(|site| site.block == block) {
        return func.layout.last_inst_of(block);
    }

    func.layout.iter_inst(block).find(|&inst| {
        use_sites
            .iter()
            .any(|site| site.block == block && site.anchor == inst)
    })
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
