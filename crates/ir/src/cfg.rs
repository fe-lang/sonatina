use std::collections::BTreeSet;

use cranelift_entity::{packed_option::PackedOption, SecondaryMap};

use crate::{BlockId, Function};

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ControlFlowGraph {
    entry: PackedOption<BlockId>,
    blocks: SecondaryMap<BlockId, BlockNode>,
    pub exits: smallvec::SmallVec<[BlockId; 8]>,
}

impl ControlFlowGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn compute(&mut self, func: &Function) {
        self.clear();

        self.entry = func.layout.entry_block().into();

        for block in func.layout.iter_block() {
            if let Some(last_inst) = func.layout.last_inst_of(block) {
                self.analyze_inst(func, last_inst);
            }
        }
    }

    pub fn preds_of(&self, block: BlockId) -> impl Iterator<Item = &BlockId> {
        self.blocks[block].preds()
    }

    pub fn succs_of(&self, block: BlockId) -> impl Iterator<Item = &BlockId> {
        self.blocks[block].succs()
    }

    pub fn pred_num_of(&self, block: BlockId) -> usize {
        self.blocks[block].pred_num()
    }

    pub fn succ_num_of(&self, block: BlockId) -> usize {
        self.blocks[block].succ_num()
    }

    pub fn entry(&self) -> Option<BlockId> {
        self.entry.expand()
    }

    pub fn post_order(&self) -> CfgPostOrder<'_> {
        CfgPostOrder::new(self)
    }

    pub fn add_edge(&mut self, from: BlockId, to: BlockId) {
        self.blocks[to].push_pred(from);
        self.blocks[from].push_succ(to);
    }

    pub fn remove_edge(&mut self, from: BlockId, to: BlockId) {
        self.blocks[to].remove_pred(from);
        self.blocks[from].remove_succ(to);
    }

    pub fn reverse_edges(&mut self, new_entry: BlockId, new_exits: &[BlockId]) {
        for node in self.blocks.values_mut() {
            node.reverse_edge();
        }
        self.entry = new_entry.into();
        self.exits = new_exits.into();
    }

    pub fn clear(&mut self) {
        self.entry = None.into();
        self.blocks.clear();
        self.exits.clear();
    }

    fn analyze_inst(&mut self, func: &Function, inst: crate::InstId) {
        if func.dfg.is_exit(inst) {
            let exit = func.layout.inst_block(inst);
            self.exits.push(exit);
        }

        let Some(branch_info) = func.dfg.branch_info(inst) else {
            return;
        };

        for dest in branch_info.dests() {
            let block = func.layout.inst_block(inst);
            self.add_edge(block, dest);
        }
    }
}

#[derive(Default, Clone, Debug, PartialEq, Eq)]
struct BlockNode {
    preds: BTreeSet<BlockId>,
    succs: BTreeSet<BlockId>,
}

impl BlockNode {
    fn push_pred(&mut self, pred: BlockId) {
        self.preds.insert(pred);
    }

    fn push_succ(&mut self, succ: BlockId) {
        self.succs.insert(succ);
    }

    fn remove_pred(&mut self, pred: BlockId) {
        self.preds.remove(&pred);
    }

    fn remove_succ(&mut self, succ: BlockId) {
        self.succs.remove(&succ);
    }

    fn preds(&self) -> impl Iterator<Item = &BlockId> {
        self.preds.iter()
    }

    fn succs(&self) -> impl Iterator<Item = &BlockId> {
        self.succs.iter()
    }

    fn pred_num(&self) -> usize {
        self.preds.len()
    }

    fn succ_num(&self) -> usize {
        self.succs.len()
    }

    fn reverse_edge(&mut self) {
        std::mem::swap(&mut self.preds, &mut self.succs);
    }
}

pub struct CfgPostOrder<'a> {
    cfg: &'a ControlFlowGraph,
    node_state: SecondaryMap<BlockId, NodeState>,
    stack: Vec<BlockId>,
}

impl<'a> CfgPostOrder<'a> {
    fn new(cfg: &'a ControlFlowGraph) -> Self {
        let mut stack = Vec::new();

        if let Some(entry) = cfg.entry() {
            stack.push(entry);
        }

        Self {
            cfg,
            node_state: SecondaryMap::default(),
            stack,
        }
    }
}

impl Iterator for CfgPostOrder<'_> {
    type Item = BlockId;

    fn next(&mut self) -> Option<BlockId> {
        while let Some(&block) = self.stack.last() {
            if self.node_state[block].is_unvisited() {
                self.node_state[block].set_visited();
                for &pred in self.cfg.succs_of(block) {
                    if self.node_state[pred].is_unvisited() {
                        self.stack.push(pred);
                    }
                }
            } else {
                self.stack.pop().unwrap();
                if !self.node_state[block].has_finished() {
                    self.node_state[block].set_finished();
                    return Some(block);
                }
            }
        }

        None
    }
}

#[derive(Default, Debug, Clone, Copy)]
struct NodeState(u8);

impl NodeState {
    fn is_unvisited(self) -> bool {
        self.0 == 0
    }

    fn has_finished(self) -> bool {
        self.0 == 2
    }

    fn set_visited(&mut self) {
        self.0 = 1;
    }

    fn set_finished(&mut self) {
        self.0 = 2;
    }
}
