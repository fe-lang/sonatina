use std::collections::BTreeSet;

use cranelift_entity::{packed_option::PackedOption, SecondaryMap};

use super::ir::{Block, Function, Insn};

#[derive(Default, Debug, PartialEq, Eq)]
pub struct ControlFlowGraph {
    entry: PackedOption<Block>,
    blocks: SecondaryMap<Block, BlockNode>,
}

impl ControlFlowGraph {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn compute(&mut self, func: &Function) {
        self.blocks.clear();

        self.entry = func.layout.first_block().into();

        for block in func.layout.iter_block() {
            if let Some(last_insn) = func.layout.last_insn_of(block) {
                self.add_insn_dests(func, last_insn);
            }
        }
    }

    pub fn preds_of(&self, block: Block) -> impl Iterator<Item = &Block> {
        self.blocks[block].preds()
    }

    pub fn succs_of(&self, block: Block) -> impl Iterator<Item = &Block> {
        self.blocks[block].succs()
    }

    pub fn pred_num_of(&self, block: Block) -> usize {
        self.blocks[block].pred_num()
    }

    pub fn succ_num_of(&self, block: Block) -> usize {
        self.blocks[block].succ_num()
    }

    pub fn entry(&self) -> Option<Block> {
        self.entry.expand()
    }

    pub fn post_order(&self) -> CfgPostOrder {
        CfgPostOrder::new(self)
    }

    pub fn add_edge(&mut self, from: Block, to: Block) {
        self.blocks[to].push_pred(from);
        self.blocks[from].push_succ(to);
    }

    pub fn remove_edge(&mut self, from: Block, to: Block) {
        self.blocks[to].remove_pred(from);
        self.blocks[from].remove_succ(to);
    }

    fn add_insn_dests(&mut self, func: &Function, insn: Insn) {
        for dest in func.dfg.branch_dests(insn) {
            let block = func.layout.insn_block(insn);
            self.add_edge(block, *dest);
        }
    }
}

#[derive(Default, Clone, Debug, PartialEq, Eq)]
struct BlockNode {
    preds: BTreeSet<Block>,
    succs: BTreeSet<Block>,
}

impl BlockNode {
    fn push_pred(&mut self, pred: Block) {
        self.preds.insert(pred);
    }

    fn push_succ(&mut self, succ: Block) {
        self.succs.insert(succ);
    }

    fn remove_pred(&mut self, pred: Block) {
        self.preds.remove(&pred);
    }

    fn remove_succ(&mut self, succ: Block) {
        self.succs.remove(&succ);
    }

    fn preds(&self) -> impl Iterator<Item = &Block> {
        self.preds.iter()
    }

    fn succs(&self) -> impl Iterator<Item = &Block> {
        self.succs.iter()
    }

    fn pred_num(&self) -> usize {
        self.preds.len()
    }

    fn succ_num(&self) -> usize {
        self.succs.len()
    }
}

pub struct CfgPostOrder<'a> {
    cfg: &'a ControlFlowGraph,
    node_state: SecondaryMap<Block, NodeState>,
    stack: Vec<Block>,
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

impl<'a> Iterator for CfgPostOrder<'a> {
    type Item = Block;

    fn next(&mut self) -> Option<Block> {
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
