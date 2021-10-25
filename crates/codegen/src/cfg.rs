use cranelift_entity::{packed_option::PackedOption, SecondaryMap};

use super::ir::{Block, Function, Insn};

#[derive(Default)]
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
                if self.maybe_add_edge(func, last_insn, block) {
                    if let Some(penultimate_insn) = func.layout.prev_insn_of(last_insn) {
                        self.maybe_add_edge(func, penultimate_insn, block);
                    }
                }
            }
        }
    }

    pub fn preds_of(&self, block: Block) -> &[Block] {
        &self.blocks[block].preds
    }

    pub fn succs_of(&self, block: Block) -> &[Block] {
        &self.blocks[block].succs
    }

    pub fn entry(&self) -> Option<Block> {
        self.entry.expand()
    }

    pub fn post_order(&self) -> CfgPostOrder {
        CfgPostOrder::new(self)
    }

    fn maybe_add_edge(&mut self, func: &Function, insn: Insn, block: Block) -> bool {
        if let Some(dest) = func.dfg.branch_dest(insn) {
            self.blocks[block].push_succ(dest);
            self.blocks[dest].push_pred(block);
            true
        } else {
            false
        }
    }
}

#[derive(Default, Clone, Debug)]
struct BlockNode {
    preds: Vec<Block>,
    succs: Vec<Block>,
}

impl BlockNode {
    fn push_pred(&mut self, pred: Block) {
        self.preds.push(pred)
    }

    fn push_succ(&mut self, succ: Block) {
        self.succs.push(succ)
    }
}

pub struct CfgPostOrder<'a> {
    cfg: &'a ControlFlowGraph,
    node_state: SecondaryMap<Block, State>,
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
struct State(u8);

impl State {
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
