use cranelift_entity::{PrimaryMap, SecondaryMap, entity_impl, packed_option::PackedOption};
use smallvec::SmallVec;
use vec_collections::VecSet;

use crate::{BlockId, Function};

type BlockSet = VecSet<[BlockId; 4]>;
type EdgeList = SmallVec<[CfgEdge; 4]>;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct CfgEdge(pub u32);
entity_impl!(CfgEdge);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CfgEdgeData {
    pub from: BlockId,
    pub to: BlockId,
    pub branch_slot: usize,
}

#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct ControlFlowGraph {
    entry: PackedOption<BlockId>,
    blocks: SecondaryMap<BlockId, BlockNode>,
    edges: PrimaryMap<CfgEdge, CfgEdgeData>,
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

    pub fn pred_edges_of(&self, block: BlockId) -> impl Iterator<Item = &CfgEdge> {
        self.blocks[block].pred_edges()
    }

    pub fn pred_edges_as_slice(&self, block: BlockId) -> &[CfgEdge] {
        self.blocks[block].pred_edges_slice()
    }

    pub fn preds_as_slice(&self, block: BlockId) -> &[BlockId] {
        self.blocks[block].preds_slice()
    }

    pub fn succs_of(&self, block: BlockId) -> impl Iterator<Item = &BlockId> {
        self.blocks[block].succs()
    }

    pub fn succ_edges_of(&self, block: BlockId) -> impl Iterator<Item = &CfgEdge> {
        self.blocks[block].succ_edges()
    }

    pub fn succ_edges_as_slice(&self, block: BlockId) -> &[CfgEdge] {
        self.blocks[block].succ_edges_slice()
    }

    pub fn succs_as_slice(&self, block: BlockId) -> &[BlockId] {
        self.blocks[block].succs_slice()
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

    pub fn edge_data(&self, edge: CfgEdge) -> &CfgEdgeData {
        &self.edges[edge]
    }

    pub fn post_order(&self) -> CfgPostOrder<'_> {
        CfgPostOrder::new(self)
    }

    pub fn reachable_blocks(&self) -> SecondaryMap<BlockId, bool> {
        let mut reachable = SecondaryMap::default();
        let Some(entry) = self.entry() else {
            return reachable;
        };

        let mut stack = vec![entry];
        while let Some(block) = stack.pop() {
            if reachable[block] {
                continue;
            }

            reachable[block] = true;
            stack.extend(
                self.succs_as_slice(block)
                    .iter()
                    .copied()
                    .filter(|succ| !reachable[*succ]),
            );
        }

        reachable
    }

    pub fn replace_succ_block(&mut self, from: BlockId, old_to: BlockId, new_to: BlockId) {
        if old_to == new_to {
            return;
        }

        let moved_edges: Vec<_> = self.blocks[from]
            .succ_edges()
            .copied()
            .filter(|edge| self.edges[*edge].to == old_to)
            .collect();
        if moved_edges.is_empty() {
            return;
        }

        for edge in &moved_edges {
            self.edges[*edge].to = new_to;
        }
        self.blocks[old_to].retain_pred_edges(|edge| !moved_edges.contains(edge));
        self.blocks[new_to].append_pred_edges(&moved_edges);

        self.blocks[from].remove_succ(old_to);
        self.blocks[from].push_succ(new_to);
        self.blocks[old_to].remove_pred(from);
        self.blocks[new_to].push_pred(from);
    }

    pub fn remove_succ_block(&mut self, from: BlockId, to: BlockId) {
        let removed_edges: Vec<_> = self.blocks[from]
            .succ_edges()
            .copied()
            .filter(|edge| self.edges[*edge].to == to)
            .collect();
        if removed_edges.is_empty() {
            return;
        }

        self.blocks[from].retain_succ_edges(|edge| !removed_edges.contains(edge));
        self.blocks[to].retain_pred_edges(|edge| !removed_edges.contains(edge));
        self.blocks[from].remove_succ(to);
        self.blocks[to].remove_pred(from);
    }

    pub fn add_succ_block(&mut self, from: BlockId, to: BlockId) {
        let branch_slot = self.blocks[from].succ_edges_slice().len();
        self.append_edge(from, to, branch_slot);
    }

    pub fn add_exit(&mut self, block: BlockId) {
        if !self.exits.contains(&block) {
            self.exits.push(block);
        }
    }

    pub fn remove_exit(&mut self, block: BlockId) {
        self.exits.retain(|exit| *exit != block);
    }

    pub fn replace_exit(&mut self, old: BlockId, new: BlockId) {
        self.remove_exit(old);
        self.add_exit(new);
    }

    pub fn reverse_edges(&mut self, new_entry: BlockId, new_exits: &[BlockId]) {
        for edge in self.edges.values_mut() {
            std::mem::swap(&mut edge.from, &mut edge.to);
        }
        for node in self.blocks.values_mut() {
            node.reverse_edge();
        }
        self.entry = new_entry.into();
        self.exits = new_exits.into();
    }

    pub fn clear(&mut self) {
        self.entry = None.into();
        self.blocks.clear();
        self.edges.clear();
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

        for (branch_slot, dest) in branch_info.dests().into_iter().enumerate() {
            let block = func.layout.inst_block(inst);
            self.append_edge(block, dest, branch_slot);
        }
    }

    fn append_edge(&mut self, from: BlockId, to: BlockId, branch_slot: usize) {
        let edge = self.edges.push(CfgEdgeData {
            from,
            to,
            branch_slot,
        });
        self.blocks[from].push_succ_edge(edge);
        self.blocks[to].push_pred_edge(edge);
        self.blocks[from].push_succ(to);
        self.blocks[to].push_pred(from);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BlockNode {
    preds: BlockSet,
    succs: BlockSet,
    in_edges: EdgeList,
    out_edges: EdgeList,
}

impl Default for BlockNode {
    fn default() -> Self {
        Self {
            preds: VecSet::empty(),
            succs: VecSet::empty(),
            in_edges: EdgeList::new(),
            out_edges: EdgeList::new(),
        }
    }
}

impl BlockNode {
    fn push_pred(&mut self, pred: BlockId) {
        self.preds.insert(pred);
    }

    fn push_succ(&mut self, succ: BlockId) {
        self.succs.insert(succ);
    }

    fn push_pred_edge(&mut self, edge: CfgEdge) {
        self.in_edges.push(edge);
    }

    fn push_succ_edge(&mut self, edge: CfgEdge) {
        self.out_edges.push(edge);
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

    fn pred_edges(&self) -> impl Iterator<Item = &CfgEdge> {
        self.in_edges.iter()
    }

    fn pred_edges_slice(&self) -> &[CfgEdge] {
        self.in_edges.as_slice()
    }

    fn preds_slice(&self) -> &[BlockId] {
        self.preds.as_ref()
    }

    fn succs(&self) -> impl Iterator<Item = &BlockId> {
        self.succs.iter()
    }

    fn succ_edges(&self) -> impl Iterator<Item = &CfgEdge> {
        self.out_edges.iter()
    }

    fn succ_edges_slice(&self) -> &[CfgEdge] {
        self.out_edges.as_slice()
    }

    fn succs_slice(&self) -> &[BlockId] {
        self.succs.as_ref()
    }

    fn pred_num(&self) -> usize {
        self.preds.len()
    }

    fn succ_num(&self) -> usize {
        self.succs.len()
    }

    fn reverse_edge(&mut self) {
        std::mem::swap(&mut self.preds, &mut self.succs);
        std::mem::swap(&mut self.in_edges, &mut self.out_edges);
    }

    fn retain_pred_edges(&mut self, mut keep: impl FnMut(&CfgEdge) -> bool) {
        self.in_edges.retain(|edge| keep(edge));
    }

    fn retain_succ_edges(&mut self, mut keep: impl FnMut(&CfgEdge) -> bool) {
        self.out_edges.retain(|edge| keep(edge));
    }

    fn append_pred_edges(&mut self, edges: &[CfgEdge]) {
        self.in_edges.extend_from_slice(edges);
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use crate::{
        Type,
        builder::test_util::{test_func_builder, test_module_builder},
        inst::control_flow::{BrTable, Return},
        isa::Isa,
    };

    use super::ControlFlowGraph;

    #[test]
    fn cfg_preserves_duplicate_branch_edges_separately_from_unique_successors() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I8], Type::I32);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        builder.switch_to_block(b0);
        let case0 = builder.make_imm_value(0i8);
        let case1 = builder.make_imm_value(1i8);
        builder.insert_inst_no_result(BrTable::new(
            is,
            builder.args()[0],
            Some(b1),
            vec![(case0, b1), (case1, b2)],
        ));

        builder.switch_to_block(b1);
        let one = builder.make_imm_value(1i32);
        builder.insert_inst_no_result(Return::new_single(is, one));

        builder.switch_to_block(b2);
        let two = builder.make_imm_value(2i32);
        builder.insert_inst_no_result(Return::new_single(is, two));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.view(func_ref, |func| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);

            let succ_edges: Vec<_> = cfg
                .succ_edges_as_slice(b0)
                .iter()
                .map(|edge| {
                    let data = cfg.edge_data(*edge);
                    (data.from, data.to, data.branch_slot)
                })
                .collect();
            assert_eq!(succ_edges, vec![(b0, b1, 0), (b0, b1, 1), (b0, b2, 2)]);

            let pred_edges: Vec<_> = cfg
                .pred_edges_as_slice(b1)
                .iter()
                .map(|edge| {
                    let data = cfg.edge_data(*edge);
                    (data.from, data.to, data.branch_slot)
                })
                .collect();
            assert_eq!(pred_edges, vec![(b0, b1, 0), (b0, b1, 1)]);

            assert_eq!(cfg.succ_edges_as_slice(b0).len(), 3);
            assert_eq!(cfg.pred_edges_as_slice(b1).len(), 2);
            assert_eq!(cfg.succ_num_of(b0), 2);
            assert_eq!(cfg.pred_num_of(b1), 1);
            assert_eq!(cfg.succs_as_slice(b0), &[b1, b2]);
            assert_eq!(cfg.preds_as_slice(b1), &[b0]);
            assert_eq!(cfg.preds_as_slice(b2), &[b0]);

            let reachable: BTreeSet<_> = cfg
                .reachable_blocks()
                .iter()
                .filter_map(|(block, is_reachable)| is_reachable.then_some(block))
                .collect();
            assert_eq!(reachable, BTreeSet::from([b0, b1, b2]));
        });
    }
}
