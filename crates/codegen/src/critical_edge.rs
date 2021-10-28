use cranelift_entity::{packed_option::PackedOption, SecondaryMap};

use super::ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    insn::{InsnData, JumpOp},
};
use super::{cfg::ControlFlowGraph, Block, Function, Insn};

pub struct CriticalEdgeSplitter {
    added_block: SecondaryMap<Block, PackedOption<Block>>,
    critical_edges: Vec<Insn>,
}

impl CriticalEdgeSplitter {
    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) {
        self.critical_edges.clear();
        self.added_block.clear();

        for block in func.layout.iter_block() {
            let (last_insn, penultimate_insn) = func.layout.last_two_insn_of(block);
            if let Some(last_insn) = last_insn {
                self.append_if_critical_edge(last_insn, func, cfg);
            }
            if let Some(penultimate_insn) = penultimate_insn {
                self.append_if_critical_edge(penultimate_insn, func, cfg);
            }
        }

        let mut edges = std::mem::replace(&mut self.critical_edges, vec![]);
        for &insn in &edges {
            self.split_edge(insn, func, cfg);
        }
        std::mem::swap(&mut self.critical_edges, &mut edges);
    }

    fn append_if_critical_edge(&mut self, insn: Insn, func: &Function, cfg: &ControlFlowGraph) {
        if self.is_critical_edge(insn, func, cfg) {
            self.critical_edges.push(insn);
        }
    }

    fn is_critical_edge(&self, insn: Insn, func: &Function, cfg: &ControlFlowGraph) -> bool {
        let dest = match func.dfg.branch_dest(insn) {
            Some(dest) => dest,
            None => return false,
        };

        let block = func.layout.insn_block(insn);
        cfg.succ_num_of(block) > 1 && cfg.pred_num_of(dest) > 1
    }

    fn split_edge(&mut self, insn: Insn, func: &mut Function, cfg: &mut ControlFlowGraph) {
        let original_dest = func.dfg.branch_dest(insn).unwrap();
        let current_block = func.layout.insn_block(insn);
        cfg.remove_edge(current_block, original_dest);

        if let Some(added_dest) = self.added_block[original_dest].expand() {
            *func.dfg.branch_dest_mut(insn).unwrap() = added_dest;
            cfg.add_edge(current_block, added_dest);
            return;
        }

        let added_dest = func.dfg.make_block();
        let fallthrough = func.dfg.make_insn(InsnData::Jump {
            code: JumpOp::FallThrough,
            dest: added_dest,
        });
        let mut cursor = InsnInserter::new(func, CursorLocation::At(insn));
        cursor.insert_block_before(added_dest);
        cursor.set_loc(CursorLocation::BlockTop(added_dest));
        cursor.append_insn(fallthrough);
        cfg.add_edge(added_dest, original_dest);
    }
}
