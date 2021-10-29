use cranelift_entity::{packed_option::PackedOption, SecondaryMap};

use super::ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    insn::{InsnData, JumpOp},
};
use super::{cfg::ControlFlowGraph, Block, Function, Insn};

#[derive(Default)]
pub struct CriticalEdgeSplitter {
    added_block: SecondaryMap<Block, PackedOption<Block>>,
    critical_edges: Vec<Insn>,
}

impl CriticalEdgeSplitter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) {
        self.critical_edges.clear();
        self.added_block.clear();

        for block in func.layout.iter_block() {
            let (last_insn, penultimate_insn) = func.layout.last_two_insn_of(block);
            if let Some(last_insn) = last_insn {
                self.push_insn_if_critical_edge(last_insn, func, cfg);
            }
            if let Some(penultimate_insn) = penultimate_insn {
                self.push_insn_if_critical_edge(penultimate_insn, func, cfg);
            }
        }

        let edges = std::mem::take(&mut self.critical_edges);
        for &insn in &edges {
            self.split_edge(insn, func, cfg);
        }
        self.critical_edges = edges;
    }

    fn push_insn_if_critical_edge(&mut self, insn: Insn, func: &Function, cfg: &ControlFlowGraph) {
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

        if let Some(added_dest) = self.added_block[original_dest].expand() {
            *func.dfg.branch_dest_mut(insn).unwrap() = added_dest;
            cfg.remove_edge(current_block, original_dest);
            cfg.add_edge(current_block, added_dest);
            return;
        }

        let added_dest = func.dfg.make_block();
        let fallthrough = func.dfg.make_insn(InsnData::Jump {
            code: JumpOp::FallThrough,
            dest: original_dest,
        });
        let mut cursor = InsnInserter::new(func, CursorLocation::BlockTop(original_dest));
        cursor.insert_block_before(added_dest);
        cursor.set_loc(CursorLocation::BlockTop(added_dest));
        cursor.append_insn(fallthrough);

        *func.dfg.branch_dest_mut(insn).unwrap() = added_dest;
        cfg.remove_edge(current_block, original_dest);
        cfg.add_edge(current_block, added_dest);
        cfg.add_edge(added_dest, original_dest);

        self.added_block[original_dest] = Some(added_dest).into();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::test_util::{dump_func, func_builder};

    #[test]
    fn critical_edge_basic() {
        let mut builder = func_builder(vec![], vec![]);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.imm_u8(1);
        builder.brz(b, v0);
        builder.jump(c);

        builder.switch_to_block(b);
        builder.jump(c);

        builder.switch_to_block(c);
        builder.ret(&[]);

        builder.seal_all();

        let mut func = builder.build();
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(&func);
        CriticalEdgeSplitter::default().run(&mut func, &mut cfg);

        assert_eq!(
            dump_func(&func),
            "func %test_func():
    block0:
        v0.i8 = imm_u8 1;
        brz v0.i8 block1;
        jump block3;

    block1:
        jump block2;

    block3:
        fallthrough block2;

    block2:
        return;

"
        );

        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(&func);
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    fn critical_edge_dup() {
        let mut builder = func_builder(vec![], vec![]);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let e = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.imm_u8(1);
        builder.brz(b, v0);
        builder.jump(d);

        builder.switch_to_block(b);
        builder.jump(c);

        builder.switch_to_block(c);
        builder.brz(d, v0);
        builder.jump(e);

        builder.switch_to_block(d);
        builder.ret(&[]);

        builder.switch_to_block(e);
        builder.ret(&[]);

        builder.seal_all();

        let mut func = builder.build();
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(&func);
        CriticalEdgeSplitter::default().run(&mut func, &mut cfg);

        assert_eq!(
            dump_func(&func),
            "func %test_func():
    block0:
        v0.i8 = imm_u8 1;
        brz v0.i8 block1;
        jump block5;

    block1:
        jump block2;

    block2:
        brz v0.i8 block5;
        jump block4;

    block5:
        fallthrough block3;

    block3:
        return;

    block4:
        return;

"
        );

        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(&func);
        assert_eq!(cfg, cfg_split);
    }
}
