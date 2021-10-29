use cranelift_entity::{packed_option::PackedOption, SecondaryMap};

use super::ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    insn::{InsnData, JumpOp},
};
use super::{cfg::ControlFlowGraph, Block, Function, Insn};

#[derive(Default)]
pub struct CriticalEdgeSplitter {
    critical_edges: Vec<Insn>,
    inserted_blocks_for: SecondaryMap<Block, PackedOption<Block>>,
}

impl CriticalEdgeSplitter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) {
        self.critical_edges.clear();
        self.inserted_blocks_for.clear();

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
        let source_block = func.layout.insn_block(insn);

        if let Some(inserted_dest) = self.inserted_blocks_for[original_dest].expand() {
            *func.dfg.branch_dest_mut(insn).unwrap() = inserted_dest;
            self.modify_cfg(cfg, source_block, original_dest, inserted_dest);
            self.modify_phi_blocks(func, original_dest);
            return;
        }

        let inserted_dest = func.dfg.make_block();
        let fallthrough = func.dfg.make_insn(InsnData::Jump {
            code: JumpOp::FallThrough,
            dest: original_dest,
        });
        let mut cursor = InsnInserter::new(func, CursorLocation::BlockTop(original_dest));
        cursor.insert_block_before(inserted_dest);
        cursor.set_loc(CursorLocation::BlockTop(inserted_dest));
        cursor.append_insn(fallthrough);

        *func.dfg.branch_dest_mut(insn).unwrap() = inserted_dest;
        self.inserted_blocks_for[original_dest] = Some(inserted_dest).into();

        self.modify_cfg(cfg, source_block, original_dest, inserted_dest);
        self.modify_phi_blocks(func, original_dest);
    }

    fn modify_phi_blocks(&self, func: &mut Function, original_dest: Block) {
        for insn in func.layout.iter_insn(original_dest) {
            if !func.dfg.is_phi(insn) {
                continue;
            }

            for block in func.dfg.phi_blocks_mut(insn) {
                if *block == original_dest {
                    *block = self.inserted_blocks_for[original_dest].unwrap();
                }
            }
        }
    }

    fn modify_cfg(
        &self,
        cfg: &mut ControlFlowGraph,
        source_block: Block,
        original_dest: Block,
        inserted_dest: Block,
    ) {
        cfg.remove_edge(source_block, original_dest);
        cfg.add_edge(source_block, inserted_dest);
        cfg.add_edge(inserted_dest, original_dest);
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

    #[test]
    fn critical_edge_phi() {
        let mut builder = func_builder(vec![], vec![]);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();

        builder.switch_to_block(a);
        let v1 = builder.imm_u8(1);
        builder.jump(b);

        builder.switch_to_block(b);
        let phi_value = builder.phi(&[(v1, a)]);
        let v2 = builder.add(phi_value, v1);
        builder.append_phi_arg(phi_value, v2, b);
        builder.brz(b, phi_value);
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
        jump block1;

    block3:
        fallthrough block1;

    block1:
        v1.i8 = phi (v0.i8 block0) (v2.i8 block3);
        v2.i8 = add v1.i8 v0.i8;
        brz v1.i8 block3;
        jump block2;

    block2:
        return;

"
        );

        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(&func);
        assert_eq!(cfg, cfg_split);
    }
}
