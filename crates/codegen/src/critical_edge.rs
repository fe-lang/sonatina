use cranelift_entity::{packed_option::PackedOption, SecondaryMap};

use super::ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    insn::{InsnData, JumpOp},
};
use super::{cfg::ControlFlowGraph, Block, Function, Insn};

#[derive(Debug, Default)]
pub struct CriticalEdgeSplitter {
    critical_edges: Vec<CriticalEdge>,
    inserted_blocks_for: SecondaryMap<Block, PackedOption<Block>>,
}

impl CriticalEdgeSplitter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) {
        self.clear();

        for block in func.layout.iter_block() {
            if let Some(last_insn) = func.layout.last_insn_of(block) {
                self.add_critical_edges(last_insn, func, cfg);
            }
        }

        let edges = std::mem::take(&mut self.critical_edges);
        for edge in edges {
            self.split_edge(edge, func, cfg);
        }
    }

    pub fn clear(&mut self) {
        self.critical_edges.clear();
        self.inserted_blocks_for.clear();
    }

    fn add_critical_edges(&mut self, insn: Insn, func: &Function, cfg: &ControlFlowGraph) {
        let branch_info = func.dfg.analyze_branch(insn);
        if branch_info.dests_num() < 2 {
            return;
        }

        for dest in branch_info.iter_dests() {
            if cfg.pred_num_of(dest) > 1 {
                self.critical_edges.push(CriticalEdge::new(insn, dest));
            }
        }
    }

    fn split_edge(&mut self, edge: CriticalEdge, func: &mut Function, cfg: &mut ControlFlowGraph) {
        let insn = edge.insn;
        let original_dest = edge.to;
        let source_block = func.layout.insn_block(insn);

        // If already blocks for the edge, then use it.
        if let Some(inserted_dest) = self.inserted_blocks_for[original_dest].expand() {
            func.dfg
                .rewrite_branch_dest(insn, original_dest, inserted_dest);
            self.modify_cfg(cfg, source_block, original_dest, inserted_dest);
            self.modify_phi_blocks(func, original_dest);
            return;
        }

        // Create a new block that contains only a jump insn to the destinating block of the
        // critical edge.
        let inserted_dest = func.dfg.make_block();
        let fallthrough = func.dfg.make_insn(InsnData::Jump {
            code: JumpOp::FallThrough,
            dests: [original_dest],
        });
        let mut cursor = InsnInserter::new(func, CursorLocation::BlockTop(original_dest));
        cursor.insert_block_before(inserted_dest);
        cursor.set_loc(CursorLocation::BlockTop(inserted_dest));
        cursor.append_insn(fallthrough);

        // Store the created block to reuse.
        self.inserted_blocks_for[original_dest] = Some(inserted_dest).into();

        // Rewrite branch destination to the new block.
        func.dfg
            .rewrite_branch_dest(insn, original_dest, inserted_dest);
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

#[derive(Debug)]
struct CriticalEdge {
    insn: Insn,
    to: Block,
}

impl CriticalEdge {
    fn new(insn: Insn, to: Block) -> Self {
        Self { insn, to }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::builder::test_util::{dump_func, func_builder};

    #[test]
    fn critical_edge_basic() {
        let mut builder = func_builder(&[], &[]);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.make_imm_value(1i32);
        builder.br(v0, c, b);

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
        br 1.i32 block3 block1;

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
    #[allow(clippy::many_single_char_names)]
    fn critical_edge_dup() {
        let mut builder = func_builder(&[], &[]);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let e = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.make_imm_value(1i8);
        builder.br(v0, d, b);

        builder.switch_to_block(b);
        builder.jump(c);

        builder.switch_to_block(c);
        builder.br(v0, e, d);

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
        br 1.i8 block5 block1;

    block1:
        jump block2;

    block2:
        br 1.i8 block4 block5;

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
        let mut builder = func_builder(&[], &[]);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();

        builder.switch_to_block(a);
        let v1 = builder.make_imm_value(1i8);
        builder.jump(b);

        builder.switch_to_block(b);
        let phi_value = builder.phi(&[(v1, a)]);
        let v2 = builder.add(phi_value, v1);
        builder.append_phi_arg(phi_value, v2, b);
        builder.br(phi_value, c, b);

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
        jump block1;

    block3:
        fallthrough block1;

    block1:
        v1.i8 = phi (1.i8 block0) (v2 block3);
        v2.i8 = add v1 1.i8;
        br v1 block2 block3;

    block2:
        return;

"
        );

        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(&func);
        assert_eq!(cfg, cfg_split);
    }
}
