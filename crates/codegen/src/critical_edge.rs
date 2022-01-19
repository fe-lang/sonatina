use super::{
    cfg::ControlFlowGraph,
    ir::{
        func_cursor::{CursorLocation, FuncCursor, InsnInserter},
        insn::InsnData,
        Block, Function, Insn,
    },
    TargetIsa,
};

#[derive(Debug)]
pub struct CriticalEdgeSplitter<'isa> {
    critical_edges: Vec<CriticalEdge>,
    isa: &'isa TargetIsa,
}

impl<'isa> CriticalEdgeSplitter<'isa> {
    pub fn new(isa: &'isa TargetIsa) -> Self {
        Self {
            critical_edges: Vec::default(),
            isa,
        }
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

        // Create a new block that contains only a jump insn to the destinating block of the
        // critical edge.
        let inserted_dest = func.dfg.make_block();
        let jump = func.dfg.make_insn(InsnData::jump(original_dest));
        let mut cursor = InsnInserter::new(func, self.isa, CursorLocation::BlockTop(original_dest));
        cursor.append_block(inserted_dest);
        cursor.set_loc(CursorLocation::BlockTop(inserted_dest));
        cursor.append_insn(jump);

        // Rewrite branch destination to the new block.
        func.dfg
            .rewrite_branch_dest(insn, original_dest, inserted_dest);
        self.modify_cfg(cfg, source_block, original_dest, inserted_dest);
        self.modify_phi_blocks(func, original_dest, inserted_dest);
    }

    fn modify_phi_blocks(&self, func: &mut Function, original_dest: Block, inserted_dest: Block) {
        for insn in func.layout.iter_insn(original_dest) {
            if !func.dfg.is_phi(insn) {
                continue;
            }

            for block in func.dfg.phi_blocks_mut(insn) {
                if *block == original_dest {
                    *block = inserted_dest;
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
    use crate::ir::builder::test_util::{build_test_isa, dump_func, func_builder};

    #[test]
    fn critical_edge_basic() {
        let isa = build_test_isa();
        let mut builder = func_builder(&[], None, &isa);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.make_imm_value(1i32);
        builder.br(v0, c, b);

        builder.switch_to_block(b);
        builder.jump(c);

        builder.switch_to_block(c);
        builder.ret(None);

        builder.seal_all();

        let mut func = builder.build();
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(&func);
        CriticalEdgeSplitter::new(&isa).run(&mut func, &mut cfg);

        assert_eq!(
            dump_func(&func),
            "func %test_func():
    block0:
        br 1.i32 block3 block1;

    block1:
        jump block2;

    block2:
        return;

    block3:
        jump block2;

"
        );

        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(&func);
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn critical_edge_to_same_block() {
        let isa = build_test_isa();
        let mut builder = func_builder(&[], None, &isa);

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
        builder.ret(None);

        builder.switch_to_block(e);
        builder.ret(None);

        builder.seal_all();

        let mut func = builder.build();
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(&func);
        CriticalEdgeSplitter::new(&isa).run(&mut func, &mut cfg);

        assert_eq!(
            dump_func(&func),
            "func %test_func():
    block0:
        br 1.i8 block5 block1;

    block1:
        jump block2;

    block2:
        br 1.i8 block4 block6;

    block3:
        return;

    block4:
        return;

    block5:
        jump block3;

    block6:
        jump block3;

"
        );

        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(&func);
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    fn critical_edge_phi() {
        let isa = build_test_isa();
        let mut builder = func_builder(&[], None, &isa);

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
        builder.ret(None);

        builder.seal_all();

        let mut func = builder.build();
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(&func);
        CriticalEdgeSplitter::new(&isa).run(&mut func, &mut cfg);

        assert_eq!(
            dump_func(&func),
            "func %test_func():
    block0:
        jump block1;

    block1:
        v1.i8 = phi (1.i8 block0) (v2 block3);
        v2.i8 = add v1 1.i8;
        br v1 block2 block3;

    block2:
        return;

    block3:
        jump block1;

"
        );

        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(&func);
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    fn critical_edge_br_table() {
        let isa = build_test_isa();
        let mut builder = func_builder(&[], None, &isa);

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let e = builder.append_block();

        builder.switch_to_block(a);
        let cond = builder.make_imm_value(true);
        builder.br(cond, b, e);

        builder.switch_to_block(b);
        let v0 = builder.make_imm_value(0i32);
        let v1 = builder.make_imm_value(1i32);
        let v2 = builder.make_imm_value(2i32);
        builder.br_table(v0, Some(c), &[(v1, d), (v2, e)]);

        builder.switch_to_block(c);
        builder.jump(b);

        builder.switch_to_block(d);
        builder.ret(None);

        builder.switch_to_block(e);
        builder.ret(None);

        builder.seal_all();

        let mut func = builder.build();
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(&func);
        CriticalEdgeSplitter::new(&isa).run(&mut func, &mut cfg);

        assert_eq!(
            dump_func(&func),
            "func %test_func():
    block0:
        br -1.i1 block5 block6;

    block1:
        br_table 0.i32 block2 (1.i32 block3) (2.i32 block7);

    block2:
        jump block1;

    block3:
        return;

    block4:
        return;

    block5:
        jump block1;

    block6:
        jump block4;

    block7:
        jump block4;

"
        );

        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(&func);
        assert_eq!(cfg, cfg_split);
    }
}
