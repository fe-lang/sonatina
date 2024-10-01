use sonatina_ir::{
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::control_flow::{Branch, Jump},
    BlockId, ControlFlowGraph, Function, InstId,
};

#[derive(Debug)]
pub struct CriticalEdgeSplitter {
    critical_edges: Vec<CriticalEdge>,
}

impl Default for CriticalEdgeSplitter {
    fn default() -> Self {
        Self::new()
    }
}

impl CriticalEdgeSplitter {
    pub fn new() -> Self {
        Self {
            critical_edges: Vec::default(),
        }
    }

    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) {
        self.clear();

        for block in func.layout.iter_block() {
            if let Some(last_inst) = func.layout.last_inst_of(block) {
                self.add_critical_edges(last_inst, func, cfg);
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

    fn add_critical_edges(&mut self, inst_id: InstId, func: &Function, cfg: &ControlFlowGraph) {
        let Some(branch_info) = func.dfg.branch_info(inst_id) else {
            return;
        };

        if branch_info.num_dests() < 2 {
            return;
        }

        for dest in branch_info.dests() {
            if cfg.pred_num_of(dest) > 1 {
                self.critical_edges.push(CriticalEdge::new(inst_id, dest));
            }
        }
    }

    fn split_edge(&mut self, edge: CriticalEdge, func: &mut Function, cfg: &mut ControlFlowGraph) {
        let inst = edge.inst;
        let original_dest = edge.to;
        let source_block = func.layout.inst_block(inst);

        // Create a new block that contains only a jump inst to the destinating block of
        // the critical edge.
        let inserted_dest = func.dfg.make_block();
        let jump = Jump::new(func.dfg.inst_set().jump(), original_dest);
        let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(original_dest));
        cursor.append_block(func, inserted_dest);
        cursor.set_location(CursorLocation::BlockTop(inserted_dest));
        cursor.append_inst_data(func, jump);

        // Rewrite branch destination to the new block.
        func.dfg
            .rewrite_branch_dest(inst, original_dest, inserted_dest);
        self.modify_cfg(cfg, source_block, original_dest, inserted_dest);
        self.modify_phi_blocks(func, original_dest, inserted_dest);
    }

    fn modify_phi_blocks(
        &self,
        func: &mut Function,
        original_dest: BlockId,
        inserted_dest: BlockId,
    ) {
        for inst in func.layout.iter_inst(original_dest) {
            let Some(phi) = func.dfg.cast_phi_mut(inst) else {
                continue;
            };

            for (_, block) in phi.args_mut() {
                if *block == original_dest {
                    *block = inserted_dest;
                }
            }
        }
    }

    fn modify_cfg(
        &self,
        cfg: &mut ControlFlowGraph,
        source_block: BlockId,
        original_dest: BlockId,
        inserted_dest: BlockId,
    ) {
        cfg.remove_edge(source_block, original_dest);
        cfg.add_edge(source_block, inserted_dest);
        cfg.add_edge(inserted_dest, original_dest);
    }
}

#[derive(Debug)]
struct CriticalEdge {
    inst: InstId,
    to: BlockId,
}

impl CriticalEdge {
    fn new(inst: InstId, to: BlockId) -> Self {
        Self { inst, to }
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        builder::test_util::*,
        inst::{
            arith::Add,
            control_flow::{Br, BrTable, Phi, Return},
        },
        isa::Isa,
        Type,
    };

    use super::*;

    #[test]
    fn critical_edge_basic() {
        let (evm, mut builder) = test_func_builder(&[], Type::Void);
        let is = evm.inst_set();

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.make_imm_value(1i32);
        let br = Br::new(is, v0, c, b);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(b);
        let jump = Jump::new(is, c);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(c);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        let mut module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &mut module.funcs[func_ref];
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(func);
        CriticalEdgeSplitter::new().run(func, &mut cfg);

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() -> void {
    block0:
        br 1.i32 block3 block1;

    block1:
        jump block2;

    block2:
        return;

    block3:
        jump block2;

}
"
        );

        let func = &mut module.funcs[func_ref];
        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(func);
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn critical_edge_to_same_block() {
        let (evm, mut builder) = test_func_builder(&[], Type::Void);
        let is = evm.inst_set();

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let e = builder.append_block();

        builder.switch_to_block(a);
        let v0 = builder.make_imm_value(1i8);
        let br = Br::new(is, v0, d, b);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(b);
        let jump = Jump::new(is, c);
        builder.insert_inst_no_result(jump);

        builder.switch_to_block(c);
        let br = Br::new(is, v0, e, d);
        builder.insert_inst_no_result(br);

        builder.switch_to_block(d);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);

        builder.switch_to_block(e);
        let ret = Return::new(is, None);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        let mut module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &mut module.funcs[func_ref];
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(func);
        CriticalEdgeSplitter::new().run(func, &mut cfg);

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() -> void {
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

}
"
        );

        let func = &mut module.funcs[func_ref];
        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(func);
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    fn critical_edge_phi() {
        let (evm, mut builder) = test_func_builder(&[], Type::Void);
        let is = evm.inst_set();

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();

        builder.switch_to_block(a);
        let v1 = builder.make_imm_value(1i8);
        builder.insert_inst_no_result_with(|| Jump::new(is, b));

        builder.switch_to_block(b);
        let phi_res = builder.insert_inst_with(|| Phi::new(is, vec![(v1, a)], Type::I8), Type::I8);
        let add_res = builder.insert_inst_with(|| Add::new(is, phi_res, v1), Type::I8);

        builder.append_phi_arg(phi_res, add_res, b);
        builder.insert_inst_no_result_with(|| Br::new(is, phi_res, c, b));

        builder.switch_to_block(c);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();
        let mut module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &mut module.funcs[func_ref];
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(func);
        CriticalEdgeSplitter::new().run(func, &mut cfg);

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() -> void {
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

}
"
        );

        let func = &mut module.funcs[func_ref];
        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(func);
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    fn critical_edge_br_table() {
        let (evm, mut builder) = test_func_builder(&[], Type::Void);
        let is = evm.inst_set();

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();
        let d = builder.append_block();
        let e = builder.append_block();

        builder.switch_to_block(a);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b, e));

        builder.switch_to_block(b);
        let v0 = builder.make_imm_value(0i32);
        let v1 = builder.make_imm_value(1i32);
        let v2 = builder.make_imm_value(2i32);
        builder
            .insert_inst_no_result_with(|| BrTable::new(is, v0, Some(c), vec![(v1, d), (v2, e)]));

        builder.switch_to_block(c);
        builder.insert_inst_no_result_with(|| Jump::new(is, b));

        builder.switch_to_block(d);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.switch_to_block(e);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();
        let mut module = builder.finish().build();
        let func_ref = module.iter_functions().next().unwrap();
        let func = &mut module.funcs[func_ref];
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(func);
        CriticalEdgeSplitter::new().run(func, &mut cfg);

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() -> void {
    block0:
        br 1.i1 block5 block6;

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

}
"
        );

        let func = &mut module.funcs[func_ref];
        let mut cfg_split = ControlFlowGraph::default();
        cfg_split.compute(func);
        assert_eq!(cfg, cfg_split);
    }
}
