use sonatina_ir::{BlockId, ControlFlowGraph, Function};

use crate::cfg_edit::{CfgEditor, CleanupMode};

#[derive(Debug, Default)]
pub struct CriticalEdgeSplitter;

impl CriticalEdgeSplitter {
    pub fn new() -> Self {
        Self
    }

    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) {
        let mut critical_edges = Vec::<(BlockId, usize)>::new();
        for block in func.layout.iter_block() {
            if cfg.succ_num_of(block) < 2 {
                continue;
            }

            // Preserve the historical destination ordering for ordinary distinct edges so bridge
            // creation does not perturb later fallthrough placement. Parallel slots for one
            // target are still kept distinct and ordered by their branch slot.
            for &to in cfg.succs_of(block) {
                if cfg.pred_num_of(to) < 2 {
                    continue;
                }
                critical_edges.extend(
                    cfg.succ_edges_of(block)
                        .map(|&edge| cfg.edge_data(edge))
                        .filter(|edge| edge.to == to)
                        .map(|edge| (block, edge.branch_slot)),
                );
            }
        }

        if critical_edges.is_empty() {
            return;
        }

        let mut editor = CfgEditor::new(func, CleanupMode::Strict);
        for (from, branch_slot) in critical_edges {
            editor.split_out_edge(from, branch_slot);
        }
        cfg.clone_from(editor.cfg());
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        Type,
        builder::test_util::*,
        inst::{
            arith::Add,
            control_flow::{Br, BrTable, Jump, Phi, Return},
        },
        isa::Isa,
    };
    use sonatina_parser::parse_module;

    use super::*;

    #[test]
    fn critical_edge_basic() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
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
        let ret = Return::new_unit(is);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let mut cfg = ControlFlowGraph::default();
        module.func_store.modify(func_ref, |func| {
            cfg.compute(func);
            CriticalEdgeSplitter::new().run(func, &mut cfg);
        });

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        br 1.i32 block3 block1;

    block1:
        jump block2;

    block3:
        jump block2;

    block2:
        return;
}
"
        );

        let mut cfg_split = ControlFlowGraph::default();
        module
            .func_store
            .view(func_ref, |func| cfg_split.compute(func));
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn critical_edge_to_same_block() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
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
        let ret = Return::new_unit(is);
        builder.insert_inst_no_result(ret);

        builder.switch_to_block(e);
        let ret = Return::new_unit(is);
        builder.insert_inst_no_result(ret);

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let mut cfg = ControlFlowGraph::default();
        module.func_store.modify(func_ref, |func| {
            cfg.compute(func);
            CriticalEdgeSplitter::new().run(func, &mut cfg);
        });

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        br 1.i8 block5 block1;

    block1:
        jump block2;

    block2:
        br 1.i8 block4 block6;

    block5:
        jump block3;

    block6:
        jump block3;

    block3:
        return;

    block4:
        return;
}
"
        );

        let mut cfg_split = ControlFlowGraph::default();
        module
            .func_store
            .view(func_ref, |func| cfg_split.compute(func));
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    fn critical_edge_phi() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();

        builder.switch_to_block(a);
        let v1 = builder.make_imm_value(1i8);
        builder.insert_inst_no_result_with(|| Jump::new(is, b));

        builder.switch_to_block(b);
        let phi_res = builder.insert_inst_with(|| Phi::new(is, vec![(v1, a)]), Type::I8);
        let add_res = builder.insert_inst_with(|| Add::new(is, phi_res, v1), Type::I8);

        builder.append_phi_arg(phi_res, add_res, b);
        builder.insert_inst_no_result_with(|| Br::new(is, phi_res, c, b));

        builder.switch_to_block(c);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let mut cfg = ControlFlowGraph::default();
        module.func_store.modify(func_ref, |func| {
            cfg.compute(func);
            CriticalEdgeSplitter::new().run(func, &mut cfg);
        });
        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        jump block1;

    block3:
        jump block1;

    block1:
        v1.i8 = phi (1.i8 block0) (v2 block3);
        v2.i8 = add v1 1.i8;
        br v1 block2 block3;

    block2:
        return;
}
"
        );

        let mut cfg_split = ControlFlowGraph::default();
        module
            .func_store
            .view(func_ref, |func| cfg_split.compute(func));
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    fn critical_edge_phi_label_update_from_other_pred() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let a = builder.append_block();
        let b = builder.append_block();
        let c = builder.append_block();

        builder.switch_to_block(a);
        let cond = builder.make_imm_value(true);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, c, b));

        builder.switch_to_block(b);
        builder.insert_inst_no_result_with(|| Jump::new(is, c));

        builder.switch_to_block(c);
        let v = builder.make_imm_value(1i8);
        builder.insert_inst_with(|| Phi::new(is, vec![(v, a), (v, b)]), Type::I8);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let mut cfg = ControlFlowGraph::default();
        module.func_store.modify(func_ref, |func| {
            cfg.compute(func);
            CriticalEdgeSplitter::new().run(func, &mut cfg);
        });

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        br 1.i1 block3 block1;

    block1:
        jump block2;

    block3:
        jump block2;

    block2:
        v2.i8 = phi (1.i8 block3) (1.i8 block1);
        return;
}
"
        );
    }

    #[test]
    fn critical_edge_br_table() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
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
        builder.insert_inst_no_result_with(|| Return::new_unit(is));

        builder.switch_to_block(e);
        builder.insert_inst_no_result_with(|| Return::new_unit(is));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        let mut cfg = ControlFlowGraph::default();
        module.func_store.modify(func_ref, |func| {
            cfg.compute(func);
            CriticalEdgeSplitter::new().run(func, &mut cfg);
        });

        assert_eq!(
            dump_func(&module, func_ref),
            "func public %test_func() {
    block0:
        br 1.i1 block5 block6;

    block5:
        jump block1;

    block1:
        br_table 0.i32 block2 (1.i32 block3) (2.i32 block7);

    block2:
        jump block1;

    block3:
        return;

    block6:
        jump block4;

    block7:
        jump block4;

    block4:
        return;
}
"
        );

        let mut cfg_split = ControlFlowGraph::default();
        module
            .func_store
            .view(func_ref, |func| cfg_split.compute(func));
        assert_eq!(cfg, cfg_split);
    }

    #[test]
    fn critical_edge_br_table_splits_duplicate_target_slots_individually() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %f(v0.i1, v1.i8) -> i8 {
block0:
    br v0 block1 block2;

block1:
    br_table v1 block3 (0.i8 block3) (1.i8 block4);

block2:
    jump block3;

block3:
    v2.i8 = phi (7.i8 block1) (9.i8 block2);
    return v2;

block4:
    return 11.i8;
}
"#,
        )
        .expect("module parses");
        let func_ref = parsed.module.funcs()[0];
        parsed.module.func_store.modify(func_ref, |func| {
            let blocks: Vec<_> = func.layout.iter_block().collect();
            let [_, duplicate_pred, other_pred, target, distinct_target] = blocks.as_slice() else {
                panic!("expected five blocks");
            };
            let phi_inst = func.layout.first_inst_of(*target).unwrap();
            let duplicate_incoming = func
                .dfg
                .cast_phi(phi_inst)
                .unwrap()
                .args()
                .iter()
                .find(|(_, pred)| pred == duplicate_pred)
                .unwrap()
                .0;

            let mut cfg = ControlFlowGraph::default();
            cfg.compute(func);
            CriticalEdgeSplitter::new().run(func, &mut cfg);

            let term = func.layout.last_inst_of(*duplicate_pred).unwrap();
            let dests = func.dfg.branch_info(term).unwrap().dests();
            assert_eq!(dests.len(), 3);
            assert_ne!(dests[0], dests[1]);
            assert_eq!(dests[2], *distinct_target);
            assert!(
                dests[..2]
                    .iter()
                    .all(|&mid| { cfg.succs_of(mid).eq(std::iter::once(target)) })
            );

            let phi = func.dfg.cast_phi(phi_inst).unwrap();
            assert_eq!(phi.args().len(), 3);
            assert!(!phi.args().iter().any(|(_, pred)| pred == duplicate_pred));
            assert!(phi.args().iter().any(|(_, pred)| pred == other_pred));
            assert_eq!(
                phi.args()
                    .iter()
                    .filter(|(value, pred)| {
                        *value == duplicate_incoming && *pred != *other_pred
                    })
                    .count(),
                2
            );
        });
    }
}
