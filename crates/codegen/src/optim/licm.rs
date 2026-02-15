// TODO: Add control flow hoisting.
use rustc_hash::FxHashSet;
use sonatina_ir::{BlockId, ControlFlowGraph, Function, InstId, ValueId};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode},
    loop_analysis::{Loop, LoopTree},
};

use super::cfg_cleanup::CfgCleanup;

#[derive(Debug)]
pub struct LicmSolver {
    invariants: Vec<InstId>,
}

impl LicmSolver {
    pub fn new() -> Self {
        Self {
            invariants: Vec::default(),
        }
    }

    pub fn clear(&mut self) {
        self.invariants.clear();
    }

    /// Run loop invariant code motion ont the function.
    /// This method also modifies `cfg` and `lpt` htt
    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph, lpt: &mut LoopTree) {
        for lp in lpt.loops() {
            self.collect_invaliants(func, cfg, lpt, lp);

            if !self.invariants.is_empty() {
                if let Some(preheader) = self.create_preheader(func, cfg, lpt, lp) {
                    self.hoist_invariants(func, preheader);
                }
                self.invariants.clear();
            }
        }

        CfgCleanup::new(CleanupMode::Strict).run_with_cfg(func, cfg);
    }

    /// Collect loop invariants int the `lp`.
    /// The found invariants are inserted to `Self::invariants`.
    fn collect_invaliants(
        &mut self,
        func: &Function,
        cfg: &ControlFlowGraph,
        lpt: &LoopTree,
        lp: Loop,
    ) {
        let mut block_in_loop_rpo: Vec<_> = lpt.iter_blocks_post_order(cfg, lp).collect();
        block_in_loop_rpo.reverse();

        let mut loop_var = FxHashSet::default();
        for block in block_in_loop_rpo {
            for inst in func.layout.iter_inst(block) {
                if self.is_invariant(func, &loop_var, inst) {
                    self.invariants.push(inst);
                } else if let Some(result) = func.dfg.inst_result(inst) {
                    loop_var.insert(result);
                }
            }
        }
    }

    /// Returns `true` if the inst is loop invariant.
    fn is_invariant(
        &self,
        func: &Function,
        loop_var: &FxHashSet<ValueId>,
        inst_id: InstId,
    ) -> bool {
        if !self.is_safe_to_hoist(func, inst_id) {
            return false;
        }

        let mut invariant = true;
        let inst = func.dfg.inst(inst_id);
        inst.for_each_value(&mut |value| invariant &= !loop_var.contains(&value));
        invariant
    }

    /// Returns `true` if the `inst` is safe to hoist.
    fn is_safe_to_hoist(&self, func: &Function, inst_id: InstId) -> bool {
        !(func.dfg.side_effect(inst_id).has_effect()
            || func.dfg.is_branch(inst_id)
            || func.dfg.is_phi(inst_id)
            || func.dfg.is_terminator(inst_id))
    }

    /// Returns preheader of the loop, if one can be used/created.
    /// 1. If there is natural preheader for the loop, then returns it without
    ///    any modification of function.
    /// 2. If no natural preheader for the loop, then create the preheader and
    ///    modify function layout, `cfg`, and `lpt`.
    fn create_preheader(
        &self,
        func: &mut Function,
        cfg: &mut ControlFlowGraph,
        lpt: &mut LoopTree,
        lp: Loop,
    ) -> Option<BlockId> {
        let lp_header = lpt.loop_header(lp);
        let original_preheaders: Vec<BlockId> = cfg
            .preds_of(lp_header)
            .copied()
            .filter(|block| !lpt.is_in_loop(*block, lp))
            .collect();
        let mut editor = CfgEditor::new(func, cfg, CleanupMode::Strict);
        let preheader = editor.create_or_reuse_loop_preheader(lp_header, &original_preheaders)?;

        if !original_preheaders.contains(&preheader)
            && let Some(parent_lp) = lpt.parent_loop(lp)
        {
            lpt.map_block(preheader, parent_lp);
        }

        Some(preheader)
    }

    /// Hoist invariants to the preheader.
    fn hoist_invariants(&self, func: &mut Function, preheader: BlockId) {
        let last_inst = func.layout.last_inst_of(preheader).unwrap();
        for invariant in self.invariants.iter().copied() {
            func.layout.remove_inst(invariant);
            func.layout.insert_inst_before(invariant, last_inst);
        }
    }
}

impl Default for LicmSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        ControlFlowGraph, Type,
        builder::test_util::*,
        inst::{
            arith::Add,
            cmp::Slt,
            control_flow::{Br, Jump, Phi, Return},
        },
        prelude::*,
    };

    use crate::{domtree::DomTree, loop_analysis::LoopTree};

    use super::LicmSolver;

    #[test]
    fn licm_skips_entry_loop_with_phi_and_no_preheader() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I32], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();

        let arg0 = builder.args()[0];

        builder.switch_to_block(b0);
        let v0 = builder.insert_inst_with(|| Phi::new(is, vec![]), Type::I32);
        let c1 = builder.make_imm_value(1i32);
        let invariant = builder.insert_inst_with(|| Add::new(is, arg0, c1), Type::I32);
        builder.insert_inst_no_result_with(|| Jump::new(is, b1));

        builder.switch_to_block(b1);
        let v1 = builder.insert_inst_with(|| Add::new(is, v0, c1), Type::I32);
        let c10 = builder.make_imm_value(10i32);
        let cond = builder.insert_inst_with(|| Slt::new(is, v1, c10), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b0, b2));
        builder.append_phi_arg(v0, v1, b1);

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            let invariant_inst = func.dfg.value_inst(invariant).unwrap();
            assert_eq!(func.layout.entry_block(), Some(b0));
            assert_eq!(func.layout.inst_block(invariant_inst), b0);
            let block_count_before = func.layout.iter_block().count();
            assert_eq!(block_count_before, 3);

            let mut cfg = ControlFlowGraph::default();
            cfg.compute(func);
            let mut domtree = DomTree::default();
            domtree.compute(&cfg);
            let mut lpt = LoopTree::default();
            lpt.compute(&cfg, &domtree);

            let mut solver = LicmSolver::new();
            solver.run(func, &mut cfg, &mut lpt);

            assert_eq!(func.layout.entry_block(), Some(b0));
            assert_eq!(func.layout.inst_block(invariant_inst), b0);
            let block_count_after = func.layout.iter_block().count();
            assert!(block_count_after <= block_count_before);
        });
    }
}
