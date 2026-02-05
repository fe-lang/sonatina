// TODO: Add control flow hoisting.
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
};

use crate::loop_analysis::{Loop, LoopTree};

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

        let is_entry_header = func.layout.entry_block() == Some(lp_header);
        let header_starts_with_phi = func
            .layout
            .first_inst_of(lp_header)
            .is_some_and(|inst| func.dfg.is_phi(inst));
        if original_preheaders.is_empty() && (!is_entry_header || header_starts_with_phi) {
            return None;
        }

        // If the loop header already has a single preheader and the edge is not a
        // critical edge, then it's possible to use the preheader as is.
        if original_preheaders.len() == 1 && cfg.succs_of(original_preheaders[0]).count() == 1 {
            return Some(original_preheaders[0]);
        }

        // Create preheader and insert it before the loop header.
        let new_preheader = func.dfg.make_block();
        let mut inserter = InstInserter::at_location(CursorLocation::BlockTop(lp_header));
        inserter.insert_block_before(func, new_preheader);

        // Insert jump inst of which destination is the loop header.
        inserter.set_location(CursorLocation::BlockTop(new_preheader));
        let jump_inst = func.dfg.make_jump(lp_header);
        inserter.insert_inst_data(func, jump_inst);
        cfg.add_edge(new_preheader, lp_header);

        // Rewrite branch destination of original preheaders and modify cfg.
        for block in original_preheaders.iter().copied() {
            let last_inst = func.layout.last_inst_of(block).unwrap();
            func.dfg
                .rewrite_branch_dest(last_inst, lp_header, new_preheader);
            cfg.remove_edge(block, lp_header);
            cfg.add_edge(block, new_preheader);
        }

        self.modify_phi_inst(func, lp_header, &original_preheaders, new_preheader);

        // Map new preheader to the parent loop if exists.
        if let Some(parent_lp) = lpt.parent_loop(lp) {
            lpt.map_block(new_preheader, parent_lp);
        }

        Some(new_preheader)
    }

    /// Hoist invariants to the preheader.
    fn hoist_invariants(&self, func: &mut Function, preheader: BlockId) {
        let last_inst = func.layout.last_inst_of(preheader).unwrap();
        for invariant in self.invariants.iter().copied() {
            func.layout.remove_inst(invariant);
            func.layout.insert_inst_before(invariant, last_inst);
        }
    }

    // Modify phi insts in loop header.
    fn modify_phi_inst(
        &self,
        func: &mut Function,
        lp_header: BlockId,
        original_preheaders: &[BlockId],
        new_preheader: BlockId,
    ) {
        if original_preheaders.is_empty() {
            return;
        }

        // Record inserted phis to avoid duplication of the same phi.
        let mut inserted_phis = FxHashMap::default();

        let mut next_inst = func.layout.first_inst_of(lp_header);
        while let Some(phi_inst_id) = next_inst {
            if func.dfg.cast_phi(phi_inst_id).is_none() {
                break;
            };

            let phi_result = func
                .dfg
                .inst_result(phi_inst_id)
                .unwrap_or_else(|| panic!("phi {phi_inst_id:?} has no result"));
            let phi_ty = func.dfg.value_ty(phi_result);

            // Create new phi inst that should be inserted to the preheader, and remove inst
            // arguments passing through original preheaders.
            let mut new_phi = func.dfg.make_phi(vec![]);
            func.dfg.untrack_inst(phi_inst_id);
            let old_phi = func.dfg.cast_phi_mut(phi_inst_id).unwrap();

            for &block in original_preheaders {
                // Remove an argument.
                let value = old_phi.remove_phi_arg(block).unwrap();
                // Add an argument to newly inserted phi inst.
                new_phi.append_phi_arg(value, block);
            }

            let phi_result = match inserted_phis.get(&new_phi) {
                // If the same phi is already inserted in the preheader, reuse its result.
                Some(&value) => value,

                // Insert new phi to the preheader if there is no same phi in the preheader.
                None => {
                    // Insert new phi inst to the preheader.
                    let mut inserter =
                        InstInserter::at_location(CursorLocation::BlockTop(new_preheader));
                    let new_phi_inst = inserter.insert_inst_data(func, new_phi.clone());
                    let result = inserter.make_result(func, new_phi_inst, phi_ty);
                    inserter.attach_result(func, new_phi_inst, result);

                    // Add phi_inst_data to `inserted_phis` for reusing.
                    inserted_phis.insert(new_phi, result);

                    result
                }
            };

            // Append the result of new phi inst.
            func.dfg
                .append_phi_arg(phi_inst_id, phi_result, new_preheader);

            next_inst = func.layout.next_inst_of(phi_inst_id);
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
            assert_eq!(func.layout.iter_block().count(), 3);

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
            assert_eq!(func.layout.iter_block().count(), 3);
        });
    }
}
