// TODO: Add control flow hoisting.
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    BlockId, ControlFlowGraph, Function, InstId, ValueId,
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
                let preheader = self.create_preheader(func, cfg, lpt, lp);
                self.hoist_invariants(func, preheader);
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
        inst.visit_values(&mut |value| invariant &= loop_var.contains(&value));
        invariant
    }

    /// Returns `true` if the `inst` is safe to hoist.
    fn is_safe_to_hoist(&self, func: &Function, inst_id: InstId) -> bool {
        !(func.dfg.has_side_effect(inst_id)
            || func.dfg.is_branch(inst_id)
            || func.dfg.is_phi(inst_id))
    }

    /// Returns preheader of the loop.
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
    ) -> BlockId {
        let lp_header = lpt.loop_header(lp);
        let original_preheaders: Vec<BlockId> = cfg
            .preds_of(lp_header)
            .copied()
            .filter(|block| !lpt.is_in_loop(*block, lp))
            .collect();

        // If the loop header already has a single preheader and the edge is not a
        // critical edge, then it's possible to use the preheader as is.
        if original_preheaders.len() == 1 && cfg.succs_of(original_preheaders[0]).count() == 1 {
            return original_preheaders[0];
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

        new_preheader
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
        // Record inserted phis to avoid duplication of the same phi.
        let mut inserted_phis = FxHashMap::default();

        let mut next_inst = func.layout.first_inst_of(lp_header);
        while let Some(phi_inst_id) = next_inst {
            if func.dfg.cast_phi(phi_inst_id).is_none() {
                break;
            };

            // Create new phi inst that should be inserted to the preheader, and remove inst
            // arguments passing through original preheaders.
            let mut new_phi = func.dfg.make_phi(vec![]);
            let old_phi = func.dfg.cast_phi_mut(phi_inst_id).unwrap();

            for &block in original_preheaders {
                // Remove an argument.
                let value = old_phi.remove_phi_arg(block).unwrap();
                // Add an argument to newly inserted phi inst.
                new_phi.append_phi_arg(value, block);
            }

            let phi_result = match inserted_phis.get(&phi_inst_id) {
                // If the same phi is already inserted in the preheader, reuse its result.
                Some(&value) => value,

                // Insert new phi to the preheader if there is no same phi in the preheader.
                None => {
                    // Insert new phi inst to the preheader.
                    let mut inserter =
                        InstInserter::at_location(CursorLocation::BlockTop(new_preheader));
                    let new_phi_inst = inserter.insert_inst_data(func, new_phi.clone());
                    let ty = func.dfg.value_ty(new_phi.args()[0].0);
                    let result = inserter.make_result(func, new_phi_inst, ty);
                    inserter.attach_result(func, new_phi_inst, result);

                    // Add phi_inst_data to `inserted_phis` for reusing.
                    inserted_phis.insert(new_phi_inst, result);

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
