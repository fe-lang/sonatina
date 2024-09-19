// TODO: Add control flow hoisting.
use rustc_hash::{FxHashMap, FxHashSet};

use crate::loop_analysis::{Loop, LoopTree};

use sonatina_ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    BlockId, ControlFlowGraph, Function, Insn, InsnData, ValueId,
};

#[derive(Debug)]
pub struct LicmSolver {
    invariants: Vec<Insn>,
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
            for insn in func.layout.iter_inst(block) {
                if self.is_invariant(func, &loop_var, insn) {
                    self.invariants.push(insn);
                } else if let Some(result) = func.dfg.insn_result(insn) {
                    loop_var.insert(result);
                }
            }
        }
    }

    /// Returns `true` if the insn is loop invariant.
    fn is_invariant(&self, func: &Function, loop_var: &FxHashSet<ValueId>, insn: Insn) -> bool {
        if !self.is_safe_to_hoist(func, insn) {
            return false;
        }

        for arg in func.dfg.insn_args(insn) {
            if loop_var.contains(arg) {
                return false;
            }
        }

        true
    }

    /// Returns `true` if the `insn` is safe to hoist.
    fn is_safe_to_hoist(&self, func: &Function, insn: Insn) -> bool {
        !(func.dfg.has_side_effect(insn)
            || func.dfg.is_branch(insn)
            || func.dfg.may_trap(insn)
            || func.dfg.is_phi(insn))
    }

    /// Returns preheader of the loop.
    /// 1. If there is natural preheader for the loop, then returns it without any modification of
    ///    function.
    /// 2. If no natural preheader for the loop, then create the preheader and modify function
    ///    layout, `cfg`, and `lpt`.
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

        // If the loop header already has a single preheader and the edge is not a critical edge,
        // then it's possible to use the preheader as is.
        if original_preheaders.len() == 1 && cfg.succs_of(original_preheaders[0]).count() == 1 {
            return original_preheaders[0];
        }

        // Create preheader and insert it before the loop header.
        let new_preheader = func.dfg.make_block();
        let mut inserter = InsnInserter::at_location(CursorLocation::BlockTop(lp_header));
        inserter.insert_block_before(func, new_preheader);

        // Insert jump insn of which destination is the loop header.
        inserter.set_location(CursorLocation::BlockTop(new_preheader));
        inserter.insert_insn_data(func, InsnData::jump(lp_header));
        cfg.add_edge(new_preheader, lp_header);

        // Rewrite branch destination of original preheaders and modify cfg.
        for block in original_preheaders.iter().copied() {
            let last_insn = func.layout.last_inst_of(block).unwrap();
            func.dfg
                .rewrite_branch_dest(last_insn, lp_header, new_preheader);
            cfg.remove_edge(block, lp_header);
            cfg.add_edge(block, new_preheader);
        }

        self.modify_phi_insn(func, lp_header, &original_preheaders, new_preheader);

        // Map new preheader to the parent loop if exists.
        if let Some(parent_lp) = lpt.parent_loop(lp) {
            lpt.map_block(new_preheader, parent_lp);
        }

        new_preheader
    }

    /// Hoist invariants to the preheader.
    fn hoist_invariants(&self, func: &mut Function, preheader: BlockId) {
        let last_insn = func.layout.last_inst_of(preheader).unwrap();
        for invariant in self.invariants.iter().copied() {
            func.layout.remove_inst(invariant);
            func.layout.insert_inst_before(invariant, last_insn);
        }
    }

    // Modify phi insns in loop header.
    fn modify_phi_insn(
        &self,
        func: &mut Function,
        lp_header: BlockId,
        original_preheaders: &[BlockId],
        new_preheader: BlockId,
    ) {
        // Record inserted phis to avoid duplication of the same phi.
        let mut inserted_phis = FxHashMap::default();

        let mut next_insn = func.layout.first_inst_of(lp_header);
        while let Some(insn) = next_insn {
            if !func.dfg.is_phi(insn) {
                break;
            }

            // Create new phi insn that should be inserted to the preheader, and remove insn
            // arguments passing through original preheaders.
            let mut phi_insn_data = InsnData::phi(func.dfg.insn_result_ty(insn).unwrap());
            for &block in original_preheaders {
                // Remove an argument.
                let value = func.dfg.remove_phi_arg(insn, block);
                // Add an argument to newly inserted phi insn.
                phi_insn_data.append_phi_arg(value, block);
            }

            let phi_result = match inserted_phis.get(&phi_insn_data) {
                // If the same phi is already inserted in the preheader, reuse its result.
                Some(&value) => value,

                // Insert new phi to the preheader if there is no same phi in the preheader.
                None => {
                    // Insert new phi insn to the preheader.
                    let mut inserter =
                        InsnInserter::at_location(CursorLocation::BlockTop(new_preheader));
                    let new_phi_insn = inserter.insert_insn_data(func, phi_insn_data.clone());
                    let result = inserter.make_result(func, new_phi_insn).unwrap();
                    inserter.attach_result(func, new_phi_insn, result);

                    // Add phi_insn_data to `inserted_phis` for reusing.
                    inserted_phis.insert(phi_insn_data, result);

                    result
                }
            };

            // Append the result of new phi insn.
            func.dfg.append_phi_arg(insn, phi_result, new_preheader);

            next_insn = func.layout.next_inst_of(insn);
        }
    }
}

impl Default for LicmSolver {
    fn default() -> Self {
        Self::new()
    }
}
