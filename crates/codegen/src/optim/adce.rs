//! This module contains a solver for `Aggressive Dead code elimination (ADCE)`.

use cranelift_entity::SecondaryMap;
use std::collections::BTreeSet;

use crate::post_domtree::{PDFSet, PDTIdom, PostDomTree};

use sonatina_ir::{
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    BlockId, Function, InstId,
};

pub struct AdceSolver {
    live_insts: SecondaryMap<InstId, bool>,
    live_blocks: SecondaryMap<BlockId, bool>,
    empty_blocks: BTreeSet<BlockId>,
    post_domtree: PostDomTree,
    worklist: Vec<InstId>,
}

impl AdceSolver {
    pub fn new() -> Self {
        Self {
            live_insts: SecondaryMap::default(),
            live_blocks: SecondaryMap::default(),
            empty_blocks: BTreeSet::default(),
            post_domtree: PostDomTree::default(),
            worklist: Vec::default(),
        }
    }

    pub fn clear(&mut self) {
        self.live_insts.clear();
        self.live_blocks.clear();
        self.empty_blocks.clear();
        self.post_domtree.clear();
        self.worklist.clear();
    }

    pub fn run(&mut self, func: &mut Function) {
        while self.run_dce(func) {}
    }

    /// Returns `true` if branch inst is modified while dead code elimination.
    fn run_dce(&mut self, func: &mut Function) -> bool {
        self.clear();

        self.post_domtree.compute(func);
        let pdf_set = self.post_domtree.compute_df();

        // TODO: We should remove this restriction.
        // ref: <https://reviews.llvm.org/D35851>
        if self.has_infinite_loop(func) {
            return false;
        }

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if func.dfg.has_side_effect(inst) {
                    self.mark_inst(func, inst);
                }
            }
        }

        while let Some(inst) = self.worklist.pop() {
            self.mark_by_inst(func, inst, &pdf_set);
        }

        self.eliminate_dead_code(func)
    }

    fn has_infinite_loop(&self, func: &Function) -> bool {
        for block in func.layout.iter_block() {
            if !self.post_domtree.is_reachable(block) {
                return true;
            }
        }

        false
    }

    fn mark_inst(&mut self, func: &Function, inst: InstId) {
        let mut mark_inst = |inst, block| {
            if !self.does_inst_live(inst) {
                self.live_insts[inst] = true;
                self.worklist.push(inst);
                self.mark_block(block);
                true
            } else {
                false
            }
        };

        let inst_block = func.layout.inst_block(inst);
        if mark_inst(inst, inst_block) {
            let last_inst = func.layout.last_inst_of(inst_block).unwrap();
            mark_inst(last_inst, inst_block);
        }
    }

    fn mark_block(&mut self, block: BlockId) {
        self.live_blocks[block] = true;
    }

    fn does_inst_live(&self, inst: InstId) -> bool {
        self.live_insts[inst]
    }

    fn does_block_live(&self, block: BlockId) -> bool {
        self.live_blocks[block]
    }

    fn mark_by_inst(&mut self, func: &Function, inst_id: InstId, pdf_set: &PDFSet) {
        let inst = func.dfg.inst(inst_id);
        inst.visit_values(&mut |value| {
            if let Some(value_inst) = func.dfg.value_inst(value) {
                self.mark_inst(func, value_inst);
            }
        });

        let inst_block = func.layout.inst_block(inst_id);
        for &block in pdf_set.frontiers(inst_block) {
            if let Some(last_inst) = func.layout.last_inst_of(block) {
                self.mark_inst(func, last_inst)
            }
        }
    }

    fn eliminate_dead_code(&mut self, func: &mut Function) -> bool {
        let entry = if let Some(entry) = func.layout.entry_block() {
            entry
        } else {
            return false;
        };

        let mut inserter = InstInserter::at_location(CursorLocation::BlockTop(entry));
        loop {
            match inserter.loc() {
                CursorLocation::At(inst) => {
                    if self.does_inst_live(inst) {
                        inserter.proceed(func);
                    } else {
                        inserter.remove_inst(func)
                    }
                }

                CursorLocation::BlockTop(block) => {
                    if self.does_block_live(block) {
                        inserter.proceed(func)
                    } else {
                        inserter.remove_block(func)
                    }
                }

                CursorLocation::BlockBottom(_) => {
                    inserter.proceed(func);
                }

                CursorLocation::NoWhere => break,
            }
        }

        // Modify branch insts to remove unreachable edges.
        inserter.set_to_entry(func);
        let mut br_inst_modified = false;
        while let Some(block) = inserter.block(func) {
            br_inst_modified |= self.modify_branch(func, &mut inserter, block);
            inserter.proceed_block(func);
        }

        br_inst_modified
    }

    fn living_post_dom(&self, mut block: BlockId) -> Option<BlockId> {
        loop {
            let idom = self.post_domtree.idom_of(block)?;
            match idom {
                PDTIdom::Real(block) if self.does_block_live(block) => return Some(block),
                PDTIdom::Real(post_dom) => block = post_dom,
                PDTIdom::DummyExit(_) | PDTIdom::DummyEntry(_) => return None,
            }
        }
    }

    /// Returns `true` if branch inst is modified.
    fn modify_branch(
        &self,
        func: &mut Function,
        inserter: &mut InstInserter,
        block: BlockId,
    ) -> bool {
        let last_inst = match func.layout.last_inst_of(block) {
            Some(inst) => inst,
            None => return false,
        };
        inserter.set_location(CursorLocation::At(last_inst));

        let dests: Vec<_> = func
            .dfg
            .branch_info(last_inst)
            .map(|bi| bi.iter_dests().collect())
            .unwrap_or_default();

        let mut changed = false;
        for dest in dests {
            if self.does_block_live(dest) {
                continue;
            }

            match self.living_post_dom(dest) {
                // If the destination is dead but its post dominator is living, then change the
                // destination to the post dominator.
                Some(postdom) => func.dfg.rewrite_branch_dest(last_inst, dest, postdom),

                // If the block doesn't have post dominator, then remove the dest.
                None => {
                    func.dfg.remove_branch_dest(last_inst, dest);
                }
            }

            changed = true;
        }

        // Turn branch inst to `jump` if all dests is the same.
        let Some(branch_info) = func.dfg.branch_info(last_inst) else {
            return changed;
        };
        if branch_info.num_dests() > 1 {
            let mut branch_dests = branch_info.iter_dests();
            let first_dest = branch_dests.next().unwrap();
            if branch_dests.all(|dest| dest == first_dest) {
                changed = true;
                let jump = func.dfg.make_jump(first_dest);
                drop(branch_dests);
                inserter.replace(func, jump);
            }
        }

        changed
    }
}

impl Default for AdceSolver {
    fn default() -> Self {
        Self::new()
    }
}
