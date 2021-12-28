//! This module contains a solver for `Aggressive Dead code elimination (ADCE)`.

use cranelift_entity::SecondaryMap;
use std::collections::BTreeSet;

use crate::{
    ir::func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    ir::insn::InsnData,
    post_domtree::{PDFSet, PDTIdom, PostDomTree},
    Block, Function, Insn,
};

#[derive(Default)]
pub struct AdceSolver {
    live_insns: SecondaryMap<Insn, bool>,
    live_blocks: SecondaryMap<Block, bool>,
    empty_blocks: BTreeSet<Block>,
    post_domtree: PostDomTree,
    worklist: Vec<Insn>,
}

impl AdceSolver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn clear(&mut self) {
        self.live_insns.clear();
        self.live_blocks.clear();
        self.empty_blocks.clear();
        self.post_domtree.clear();
        self.worklist.clear();
    }

    pub fn run(&mut self, func: &mut Function) {
        while self.run_dce(func) {}
    }

    /// Returns `true` if branch insn is modified while dead code elimination.
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
            for insn in func.layout.iter_insn(block) {
                if func.dfg.has_side_effect(insn) {
                    self.mark_insn(func, insn);
                }
            }
        }

        while let Some(insn) = self.worklist.pop() {
            self.mark_by_insn(func, insn, &pdf_set);
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

    fn mark_insn(&mut self, func: &Function, insn: Insn) {
        let mut mark_insn = |insn, block| {
            if !self.does_insn_live(insn) {
                self.live_insns[insn] = true;
                self.worklist.push(insn);
                self.mark_block(block);
                true
            } else {
                false
            }
        };

        let insn_block = func.layout.insn_block(insn);
        if mark_insn(insn, insn_block) {
            let last_insn = func.layout.last_insn_of(insn_block).unwrap();
            mark_insn(last_insn, insn_block);
        }
    }

    fn mark_block(&mut self, block: Block) {
        self.live_blocks[block] = true;
    }

    fn does_insn_live(&self, insn: Insn) -> bool {
        self.live_insns[insn]
    }

    fn does_block_live(&self, block: Block) -> bool {
        self.live_blocks[block]
    }

    fn mark_by_insn(&mut self, func: &Function, insn: Insn, pdf_set: &PDFSet) {
        for &value in func.dfg.insn_args(insn) {
            if let Some(value_insn) = func.dfg.value_insn(value) {
                self.mark_insn(func, value_insn);
            }
        }

        let insn_block = func.layout.insn_block(insn);
        for &block in pdf_set.frontiers(insn_block) {
            if let Some(last_insn) = func.layout.last_insn_of(block) {
                self.mark_insn(func, last_insn)
            }
        }
    }

    fn eliminate_dead_code(&mut self, func: &mut Function) -> bool {
        let entry = if let Some(entry) = func.layout.entry_block() {
            entry
        } else {
            return false;
        };

        let mut inserter = InsnInserter::new(func, CursorLocation::BlockTop(entry));
        loop {
            match inserter.loc() {
                CursorLocation::At(insn) => {
                    if self.does_insn_live(insn) {
                        inserter.proceed();
                    } else {
                        inserter.remove_insn()
                    }
                }

                CursorLocation::BlockTop(block) => {
                    if self.does_block_live(block) {
                        inserter.proceed()
                    } else {
                        inserter.remove_block()
                    }
                }

                CursorLocation::BlockBottom(_) => {
                    inserter.proceed();
                }

                CursorLocation::NoWhere => break,
            }
        }

        // Modify branch insns to remove unreachable edges.
        inserter.set_to_entry();
        let mut br_insn_modified = false;
        while let Some(block) = inserter.block() {
            br_insn_modified |= self.modify_branch(&mut inserter, block);
            inserter.proceed_block();
        }

        br_insn_modified
    }

    fn living_post_dom(&self, mut block: Block) -> Option<Block> {
        loop {
            let idom = self.post_domtree.idom_of(block)?;
            match idom {
                PDTIdom::Real(block) if self.does_block_live(block) => return Some(block),
                PDTIdom::Real(post_dom) => block = post_dom,
                PDTIdom::DummyExit(_) | PDTIdom::DummyEntry(_) => return None,
            }
        }
    }

    /// Returns `true` if branch insn is modified.
    fn modify_branch(&self, inserter: &mut InsnInserter, block: Block) -> bool {
        let last_insn = match inserter.func().layout.last_insn_of(block) {
            Some(insn) => insn,
            None => return false,
        };
        inserter.set_loc(CursorLocation::At(last_insn));

        let dests: Vec<_> = inserter
            .func()
            .dfg
            .analyze_branch(last_insn)
            .iter_dests()
            .collect();

        let mut changed = false;
        for dest in dests {
            if self.does_block_live(dest) {
                continue;
            }

            match self.living_post_dom(dest) {
                // If the destination is dead but its post dominator is living, then change the
                // destination to the post dominator.
                Some(postdom) => inserter
                    .func_mut()
                    .dfg
                    .rewrite_branch_dest(last_insn, dest, postdom),

                // If the block doesn't have post dominator, then remove the dest.
                None => {
                    inserter.func_mut().dfg.remove_branch_dest(last_insn, dest);
                }
            }

            changed = true;
        }

        // Turn branch insn to `jump` if all dests is the same.
        let branch_info = inserter.func().dfg.analyze_branch(last_insn);
        if branch_info.dests_num() > 1 {
            let mut branch_dests = branch_info.iter_dests();
            let first_dest = branch_dests.next().unwrap();
            if branch_dests.all(|dest| dest == first_dest) {
                changed = true;
                inserter.replace(InsnData::jump(first_dest));
            }
        }

        changed
    }
}
