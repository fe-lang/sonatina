//! This module contains a solver for `Aggressive Dead code elimination (ADCE)`.

use cranelift_entity::SecondaryMap;
use std::collections::BTreeSet;

use crate::{
    cfg::ControlFlowGraph,
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
    cfg: ControlFlowGraph,
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
        self.cfg.clear();
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
        let loc = if let Some(entry) = func.layout.entry_block() {
            CursorLocation::BlockTop(entry)
        } else {
            CursorLocation::NoWhere
        };

        self.cfg.compute(func);
        let mut inserter = InsnInserter::new(func, loc);
        let mut empty_blocks = vec![];
        loop {
            match inserter.loc() {
                CursorLocation::At(insn) => {
                    if self.does_insn_live(insn) {
                        inserter.proceed();
                    } else {
                        inserter.remove_insn()
                    }
                }

                CursorLocation::BlockTop(..) => inserter.proceed(),

                CursorLocation::BlockBottom(block) => {
                    if inserter.func().layout.is_block_empty(block) {
                        empty_blocks.push(block);
                    }
                    inserter.proceed();
                }

                CursorLocation::NoWhere => break,
            }
        }

        let mut br_insn_modified = false;
        for &block in &empty_blocks {
            for &pred in self.cfg.preds_of(block) {
                br_insn_modified |= self.modify_branch(&mut inserter, pred, block);
            }
            inserter.set_loc(CursorLocation::BlockTop(block));
            inserter.remove_block();
        }

        br_insn_modified
    }

    fn post_dom(&self, mut block: Block) -> Option<Block> {
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
    fn modify_branch(&self, inserter: &mut InsnInserter, pred: Block, removed: Block) -> bool {
        if !inserter.func().layout.is_block_inserted(pred) {
            return false;
        }

        if !self.does_block_live(pred) {
            return false;
        }

        let last_insn = match inserter.func().layout.last_insn_of(pred) {
            Some(insn) => insn,
            None => return false,
        };

        inserter.set_loc(CursorLocation::At(last_insn));
        match self.post_dom(removed) {
            Some(postdom) => match inserter.func_mut().dfg.branch_dests_mut(last_insn) {
                [b1, _] if *b1 == removed => *b1 = postdom,
                [_, b2] if *b2 == removed => *b2 = postdom,
                [b1] => *b1 = postdom,
                _ => unreachable!(),
            },

            None => {
                let insn_data = match *inserter.func_mut().dfg.branch_dests(last_insn) {
                    [b1, b2] if b1 == removed => InsnData::jump(b2),
                    [b1, b2] if b2 == removed => InsnData::jump(b1),
                    _ => InsnData::jump(self.post_dom(pred).unwrap()),
                };
                inserter.replace(insn_data);
            }
        }

        match *inserter.func().dfg.branch_dests(last_insn) {
            [b1, b2] if b1 == b2 => inserter.replace(InsnData::jump(b1)),
            _ => {}
        }

        true
    }
}
