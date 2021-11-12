//! This module contains a solver for `Aggressive Dead code elimination (ADCE)`.

use cranelift_entity::SecondaryMap;
use std::collections::BTreeSet;

use crate::{
    cfg::ControlFlowGraph,
    ir::func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    ir::insn::{InsnData, JumpOp},
    post_domtree::{PDFSet, PostDomTree},
    Block, Function, Insn,
};

#[derive(Default)]
pub struct AdceSolver {
    marks: SecondaryMap<Insn, bool>,
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
        self.marks.clear();
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
                    self.mark(func, insn);
                }
            }
        }

        while let Some(insn) = self.worklist.pop() {
            self.mark_by_insn(func, insn, &pdf_set);
        }

        self.eliminate_dead_code(func)
    }

    pub fn has_infinite_loop(&self, func: &Function) -> bool {
        for block in func.layout.iter_block() {
            if !self.post_domtree.is_reachable(block) {
                return true;
            }
        }

        false
    }

    fn mark(&mut self, func: &Function, insn: Insn) {
        let mut mark_insn = |insn| {
            if !self.is_marked(insn) {
                self.marks[insn] = true;
                self.worklist.push(insn);
                true
            } else {
                false
            }
        };

        if mark_insn(insn) {
            let insn_block = func.layout.insn_block(insn);
            let last_insn = func.layout.last_insn_of(insn_block).unwrap();
            mark_insn(last_insn);
        }
    }

    fn is_marked(&self, insn: Insn) -> bool {
        self.marks[insn]
    }

    fn mark_by_insn(&mut self, func: &Function, insn: Insn, pdf_set: &PDFSet) {
        for &value in func.dfg.insn_args(insn) {
            if let Some(value_insn) = func.dfg.value_insn(value) {
                self.mark(func, value_insn);
            }
        }

        let insn_block = func.layout.insn_block(insn);
        for &block in pdf_set.frontiers(insn_block) {
            if let Some(last_insn) = func.layout.last_insn_of(block) {
                self.mark(func, last_insn)
            }
        }
    }

    fn eliminate_dead_code(&mut self, func: &mut Function) -> bool {
        let loc = if let Some(entry) = func.layout.first_block() {
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
                    if self.is_marked(insn) {
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
                br_insn_modified |= self.remove_branch_dest(&mut inserter, pred, block);
            }
            inserter.set_loc(CursorLocation::BlockTop(block));
            inserter.remove_block();
        }

        br_insn_modified
    }

    /// Returns `true` if `dest` is removed from predecessor's branch dest.
    fn remove_branch_dest(&self, inserter: &mut InsnInserter, pred: Block, dest: Block) -> bool {
        let last_insn = match inserter.func().layout.last_insn_of(pred) {
            Some(insn) => insn,
            None => return false,
        };

        let insn_data = match *inserter.func().dfg.branch_dests(last_insn) {
            [b1, b2] if b1 == dest => InsnData::Jump {
                code: JumpOp::Jump,
                dests: [b2],
            },
            [b1, b2] if b2 == dest => InsnData::Jump {
                code: JumpOp::Jump,
                dests: [b1],
            },
            _ => unreachable!(),
        };

        inserter.set_loc(CursorLocation::At(last_insn));
        inserter.replace(insn_data);

        true
    }
}
