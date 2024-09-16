//! This module contains a solver for instruction simplification.

use std::collections::VecDeque;

use sonatina_ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    Function, Insn, InsnData, ValueId,
};

use super::simplify_impl::{simplify_insn, SimplifyResult};

#[derive(Debug)]
pub struct InsnSimplifySolver {
    worklist: VecDeque<Insn>,
}

impl InsnSimplifySolver {
    pub fn new() -> Self {
        Self {
            worklist: VecDeque::default(),
        }
    }

    pub fn run(&mut self, func: &mut Function) {
        let entry = match func.layout.entry_block() {
            Some(entry) => entry,
            None => return,
        };
        let mut inserter = InsnInserter::at_location(CursorLocation::BlockTop(entry));

        while inserter.loc() != CursorLocation::NoWhere {
            let insn = match inserter.insn() {
                Some(insn) => insn,
                None => {
                    inserter.proceed(func);
                    continue;
                }
            };

            self.simplify(func, &mut inserter, insn);
        }

        while let Some(insn) = self.worklist.pop_front() {
            if !func.layout.is_insn_inserted(insn) {
                continue;
            }

            inserter.set_location(CursorLocation::At(insn));
            self.simplify(func, &mut inserter, insn);
        }
    }

    pub fn simplify(&mut self, func: &mut Function, inserter: &mut InsnInserter, insn: Insn) {
        match simplify_insn(&mut func.dfg, insn) {
            Some(SimplifyResult::Value(val)) => {
                self.replace_insn_with_value(func, inserter, insn, val)
            }

            Some(SimplifyResult::Insn(data)) => {
                self.replace_insn_with_data(func, inserter, insn, data);
            }

            None => inserter.proceed(func),
        }
    }

    pub fn clear(&mut self) {
        self.worklist.clear();
    }

    pub fn replace_insn_with_value(
        &mut self,
        func: &mut Function,
        inserter: &mut InsnInserter,
        insn: Insn,
        value: ValueId,
    ) {
        if let Some(insn_result) = func.dfg.insn_result(insn) {
            self.worklist.extend(func.dfg.users(insn_result).copied());
            self.worklist.push_back(insn);
            func.dfg.change_to_alias(insn_result, value);
        };

        inserter.remove_insn(func);
    }

    pub fn replace_insn_with_data(
        &mut self,
        func: &mut Function,
        inserter: &mut InsnInserter,
        insn: Insn,
        data: InsnData,
    ) {
        if let Some(res) = func.dfg.insn_result(insn) {
            self.worklist.extend(func.dfg.users(res).copied());
            self.worklist.push_back(insn);
        }

        inserter.replace(func, data);
        inserter.proceed(func);
    }
}

impl Default for InsnSimplifySolver {
    fn default() -> Self {
        Self::new()
    }
}
