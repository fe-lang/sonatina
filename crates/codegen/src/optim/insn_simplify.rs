//! This module contains a solver for instruction simplification.

use std::collections::VecDeque;

use crate::{
    ir::{
        func_cursor::{CursorLocation, FuncCursor, InsnInserter},
        Function, Insn, InsnData, Value,
    },
    TargetIsa,
};

use super::simplify_impl::{simplify_insn, SimplifyResult};

#[derive(Debug)]
pub struct InsnSimplifySolver<'isa> {
    isa: &'isa TargetIsa,
    worklist: VecDeque<Insn>,
}

impl<'isa> InsnSimplifySolver<'isa> {
    pub fn new(isa: &'isa TargetIsa) -> Self {
        Self {
            isa,
            worklist: VecDeque::default(),
        }
    }

    pub fn run(&mut self, func: &mut Function) {
        let entry = match func.layout.entry_block() {
            Some(entry) => entry,
            None => return,
        };
        let mut inserter = InsnInserter::new(func, self.isa, CursorLocation::BlockTop(entry));

        while inserter.loc() != CursorLocation::NoWhere {
            let insn = match inserter.insn() {
                Some(insn) => insn,
                None => {
                    inserter.proceed();
                    continue;
                }
            };

            self.simplify(&mut inserter, insn);
        }

        while let Some(insn) = self.worklist.pop_front() {
            if !inserter.func().layout.is_insn_inserted(insn) {
                continue;
            }

            inserter.set_loc(CursorLocation::At(insn));
            self.simplify(&mut inserter, insn);
        }
    }

    pub fn simplify(&mut self, inserter: &mut InsnInserter, insn: Insn) {
        match simplify_insn(&mut inserter.func_mut().dfg, self.isa, insn) {
            Some(SimplifyResult::Value(val)) => self.replace_insn_with_value(inserter, insn, val),

            Some(SimplifyResult::Insn(data)) => {
                self.replace_insn_with_data(inserter, insn, data);
            }

            None => inserter.proceed(),
        }
    }

    pub fn clear(&mut self) {
        self.worklist.clear();
    }

    pub fn replace_insn_with_value(
        &mut self,
        inserter: &mut InsnInserter,
        insn: Insn,
        value: Value,
    ) {
        if let Some(insn_result) = inserter.func().dfg.insn_result(insn) {
            self.worklist
                .extend(inserter.func().dfg.users(insn_result).copied());
            self.worklist.push_back(insn);
            inserter.func_mut().dfg.change_to_alias(insn_result, value);
        };

        inserter.remove_insn();
    }

    pub fn replace_insn_with_data(
        &mut self,
        inserter: &mut InsnInserter,
        insn: Insn,
        data: InsnData,
    ) {
        if let Some(res) = inserter.func().dfg.insn_result(insn) {
            self.worklist
                .extend(inserter.func().dfg.users(res).copied());
            self.worklist.push_back(insn);
        }

        inserter.replace(data);
        inserter.proceed();
    }
}
