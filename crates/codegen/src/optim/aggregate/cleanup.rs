use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
};

#[derive(Default)]
pub(crate) struct DeadPureInstCleanup {
    worklist: Vec<InstId>,
    queued: FxHashSet<InstId>,
}

impl DeadPureInstCleanup {
    pub(crate) fn run_with_current_users(&mut self, func: &mut Function) -> bool {
        self.worklist.clear();
        self.queued.clear();
        for block in func.layout.iter_block() {
            let mut next_inst = func.layout.first_inst_of(block);
            while let Some(inst) = next_inst {
                next_inst = func.layout.next_inst_of(inst);
                if is_dead_pure_inst(func, inst) && self.queued.insert(inst) {
                    self.worklist.push(inst);
                }
            }
        }

        let mut changed = false;
        while let Some(inst) = self.worklist.pop() {
            if !is_dead_pure_inst(func, inst) {
                continue;
            }

            let operands = inst_operands(func, inst);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            changed = true;

            for operand in operands {
                let Some(def_inst) = func.dfg.value_inst(operand) else {
                    continue;
                };
                if self.queued.insert(def_inst) {
                    self.worklist.push(def_inst);
                }
            }
        }

        changed
    }
}

fn is_dead_pure_inst(func: &Function, inst: InstId) -> bool {
    if !func.layout.is_inst_inserted(inst) || func.dfg.side_effect(inst).has_effect() {
        return false;
    }

    let Some(result) = func.dfg.inst_result(inst) else {
        return false;
    };

    !func
        .dfg
        .users(result)
        .copied()
        .any(|user| func.layout.is_inst_inserted(user))
}

fn inst_operands(func: &Function, inst: InstId) -> SmallVec<[ValueId; 8]> {
    let mut operands = SmallVec::new();
    func.dfg
        .inst(inst)
        .for_each_value(&mut |value| operands.push(value));
    operands
}
