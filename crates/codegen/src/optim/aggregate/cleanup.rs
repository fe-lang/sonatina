use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use sonatina_ir::{
    Function, InstId, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
};

pub(crate) fn remove_dead_pure_insts(func: &mut Function) -> bool {
    func.rebuild_users();
    remove_dead_pure_insts_with_current_users(func)
}

pub(crate) fn remove_dead_pure_insts_with_current_users(func: &mut Function) -> bool {
    let mut worklist = Vec::new();
    let mut queued = FxHashSet::default();
    let blocks: Vec<_> = func.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = func.layout.iter_inst(block).collect();
        for inst in insts {
            if is_dead_pure_inst(func, inst) && queued.insert(inst) {
                worklist.push(inst);
            }
        }
    }

    let mut changed = false;
    while let Some(inst) = worklist.pop() {
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
            if queued.insert(def_inst) {
                worklist.push(def_inst);
            }
        }
    }

    changed
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
