use sonatina_ir::{
    Function,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
};

pub(crate) fn remove_dead_pure_insts(func: &mut Function) -> bool {
    let mut changed = false;

    loop {
        func.rebuild_users();
        let mut removed_any = false;
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if !func.layout.is_inst_inserted(inst) || func.dfg.side_effect(inst).has_effect() {
                    continue;
                }
                let Some(result) = func.dfg.inst_result(inst) else {
                    continue;
                };
                if func
                    .dfg
                    .users(result)
                    .copied()
                    .any(|user| func.layout.is_inst_inserted(user))
                {
                    continue;
                }

                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                removed_any = true;
                changed = true;
            }
        }

        if !removed_any {
            break;
        }
    }

    changed
}
