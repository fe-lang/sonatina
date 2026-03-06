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
            self.queued.remove(&inst);
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

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{InstDowncast, Module, module::FuncRef};
    use sonatina_parser::parse_module;

    fn parse_test_module(src: &str) -> Module {
        parse_module(src).expect("parse should succeed").module
    }

    fn lookup_func(module: &Module, name: &str) -> FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .expect("function should exist")
    }

    #[test]
    fn dead_pure_cleanup_requeues_transitively_dead_defs() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

func private %f() {
block0:
    v0.i256 = add 1.i256 2.i256;
    v1.i256 = add v0 3.i256;
    v2.i256 = sub v0 4.i256;
    return;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            func.rebuild_users();
            assert!(DeadPureInstCleanup::default().run_with_current_users(func));
        });

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    assert!(
                        <&sonatina_ir::inst::arith::Add as InstDowncast>::downcast(
                            func.inst_set(),
                            func.dfg.inst(inst),
                        )
                        .is_none(),
                        "dead add should be removed"
                    );
                    assert!(
                        <&sonatina_ir::inst::arith::Sub as InstDowncast>::downcast(
                            func.inst_set(),
                            func.dfg.inst(inst),
                        )
                        .is_none(),
                        "dead sub should be removed"
                    );
                }
            }
        });
    }
}
