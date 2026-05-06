use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use sonatina_ir::{Function, InstId, ValueId};

#[derive(Default)]
pub(crate) struct DeadPureInstCleanup {
    worklist: Vec<InstId>,
    candidates: FxHashSet<InstId>,
    live: FxHashSet<InstId>,
}

impl DeadPureInstCleanup {
    pub(crate) fn run_with_current_users(&mut self, func: &mut Function) -> bool {
        self.worklist.clear();
        self.candidates.clear();
        self.live.clear();

        let mut insts = Vec::new();
        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                insts.push(inst);
                if is_drop_candidate(func, inst) {
                    self.candidates.insert(inst);
                }
            }
        }

        for inst in insts.iter().copied() {
            if !self.candidates.contains(&inst) {
                self.mark_operands_live(func, inst);
            }
        }

        while let Some(inst) = self.worklist.pop() {
            self.mark_operands_live(func, inst);
        }

        let dead_insts: Vec<_> = insts
            .into_iter()
            .filter(|inst| self.candidates.contains(inst) && !self.live.contains(inst))
            .collect();
        if dead_insts.is_empty() {
            return false;
        }

        for &inst in &dead_insts {
            func.layout.remove_inst(inst);
        }
        func.erase_insts(&dead_insts);
        true
    }

    fn mark_operands_live(&mut self, func: &Function, inst: InstId) {
        for operand in inst_operands(func, inst) {
            let Some(def_inst) = func.dfg.value_inst(operand) else {
                continue;
            };
            if self.candidates.contains(&def_inst) && self.live.insert(def_inst) {
                self.worklist.push(def_inst);
            }
        }
    }
}

fn is_drop_candidate(func: &Function, inst: InstId) -> bool {
    func.layout.is_inst_inserted(inst)
        && func.dfg.call_info(inst).is_none()
        && func.dfg.can_drop_if_unused(inst)
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

    #[test]
    fn dead_pure_cleanup_removes_closed_dead_cycles() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-london"

func private %f(v0.i1) {
block0:
    br v0 block1 block2;

block1:
    v1.i256 = phi (v2 block1) (1.i256 block0);
    v2.i256 = add v1 1.i256;
    jump block1;

block2:
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
                        "dead add cycle member should be removed"
                    );
                    assert!(
                        <&sonatina_ir::inst::control_flow::Phi as InstDowncast>::downcast(
                            func.inst_set(),
                            func.dfg.inst(inst),
                        )
                        .is_none(),
                        "dead phi cycle member should be removed"
                    );
                }
            }
        });
    }
}
