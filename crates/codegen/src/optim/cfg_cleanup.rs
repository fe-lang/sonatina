use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstDowncast,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::control_flow::Unreachable,
    module::FuncAttrs,
};

use crate::cfg_edit::{CfgEditor, CleanupMode};

pub struct CfgCleanup {
    mode: CleanupMode,
}

impl CfgCleanup {
    pub fn new(mode: CleanupMode) -> Self {
        Self { mode }
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        if func.layout.entry_block().is_none() {
            return false;
        }

        let mut editor = CfgEditor::new(func, self.mode);

        let mut changed = editor.trim_after_terminator();
        changed |= ensure_blocks_terminated(editor.func_mut(), self.mode);
        if changed {
            editor.recompute_cfg();
        }

        changed |= trim_after_noreturn_call(&mut editor);

        let pruned_unreachable = prune_unreachable(&mut editor);
        changed |= pruned_unreachable;

        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        for block in blocks {
            assert_phis_leading(editor.func(), block);
            changed |= editor.prune_phi_to_current_preds(block);
            changed |= crate::cfg_edit::simplify_trivial_phis_in_block(editor.func_mut(), block);
        }

        let merged = merge_linear_blocks(&mut editor);
        changed |= merged;
        if merged {
            let blocks: Vec<_> = editor.func().layout.iter_block().collect();
            for block in blocks {
                assert_phis_leading(editor.func(), block);
                changed |= editor.prune_phi_to_current_preds(block);
                changed |=
                    crate::cfg_edit::simplify_trivial_phis_in_block(editor.func_mut(), block);
            }
        }

        if matches!(self.mode, CleanupMode::Strict) {
            assert_ir_invariants(editor.func(), editor.cfg());
        }

        changed
    }
}

fn merge_linear_blocks(editor: &mut CfgEditor) -> bool {
    let mut changed = false;
    let mut budget = editor.func().layout.iter_block().count().saturating_mul(2);

    while budget > 0 {
        budget -= 1;
        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        let mut merged = false;

        for block in blocks {
            if !editor.func().layout.is_block_inserted(block) {
                continue;
            }
            if editor.fold_trampoline_block(block)
                || editor.forward_bridge_block(block)
                || editor.merge_linear_successor(block)
            {
                merged = true;
                changed = true;
                break;
            }
        }

        if !merged {
            break;
        }
    }

    changed
}

fn trim_after_noreturn_call(editor: &mut CfgEditor<'_>) -> bool {
    let mut changed = false;

    'restart: loop {
        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        for block in blocks {
            if !editor.func().layout.is_block_inserted(block) {
                continue;
            }

            let mut next_inst = editor.func().layout.first_inst_of(block);
            while let Some(inst) = next_inst {
                next_inst = editor.func().layout.next_inst_of(inst);

                let Some(call_info) = editor.func().dfg.call_info(inst) else {
                    continue;
                };
                let callee = call_info.callee();
                if !editor
                    .func()
                    .ctx()
                    .func_attrs(callee)
                    .contains(FuncAttrs::NORETURN)
                {
                    continue;
                }

                let Some(after) = editor.func().layout.next_inst_of(inst) else {
                    continue;
                };
                let already_normalized = editor.func().layout.next_inst_of(after).is_none()
                    && <&Unreachable as InstDowncast>::downcast(
                        editor.func().inst_set(),
                        editor.func().dfg.inst(after),
                    )
                    .is_some();
                if already_normalized {
                    continue;
                }

                let (_, cont_block) = editor.split_block_at(after);
                let term = editor
                    .func()
                    .layout
                    .last_inst_of(block)
                    .expect("split block should end with a jump");
                let jump = editor
                    .func()
                    .dfg
                    .cast_jump(term)
                    .expect("split block terminator should be a jump");
                debug_assert_eq!(*jump.dest(), cont_block);

                InstInserter::at_location(CursorLocation::At(term)).remove_inst(editor.func_mut());

                let inst_set = editor.func().inst_set();
                InstInserter::at_location(CursorLocation::BlockBottom(block))
                    .insert_inst_data(editor.func_mut(), Unreachable::new_unchecked(inst_set));

                editor.recompute_cfg();
                let unreachable = collect_unreachable_blocks(editor);
                if !unreachable.is_empty() {
                    editor.delete_blocks_unreachable(&unreachable);
                }

                changed = true;
                continue 'restart;
            }
        }

        break;
    }

    changed
}

fn collect_unreachable_blocks(editor: &CfgEditor<'_>) -> Vec<BlockId> {
    let reachable = editor.cfg().reachable_blocks();
    editor
        .func()
        .layout
        .iter_block()
        .filter(|block| !reachable[*block])
        .collect()
}

fn prune_unreachable(editor: &mut CfgEditor<'_>) -> bool {
    let unreachable = collect_unreachable_blocks(editor);
    if unreachable.is_empty() {
        return false;
    }

    editor.delete_blocks_unreachable(&unreachable)
}

fn ensure_blocks_terminated(func: &mut Function, mode: CleanupMode) -> bool {
    let blocks: Vec<_> = func.layout.iter_block().collect();
    let mut changed = false;

    for block in blocks {
        let term = func.layout.last_inst_of(block);
        if term.is_some_and(|inst| func.dfg.is_terminator(inst)) {
            continue;
        }

        match mode {
            CleanupMode::Strict => panic!("block {block:?} does not end with a terminator"),
            CleanupMode::RepairWithUndef => {
                let unreachable = Unreachable::new_unchecked(func.inst_set());
                InstInserter::at_location(CursorLocation::BlockBottom(block))
                    .insert_inst_data(func, unreachable);
                changed = true;
            }
        }
    }

    changed
}

fn assert_phis_leading(func: &Function, block: BlockId) {
    let mut seen_non_phi = false;
    for inst in func.layout.iter_inst(block) {
        if func.dfg.is_phi(inst) {
            assert!(!seen_non_phi, "phi found after non-phi in {block:?}");
        } else {
            seen_non_phi = true;
        }
    }
}

fn assert_ir_invariants(func: &Function, cfg: &ControlFlowGraph) {
    let entry = func
        .layout
        .entry_block()
        .unwrap_or_else(|| panic!("function has no entry block"));
    if func
        .layout
        .first_inst_of(entry)
        .is_some_and(|inst| func.dfg.is_phi(inst))
    {
        panic!("entry block {entry:?} must not have phis");
    }

    for block in func.layout.iter_block() {
        let term = func
            .layout
            .last_inst_of(block)
            .unwrap_or_else(|| panic!("block {block:?} has no terminator"));
        assert!(
            func.dfg.is_terminator(term),
            "block {block:?} does not end with a terminator"
        );

        let mut seen_term = false;
        for inst in func.layout.iter_inst(block) {
            if seen_term {
                panic!("instruction found after terminator in {block:?}");
            }

            func.dfg.inst(inst).for_each_value(&mut |value| {
                if let Some(def_inst) = func.dfg.value_inst(value) {
                    assert!(
                        func.layout.is_inst_inserted(def_inst),
                        "value {value:?} is defined by uninserted inst {def_inst:?}"
                    );
                }
            });

            seen_term = func.dfg.is_terminator(inst);
        }

        if let Some(branch_info) = func.dfg.branch_info(term) {
            for dest in branch_info.dests() {
                assert!(
                    func.layout.is_block_inserted(dest),
                    "branch target {dest:?} is not inserted"
                );
            }
        }

        assert_phis_leading(func, block);

        let preds = cfg.preds_as_slice(block);
        let mut next_inst = func.layout.first_inst_of(block);
        while let Some(inst) = next_inst {
            next_inst = func.layout.next_inst_of(inst);
            let Some(phi) = func.dfg.cast_phi(inst) else {
                break;
            };

            let mut seen = Vec::with_capacity(phi.args().len());
            for &(_, pred) in phi.args() {
                assert!(!seen.contains(&pred), "phi {inst:?} has duplicate {pred:?}");
                assert!(
                    preds.binary_search(&pred).is_ok(),
                    "phi {inst:?} has stale {pred:?}"
                );
                seen.push(pred);
            }
            seen.sort_unstable();

            assert_eq!(
                seen.as_slice(),
                preds,
                "phi {inst:?} incoming set does not match predecessors"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        InstDowncast, Module,
        inst::control_flow::{Return, Unreachable},
        ir_writer::FuncWriter,
        module::FuncRef,
    };
    use sonatina_parser::parse_module;

    fn parse(src: &str) -> Module {
        parse_module(src)
            .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
            .module
    }

    fn find_func(module: &Module, name: &str) -> FuncRef {
        module
            .func_store
            .funcs()
            .into_iter()
            .find(|func_ref| module.ctx.func_sig(*func_ref, |sig| sig.name() == name))
            .expect("function should exist")
    }

    #[test]
    fn trims_code_after_call_to_evm_return_only_helper() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %exit_now() {
    block0:
        evm_return 0.i256 0.i256;
}

func private %caller() {
    block0:
        call %exit_now;
        return;
}
"#,
        );
        crate::analysis::func_behavior::analyze_module(&module);

        let exit_now = find_func(&module, "exit_now");
        let caller = find_func(&module, "caller");
        assert!(
            module
                .ctx
                .func_attrs(exit_now)
                .contains(FuncAttrs::NORETURN)
        );

        module.func_store.modify(caller, |func| {
            assert!(CfgCleanup::new(CleanupMode::RepairWithUndef).run(func));

            let block = func.layout.entry_block().expect("entry block");
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            assert_eq!(insts.len(), 2);
            assert!(func.dfg.call_info(insts[0]).is_some());
            assert!(
                <&Unreachable as InstDowncast>::downcast(func.inst_set(), func.dfg.inst(insts[1]))
                    .is_some()
            );
            assert_eq!(
                insts
                    .iter()
                    .filter(|&&inst| {
                        <&Return as InstDowncast>::downcast(func.inst_set(), func.dfg.inst(inst))
                            .is_some()
                    })
                    .count(),
                0
            );
        });
    }

    #[test]
    fn trims_noreturn_split_continuation_without_undef() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %run() -> i256 {
block0:
    evm_return 0.i256 0.i256;
}

func private %test_run() {
block0:
    v0.i256 = call %run;
    v3.i1 = eq v0 2.i256;
    jump block2;

block2:
    v4.i1 = is_zero v3;
    br v4 block3 block4;

block3:
    evm_revert 0.i256 0.i256;

block4:
    jump block1;

block1:
    return;
}
"#,
        );
        crate::analysis::func_behavior::analyze_module(&module);

        let test_run = find_func(&module, "test_run");
        module.func_store.modify(test_run, |func| {
            assert!(CfgCleanup::new(CleanupMode::RepairWithUndef).run(func));

            let dumped = FuncWriter::new(test_run, func).dump_string();
            assert!(dumped.contains("unreachable;"));
            assert!(!dumped.contains("eq "));
            assert!(!dumped.contains("is_zero "));
            assert!(!dumped.contains("undef"));
            assert_eq!(func.layout.iter_block().count(), 1);
        });
    }

    #[test]
    fn trims_noreturn_loop_tail_and_repairs_backedge_phi_inputs() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %exit_now() {
    block0:
        evm_return 0.i256 0.i256;
}

func private %caller() {
    block0:
        jump block1;

    block1:
        v0.i256 = phi (0.i256 block0) (v1 block2);
        br 1.i1 block2 block3;

    block2:
        call %exit_now;
        v1.i256 = add v0 1.i256;
        jump block1;

    block3:
        return;
}
"#,
        );
        crate::analysis::func_behavior::analyze_module(&module);

        let caller = find_func(&module, "caller");
        module.func_store.modify(caller, |func| {
            assert!(CfgCleanup::new(CleanupMode::RepairWithUndef).run(func));

            let block2 = func
                .layout
                .iter_block()
                .find(|&block| {
                    func.layout.first_inst_of(block).is_some_and(|inst| {
                        func.dfg.call_info(inst).is_some_and(|call| {
                            func.ctx()
                                .func_sig(call.callee(), |sig| sig.name() == "exit_now")
                        })
                    })
                })
                .expect("block with exit_now call should remain");
            let block2_insts: Vec<_> = func.layout.iter_inst(block2).collect();
            assert_eq!(block2_insts.len(), 2);
            assert!(func.dfg.call_info(block2_insts[0]).is_some());
            assert!(
                <&Unreachable as InstDowncast>::downcast(
                    func.inst_set(),
                    func.dfg.inst(block2_insts[1]),
                )
                .is_some()
            );

            let block1 = func
                .layout
                .iter_block()
                .find(|&block| {
                    func.layout.last_inst_of(block).is_some_and(|inst| {
                        func.dfg.is_branch(inst)
                            && func
                                .dfg
                                .branch_info(inst)
                                .is_some_and(|info| info.dests().contains(&block2))
                    })
                })
                .expect("loop header block should remain");
            let header_first = func
                .layout
                .first_inst_of(block1)
                .expect("header first inst");
            assert!(func.dfg.cast_phi(header_first).is_none());
        });
    }

    #[test]
    fn prunes_multi_block_unreachable_region_as_closed_set() {
        let module = parse(
            r#"
target = "evm-ethereum-osaka"

func private %dead_region() {
block0:
    return;

block1:
    v0.i1 = eq 1.i256 2.i256;
    jump block2;

block2:
    v1.i1 = is_zero v0;
    br v1 block3 block4;

block3:
    return;

block4:
    return;
}
"#,
        );

        let dead_region = find_func(&module, "dead_region");
        module.func_store.modify(dead_region, |func| {
            assert!(CfgCleanup::new(CleanupMode::RepairWithUndef).run(func));

            let dumped = FuncWriter::new(dead_region, func).dump_string();
            assert!(!dumped.contains("eq "));
            assert!(!dumped.contains("is_zero "));
            assert!(!dumped.contains("undef"));
            assert_eq!(func.layout.iter_block().count(), 1);
        });
    }
}
