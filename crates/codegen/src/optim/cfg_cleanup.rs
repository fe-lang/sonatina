use std::collections::BTreeSet;

use sonatina_ir::{
    BlockId, ControlFlowGraph, Function,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::control_flow::Unreachable,
    module::FuncAttrs,
};

use crate::cfg_edit::{CfgEditor, CleanupMode, prune_phi_to_preds};

pub struct CfgCleanup {
    mode: CleanupMode,
}

impl CfgCleanup {
    pub fn new(mode: CleanupMode) -> Self {
        Self { mode }
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        let Some(entry) = func.layout.entry_block() else {
            return false;
        };

        let mut editor = CfgEditor::new(func, self.mode);

        let mut changed = editor.trim_after_terminator();
        changed |= ensure_blocks_terminated(editor.func_mut(), self.mode);
        changed |= trim_after_noreturn_call(editor.func_mut());
        editor.recompute_cfg();

        let reachable = compute_reachable(editor.cfg(), entry);
        changed |= prune_unreachable(editor.func_mut(), &reachable);
        editor.recompute_cfg();

        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        for block in blocks {
            assert_phis_leading(editor.func(), block);

            let preds: BTreeSet<_> = editor.cfg().preds_of(block).copied().collect();
            changed |= prune_phi_to_preds(editor.func_mut(), block, &preds, self.mode);
            changed |= crate::cfg_edit::simplify_trivial_phis_in_block(editor.func_mut(), block);
        }

        changed |= fold_trampoline_blocks(&mut editor);

        if matches!(self.mode, CleanupMode::Strict) {
            assert_ir_invariants(editor.func(), editor.cfg());
        }

        changed
    }
}

fn trim_after_noreturn_call(func: &mut Function) -> bool {
    let blocks: Vec<_> = func.layout.iter_block().collect();
    let mut changed = false;

    for block in blocks {
        let mut next_inst = func.layout.first_inst_of(block);
        while let Some(inst) = next_inst {
            next_inst = func.layout.next_inst_of(inst);

            let Some(call_info) = func.dfg.call_info(inst) else {
                continue;
            };
            let callee = call_info.callee();
            if !func.ctx().func_attrs(callee).contains(FuncAttrs::NORETURN) {
                continue;
            }

            let mut to_remove = Vec::new();
            let mut cursor = func.layout.next_inst_of(inst);
            while let Some(after) = cursor {
                to_remove.push(after);
                cursor = func.layout.next_inst_of(after);
            }

            for inst in to_remove {
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            }

            let unreachable = Unreachable::new_unchecked(func.inst_set());
            InstInserter::at_location(CursorLocation::BlockBottom(block))
                .insert_inst_data(func, unreachable);
            changed = true;
            break;
        }
    }

    changed
}

fn compute_reachable(cfg: &ControlFlowGraph, entry: BlockId) -> BTreeSet<BlockId> {
    let mut reachable = BTreeSet::new();
    let mut stack = vec![entry];

    while let Some(block) = stack.pop() {
        if !reachable.insert(block) {
            continue;
        }
        for &succ in cfg.succs_of(block) {
            stack.push(succ);
        }
    }

    reachable
}

fn prune_unreachable(func: &mut Function, reachable: &BTreeSet<BlockId>) -> bool {
    let blocks: Vec<_> = func.layout.iter_block().collect();
    let mut changed = false;

    for block in blocks {
        if reachable.contains(&block) {
            continue;
        }
        InstInserter::at_location(CursorLocation::BlockTop(block)).remove_block(func);
        changed = true;
    }

    changed
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

fn fold_trampoline_blocks(editor: &mut CfgEditor<'_>) -> bool {
    let mut changed = false;

    loop {
        let mut local_changed = editor.fold_entry_trampoline_block();

        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        for block in blocks {
            local_changed |= editor.fold_trampoline_block(block);
        }

        if !local_changed {
            return changed;
        }
        changed = true;
    }
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

        let preds: BTreeSet<_> = cfg.preds_of(block).copied().collect();
        let mut next_inst = func.layout.first_inst_of(block);
        while let Some(inst) = next_inst {
            next_inst = func.layout.next_inst_of(inst);
            let Some(phi) = func.dfg.cast_phi(inst) else {
                break;
            };

            let mut seen = BTreeSet::new();
            for &(_, pred) in phi.args() {
                assert!(seen.insert(pred), "phi {inst:?} has duplicate {pred:?}");
                assert!(preds.contains(&pred), "phi {inst:?} has stale {pred:?}");
            }

            assert_eq!(
                seen, preds,
                "phi {inst:?} incoming set does not match predecessors"
            );
        }
    }
}
