//! This module contains a solver for `Aggressive Dead code elimination (ADCE)`.

use std::collections::BTreeSet;

use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::SideEffect,
};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode},
    optim::{call_purity::is_removable_pure_call, cfg_cleanup::CfgCleanup},
    post_domtree::{PDFSet, PDTIdom, PostDomTree},
};

pub struct AdceSolver {
    live_insts: SecondaryMap<InstId, bool>,
    live_blocks: SecondaryMap<BlockId, bool>,
    empty_blocks: BTreeSet<BlockId>,
    post_domtree: PostDomTree,
    worklist: Vec<InstId>,
}

impl AdceSolver {
    pub fn new() -> Self {
        Self {
            live_insts: SecondaryMap::default(),
            live_blocks: SecondaryMap::default(),
            empty_blocks: BTreeSet::default(),
            post_domtree: PostDomTree::default(),
            worklist: Vec::default(),
        }
    }

    pub fn clear(&mut self) {
        self.live_insts.clear();
        self.live_blocks.clear();
        self.empty_blocks.clear();
        self.post_domtree.clear();
        self.worklist.clear();
    }

    pub fn run(&mut self, func: &mut Function) {
        while self.run_dce(func) {}
        CfgCleanup::new(CleanupMode::Strict).run(func);
    }

    /// Returns `true` if branch inst is modified while dead code elimination.
    fn run_dce(&mut self, func: &mut Function) -> bool {
        self.clear();

        self.post_domtree.compute(func);
        let pdf_set = self.post_domtree.compute_df();

        // TODO: We should remove this restriction.
        // ref: <https://reviews.llvm.org/D35851>
        if self.has_infinite_loop(func) {
            return false;
        }

        // The entry block must always be live — removing it would shift
        // the layout so a different block becomes the entry, breaking
        // the function's control flow.
        if let Some(entry) = func.layout.entry_block() {
            self.mark_block(entry);
            if let Some(term) = func.layout.last_inst_of(entry) {
                self.mark_inst(func, term);
            }
        }

        for block in func.layout.iter_block() {
            for inst in func.layout.iter_inst(block) {
                if is_live_root_inst(func, inst) {
                    self.mark_inst(func, inst);
                }
            }
        }

        while let Some(inst) = self.worklist.pop() {
            self.mark_by_inst(func, inst, &pdf_set);
        }

        self.eliminate_dead_code(func)
    }

    fn has_infinite_loop(&self, func: &Function) -> bool {
        for block in func.layout.iter_block() {
            if !self.post_domtree.is_reachable(block) {
                return true;
            }
        }

        false
    }

    fn mark_inst(&mut self, func: &Function, inst: InstId) {
        let mut mark_inst = |inst, block| {
            if !self.does_inst_live(inst) {
                self.live_insts[inst] = true;
                self.worklist.push(inst);
                self.mark_block(block);
                true
            } else {
                false
            }
        };

        let inst_block = func.layout.inst_block(inst);
        if mark_inst(inst, inst_block) {
            let last_inst = func.layout.last_inst_of(inst_block).unwrap();
            mark_inst(last_inst, inst_block);
        }
    }

    fn mark_block(&mut self, block: BlockId) {
        self.live_blocks[block] = true;
    }

    fn does_inst_live(&self, inst: InstId) -> bool {
        self.live_insts[inst]
    }

    fn does_block_live(&self, block: BlockId) -> bool {
        self.live_blocks[block]
    }

    fn mark_by_inst(&mut self, func: &Function, inst_id: InstId, pdf_set: &PDFSet) {
        let inst = func.dfg.inst(inst_id);
        inst.for_each_value(&mut |value| {
            if let Some(value_inst) = func.dfg.value_inst(value) {
                self.mark_inst(func, value_inst);
            }
        });

        // A live phi semantically depends on predecessor edges.
        // Keep predecessor terminators live so we do not erase incoming values.
        if let Some(phi) = func.dfg.cast_phi(inst_id) {
            for &(_, pred) in phi.args() {
                if let Some(term) = func.layout.last_inst_of(pred) {
                    self.mark_inst(func, term);
                }
            }
        }

        let inst_block = func.layout.inst_block(inst_id);
        for &block in pdf_set.frontiers(inst_block) {
            if let Some(last_inst) = func.layout.last_inst_of(block) {
                self.mark_inst(func, last_inst)
            }
        }
    }

    fn eliminate_dead_code(&mut self, func: &mut Function) -> bool {
        let entry = if let Some(entry) = func.layout.entry_block() {
            entry
        } else {
            return false;
        };

        let mut inserter = InstInserter::at_location(CursorLocation::BlockTop(entry));
        loop {
            match inserter.loc() {
                CursorLocation::At(inst) => {
                    if self.does_inst_live(inst) {
                        inserter.proceed(func);
                    } else {
                        inserter.remove_inst(func)
                    }
                }

                CursorLocation::BlockTop(block) => {
                    if self.does_block_live(block) {
                        inserter.proceed(func)
                    } else {
                        inserter.remove_block(func)
                    }
                }

                CursorLocation::BlockBottom(_) => {
                    inserter.proceed(func);
                }

                CursorLocation::NoWhere => break,
            }
        }

        // Modify branch insts to remove unreachable edges via CfgEditor.
        let mut cfg = ControlFlowGraph::default();
        let mut editor = CfgEditor::new(func, &mut cfg, CleanupMode::RepairWithUndef);
        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        let mut br_inst_modified = false;
        for block in blocks {
            br_inst_modified |= self.modify_branch(&mut editor, block);
        }

        br_inst_modified
    }

    fn living_post_dom(&self, mut block: BlockId) -> Option<BlockId> {
        loop {
            let idom = self.post_domtree.idom_of(block)?;
            match idom {
                PDTIdom::Real(block) if self.does_block_live(block) => return Some(block),
                PDTIdom::Real(post_dom) => block = post_dom,
                PDTIdom::DummyExit(_) | PDTIdom::DummyEntry(_) => return None,
            }
        }
    }

    /// Returns `true` if branch inst is modified.
    fn modify_branch(&self, editor: &mut CfgEditor, block: BlockId) -> bool {
        let last_inst = match editor.func().layout.last_inst_of(block) {
            Some(inst) => inst,
            None => return false,
        };
        let dests = editor
            .func()
            .dfg
            .branch_info(last_inst)
            .map(|bi| bi.dests())
            .unwrap_or_default();

        let mut changed = false;
        for dest in dests {
            if self.does_block_live(dest) {
                continue;
            }

            let mut rewrote = false;
            if let Some(postdom) = self.living_post_dom(dest) {
                let safe_succ = editor
                    .func()
                    .dfg
                    .branch_info(last_inst)
                    .is_some_and(|bi| bi.dests().contains(&postdom));
                let safe_no_phi = !editor
                    .func()
                    .layout
                    .iter_inst(postdom)
                    .any(|inst| editor.func().dfg.is_phi(inst));
                if safe_succ || safe_no_phi {
                    rewrote = editor.replace_succ_allow_existing_pred(block, dest, postdom, &[]);
                }
            }

            if !rewrote {
                rewrote = editor.remove_succ(block, dest);
            }

            changed |= rewrote;
        }

        changed
    }
}

impl Default for AdceSolver {
    fn default() -> Self {
        Self::new()
    }
}

fn is_live_root_inst(func: &Function, inst_id: InstId) -> bool {
    if func.dfg.call_info(inst_id).is_some() {
        return !is_removable_pure_call(func, inst_id);
    }

    matches!(
        func.dfg.side_effect(inst_id),
        SideEffect::Write | SideEffect::Control
    )
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{Module, ir_writer::FuncWriter};

    use super::AdceSolver;

    fn parse_module(input: &str) -> sonatina_parser::ParsedModule {
        sonatina_parser::parse_module(input).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
    }

    fn only_func_ref(module: &Module) -> sonatina_ir::module::FuncRef {
        let funcs = module.funcs();
        assert_eq!(funcs.len(), 1);
        funcs[0]
    }

    #[test]
    fn keeps_phi_entry_pred_edge_live() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (v0 block0) (v2 block2);
        v3.i1 = lt v1 10.i256;
        br v3 block2 block3;

    block2:
        v2.i256 = add v1 1.i256;
        jump block1;

    block3:
        return v1;
}
"#;

        let parsed = parse_module(source);
        let func_ref = only_func_ref(&parsed.module);

        parsed.module.func_store.modify(func_ref, |func| {
            AdceSolver::new().run(func);
        });

        parsed.module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("phi (v0 block0)")
                    && dumped.contains("block0:\n        jump block1;"),
                "ADCE must keep the entry predecessor for live phi values:\n{dumped}"
            );
        });
    }
}
