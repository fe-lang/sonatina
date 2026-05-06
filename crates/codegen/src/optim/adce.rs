//! This module contains a solver for `Aggressive Dead code elimination (ADCE)`.

use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashSet;
use sonatina_ir::{BlockId, ControlFlowGraph, Function, InstId};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode},
    cfg_scc::{CfgSccAnalysis, SccId},
    optim::{call_purity::is_nonmutating_returning_call, cfg_cleanup::CfgCleanup},
    post_domtree::{PDFSet, PDTIdom, PostDomTree},
};

pub struct AdceSolver {
    live_insts: SecondaryMap<InstId, bool>,
    live_blocks: SecondaryMap<BlockId, bool>,
    post_domtree: PostDomTree,
    worklist: Vec<InstId>,
    call_policy: AdceCallPolicy,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdceCallPolicy {
    ConservativeCalls,
    UseCurrentFuncEffects,
}

impl AdceSolver {
    pub fn new() -> Self {
        Self::with_call_policy(AdceCallPolicy::ConservativeCalls)
    }

    pub fn with_call_policy(call_policy: AdceCallPolicy) -> Self {
        Self {
            live_insts: SecondaryMap::default(),
            live_blocks: SecondaryMap::default(),
            post_domtree: PostDomTree::default(),
            worklist: Vec::default(),
            call_policy,
        }
    }

    pub fn clear(&mut self) {
        self.live_insts.clear();
        self.live_blocks.clear();
        self.post_domtree.clear();
        self.worklist.clear();
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        let mut changed = false;
        while self.run_dce(func) {
            changed = true;
        }
        let cleaned_cfg = CfgCleanup::new(CleanupMode::Strict).run(func);
        changed || cleaned_cfg
    }

    /// Returns `true` if dead code elimination changed the function.
    fn run_dce(&mut self, func: &mut Function) -> bool {
        self.clear();

        let divergent_blocks = divergent_blocks(func);
        self.post_domtree
            .compute_with_extra_exits(func, &divergent_blocks);
        let pdf_set = self.post_domtree.compute_df();

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
                if is_live_root_inst(func, inst, self.call_policy) {
                    self.mark_inst(func, inst);
                }
            }
        }
        for block in divergent_blocks {
            self.mark_block(block);
            if let Some(term) = func.layout.last_inst_of(block) {
                self.mark_inst(func, term);
            }
        }

        while let Some(inst) = self.worklist.pop() {
            self.mark_by_inst(func, inst, &pdf_set);
        }

        self.eliminate_dead_code(func)
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
        if func.layout.entry_block().is_none() {
            return false;
        }

        let blocks: Vec<_> = func.layout.iter_block().collect();
        let dead_blocks: Vec<_> = blocks
            .iter()
            .copied()
            .filter(|&block| !self.does_block_live(block))
            .collect();
        let dead_insts: Vec<_> = blocks
            .iter()
            .copied()
            .flat_map(|block| func.layout.iter_inst(block))
            .filter(|&inst| !self.does_inst_live(inst))
            .collect();

        let erased_dead_insts = erase_closed_dead_insts(func, dead_insts);

        let mut changed = erased_dead_insts;
        {
            let mut editor = CfgEditor::new(func, CleanupMode::RepairWithUndef);
            for block in blocks {
                if editor.func().layout.is_block_inserted(block) && self.does_block_live(block) {
                    changed |= self.modify_branch(&mut editor, block);
                }
            }
            changed |= editor.delete_blocks_unreachable(&dead_blocks);
        }

        changed
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

fn divergent_blocks(func: &Function) -> Vec<BlockId> {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);

    let mut sccs = CfgSccAnalysis::new();
    sccs.compute(&cfg);

    let mut reaches_real_exit = SecondaryMap::<SccId, bool>::with_capacity(sccs.scc_count());
    for &scc in sccs.topo_order().iter().rev() {
        let data = sccs.scc_data(scc);
        reaches_real_exit[scc] = data
            .blocks_rpo
            .iter()
            .any(|block| cfg.exits.contains(block))
            || data.succ_sccs.iter().any(|&succ| reaches_real_exit[succ]);
    }

    let mut blocks = Vec::new();
    for &scc in sccs.topo_order() {
        if !reaches_real_exit[scc] {
            blocks.extend(sccs.scc_data(scc).blocks_rpo.iter().copied());
        }
    }
    blocks
}

fn erase_closed_dead_insts(func: &mut Function, insts: impl IntoIterator<Item = InstId>) -> bool {
    let mut dead_insts = Vec::new();
    let mut dead_set = FxHashSet::default();
    for inst in insts {
        if func.dfg.has_inst(inst) && func.layout.is_inst_inserted(inst) && dead_set.insert(inst) {
            dead_insts.push(inst);
        }
    }
    if dead_insts.is_empty() {
        return false;
    }

    assert_closed_dead_inst_set(func, &dead_set);
    for &inst in &dead_insts {
        func.layout.remove_inst(inst);
    }
    func.erase_insts(&dead_insts);
    true
}

fn assert_closed_dead_inst_set(func: &Function, dead_set: &FxHashSet<InstId>) {
    for &inst in dead_set {
        for &result in func.dfg.inst_results(inst) {
            for &user in func.dfg.users(result) {
                if func.dfg.has_inst(user) && !dead_set.contains(&user) {
                    panic!(
                        "ADCE dead instruction set is not closed: {inst:?} result {result:?} is used by live instruction {user:?}"
                    );
                }
            }
        }
    }
}

impl Default for AdceSolver {
    fn default() -> Self {
        Self::new()
    }
}

fn is_live_root_inst(func: &Function, inst_id: InstId, call_policy: AdceCallPolicy) -> bool {
    if func.dfg.call_info(inst_id).is_some() {
        return match call_policy {
            AdceCallPolicy::ConservativeCalls => true,
            AdceCallPolicy::UseCurrentFuncEffects => {
                // ADCE may erase whole unused read-only calls only when the
                // caller guarantees function-effect summaries match the current
                // call ABI and function bodies.
                !is_nonmutating_returning_call(func, inst_id)
            }
        };
    }

    func.dfg.may_mutate_state(inst_id) || func.dfg.may_transfer_control(inst_id)
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{FuncEffectSummary, Module, ir_writer::FuncWriter};

    use crate::analysis::func_behavior;

    use super::{AdceCallPolicy, AdceSolver};

    fn parse_module(input: &str) -> sonatina_parser::ParsedModule {
        sonatina_parser::parse_module(input).unwrap_or_else(|errs| panic!("parse failed: {errs:?}"))
    }

    fn only_func_ref(module: &Module) -> sonatina_ir::module::FuncRef {
        let funcs = module.funcs();
        assert_eq!(funcs.len(), 1);
        funcs[0]
    }

    fn find_func(module: &Module, name: &str) -> sonatina_ir::module::FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .unwrap_or_else(|| panic!("missing function {name}"))
    }

    fn run_default_adce(input: &str) -> (bool, String) {
        let parsed = parse_module(input);
        let func_ref = only_func_ref(&parsed.module);
        let changed = parsed
            .module
            .func_store
            .modify(func_ref, |func| AdceSolver::new().run(func));
        let dumped = parsed.module.func_store.view(func_ref, |func| {
            FuncWriter::new(func_ref, func).dump_string()
        });
        (changed, dumped)
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

        let (_, dumped) = run_default_adce(source);
        assert!(
            dumped.contains("phi (v0 block0)") && dumped.contains("block0:\n        jump block1;"),
            "ADCE must keep the entry predecessor for live phi values:\n{dumped}"
        );
    }

    #[test]
    fn preserves_branch_to_infinite_loop() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i1) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        jump block1;

    block2:
        return 7.i256;
}
"#;

        let (_, dumped) = run_default_adce(source);
        assert!(
            dumped.contains("br v0 block1 block2;")
                && dumped.contains("block1:\n        jump block1;")
                && dumped.contains("return 7.i256;"),
            "ADCE must preserve divergence as control behavior:\n{dumped}"
        );
    }

    #[test]
    fn removes_dead_ssa_cycle_in_infinite_loop() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i1) {
    block0:
        br v0 block1 block2;

    block1:
        v1.i256 = phi (1.i256 block0) (v2 block1);
        v2.i256 = add v1 1.i256;
        jump block1;

    block2:
        return;
}
"#;

        let (changed, dumped) = run_default_adce(source);
        assert!(changed);
        assert!(
            !dumped.contains(" = phi ") && !dumped.contains(" = add "),
            "ADCE should remove unused pure cycles inside divergent regions:\n{dumped}"
        );
        assert!(
            dumped.contains("block1:\n        jump block1;"),
            "ADCE should keep the divergent control sink:\n{dumped}"
        );
    }

    #[test]
    fn runs_on_function_with_no_real_exit() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f() {
    block0:
        v0.i256 = add 1.i256 2.i256;
        jump block0;
}
"#;

        let (changed, dumped) = run_default_adce(source);
        assert!(changed);
        assert!(
            !dumped.contains(" = add ") && dumped.contains("jump block0;"),
            "ADCE should remove dead pure code even when the function never returns:\n{dumped}"
        );
    }

    #[test]
    fn removes_unused_read_only_call() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %reader(v0.i256) -> i256 {
    block0:
        v1.i256 = evm_sload v0;
        return v1;
}

func public %caller(v0.i256) -> i256 {
    block0:
        v1.i256 = call %reader v0;
        return 7.i256;
}
"#;

        let parsed = parse_module(source);
        func_behavior::analyze_module(&parsed.module);
        let func_ref = find_func(&parsed.module, "caller");

        parsed.module.func_store.modify(func_ref, |func| {
            AdceSolver::with_call_policy(AdceCallPolicy::UseCurrentFuncEffects).run(func);
        });

        parsed.module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                !dumped.contains("call %reader"),
                "ADCE should remove unused read-only calls:\n{dumped}"
            );
            assert!(
                dumped.contains("return 7.i256;"),
                "caller should still return the live constant:\n{dumped}"
            );
        });
    }

    #[test]
    fn conservative_call_policy_keeps_unused_read_only_call() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %reader(v0.i256) -> i256 {
    block0:
        v1.i256 = evm_sload v0;
        return v1;
}

func public %caller(v0.i256) -> i256 {
    block0:
        v1.i256 = call %reader v0;
        return 7.i256;
}
"#;

        let parsed = parse_module(source);
        func_behavior::analyze_module(&parsed.module);
        let func_ref = find_func(&parsed.module, "caller");

        parsed.module.func_store.modify(func_ref, |func| {
            AdceSolver::new().run(func);
        });

        parsed.module.func_store.view(func_ref, |func| {
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains("call %reader"),
                "conservative ADCE must keep calls even when stale summaries would classify them as elidable:\n{dumped}"
            );
        });
    }

    #[test]
    fn conservative_call_policy_keeps_out_pointer_call_with_stale_pure_summary() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %fill(v0.*i256) {
    block0:
        mstore v0 42.i256 i256;
        return;
}

func public %caller() -> i256 {
    block0:
        v0.*i256 = alloca i256;
        call %fill v0;
        v1.i256 = mload v0 i256;
        return v1;
}
"#;

        let parsed = parse_module(source);
        let fill = find_func(&parsed.module, "fill");
        parsed.module.ctx.set_func_effects(
            fill,
            FuncEffectSummary {
                will_return: true,
                ..FuncEffectSummary::default()
            },
        );
        let caller = find_func(&parsed.module, "caller");

        parsed.module.func_store.modify(caller, |func| {
            AdceSolver::new().run(func);
        });

        parsed.module.func_store.view(caller, |func| {
            let dumped = FuncWriter::new(caller, func).dump_string();
            assert!(
                dumped.contains("call %fill"),
                "conservative ADCE must not trust stale pure summaries for out-pointer calls:\n{dumped}"
            );
        });
    }

    #[test]
    fn removes_dead_ssa_cycle_in_live_blocks() {
        let source = r#"
target = "evm-ethereum-osaka"

type @pair = {i256, i256};

func private %f(v0.i1) {
    block0:
        v1.@pair = insert_value undef.@pair 0.i256 4.i256;
        v2.@pair = insert_value v1 1.i256 4.i256;
        jump block1;

    block1:
        v3.@pair = phi (v2 block0) (v5 block2);
        br v0 block2 block3;

    block2:
        v4.@pair = insert_value v3 0.i256 5.i256;
        v5.@pair = insert_value v4 1.i256 6.i256;
        jump block1;

    block3:
        return;
}
"#;

        let (changed, dumped) = run_default_adce(source);
        assert!(changed);
        assert!(
            !dumped.contains("insert_value") && !dumped.contains("@pair = phi"),
            "ADCE should remove the unused aggregate cycle:\n{dumped}"
        );
        assert!(
            dumped.contains("return;"),
            "ADCE should preserve live control flow:\n{dumped}"
        );
    }
}
