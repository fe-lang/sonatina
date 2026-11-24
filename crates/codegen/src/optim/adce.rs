//! This module contains a solver for `Aggressive Dead code elimination (ADCE)`.

use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashSet;
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, Type, U256, ValueId,
    inst::{BinaryInstKind, control_flow::Br, data::Alloca},
};

use crate::{
    analysis::{
        induction::{
            detect_basic_iv_step, is_loop_invariant_value, phi_backedge_with_outside_preds,
            unique_latch,
        },
        known_bits::type_mask,
    },
    cfg_edit::CfgEditor,
    cfg_scc::{CfgSccAnalysis, SccId},
    domtree::DomTree,
    loop_analysis::{Loop, LoopTree},
    object::lowering::{FiniteLoop, StepFacts, StepKind},
    optim::{call_purity::is_nonmutating_returning_call, cfg_cleanup::CfgCleanup, steps::StepLog},
    post_domtree::{PDFSet, PDTIdom, PostDomTree},
    range_analysis::{NormalizedCond, RangeEnv, imm_to_unsigned, normalize_condition},
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
        self.run_with_steps(func, None, 0)
    }

    /// `run`, reporting its rounds to `steps` in phase `first_phase` and its
    /// cleanup in the next.
    pub(crate) fn run_with_steps(
        &mut self,
        func: &mut Function,
        mut steps: Option<&mut StepLog>,
        first_phase: usize,
    ) -> bool {
        let mut changed = false;
        loop {
            let (round_changed, finite_loops) = self.run_dce(func);
            let facts = StepFacts {
                finite_loops,
                ..StepFacts::default()
            };
            StepLog::step(&mut steps, first_phase, StepKind::Adce, func, Some(facts));
            if !round_changed {
                break;
            }
            changed = true;
        }
        let cleaned_cfg = CfgCleanup::new().run(func);
        StepLog::step(
            &mut steps,
            first_phase + 1,
            StepKind::CfgCleanup,
            func,
            None,
        );
        changed || cleaned_cfg
    }

    /// Returns `true` if dead code elimination changed the function, and the
    /// loops it may remove, which it proved finite.
    fn run_dce(&mut self, func: &mut Function) -> (bool, Vec<FiniteLoop>) {
        self.clear();

        let mut cfg = ControlFlowGraph::new();
        cfg.compute(func);
        let (sccs, reaches_real_exit) = compute_scc_reachability(&cfg);
        let divergent_blocks = collect_divergent_blocks(&sccs, &reaches_real_exit);
        let (preserved_cycle_blocks, finite_loops) =
            preserved_cycle_blocks(func, &cfg, &sccs, &reaches_real_exit);
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
        for block in preserved_cycle_blocks {
            self.mark_block(block);
            if let Some(term) = func.layout.last_inst_of(block) {
                self.mark_inst(func, term);
            }
        }

        while let Some(inst) = self.worklist.pop() {
            self.mark_by_inst(func, inst, &pdf_set);
        }

        (self.eliminate_dead_code(func), finite_loops)
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
            let mut editor = CfgEditor::new(func);
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

fn compute_scc_reachability(cfg: &ControlFlowGraph) -> (CfgSccAnalysis, SecondaryMap<SccId, bool>) {
    let mut sccs = CfgSccAnalysis::new();
    sccs.compute(cfg);

    let mut reaches_real_exit = SecondaryMap::<SccId, bool>::with_capacity(sccs.scc_count());
    for &scc in sccs.topo_order().iter().rev() {
        let data = sccs.scc_data(scc);
        reaches_real_exit[scc] = data
            .blocks_rpo
            .iter()
            .any(|block| cfg.exits.contains(block))
            || data.succ_sccs.iter().any(|&succ| reaches_real_exit[succ]);
    }

    (sccs, reaches_real_exit)
}

fn collect_divergent_blocks(
    sccs: &CfgSccAnalysis,
    reaches_real_exit: &SecondaryMap<SccId, bool>,
) -> Vec<BlockId> {
    let mut blocks = Vec::new();
    for &scc in sccs.topo_order() {
        if !reaches_real_exit[scc] {
            blocks.extend(sccs.scc_data(scc).blocks_rpo.iter().copied());
        }
    }
    blocks
}

/// Returns entry-reachable blocks with no path to a CFG exit.
pub(crate) fn divergent_blocks(cfg: &ControlFlowGraph) -> Vec<BlockId> {
    let (sccs, reaches_real_exit) = compute_scc_reachability(cfg);
    collect_divergent_blocks(&sccs, &reaches_real_exit)
}

/// Returns blocks that must remain live to preserve cycles not proven finite,
/// and the loops proven finite.
///
/// Cycles with no path to a CFG exit are already preserved via
/// `divergent_blocks`. For cyclic SCCs that can reach a CFG exit, ADCE may
/// bypass a cycle only when it is a reducible natural loop proven to terminate
/// by a basic induction variable with a non-zero constant step and a
/// loop-invariant exit bound that cannot be wrapped past.
fn preserved_cycle_blocks(
    func: &Function,
    cfg: &ControlFlowGraph,
    sccs: &CfgSccAnalysis,
    reaches_real_exit: &SecondaryMap<SccId, bool>,
) -> (Vec<BlockId>, Vec<FiniteLoop>) {
    if !sccs
        .topo_order()
        .iter()
        .any(|&scc| sccs.scc_data(scc).is_cycle && reaches_real_exit[scc])
    {
        return (Vec::new(), Vec::new());
    }

    let mut domtree = DomTree::new();
    domtree.compute(cfg);
    let mut lpt = LoopTree::new();
    lpt.compute(cfg, &domtree);

    // Without its back edges a reducible CFG is acyclic, so the cycles that
    // remain are the irreducible ones.
    let mut forward = cfg.clone();
    for &block in domtree.rpo() {
        for &succ in cfg.succs_of(block) {
            if domtree.dominates(succ, block) {
                forward.remove_succ_block(block, succ);
            }
        }
    }
    let mut forward_sccs = CfgSccAnalysis::new();
    forward_sccs.compute(&forward);
    let irreducible: FxHashSet<BlockId> = forward_sccs
        .topo_order()
        .iter()
        .map(|&scc| forward_sccs.scc_data(scc))
        .filter(|data| data.is_cycle)
        .flat_map(|data| data.blocks_rpo.iter().copied())
        .collect();

    let mut finite_loops = SecondaryMap::<Loop, Option<FiniteLoop>>::with_capacity(lpt.loop_num());
    for lp in lpt.loops().rev() {
        finite_loops[lp] = (lpt
            .children(lp)
            .iter()
            .all(|&child| finite_loops[child].is_some())
            && !lpt
                .iter_blocks_post_order(cfg, lp)
                .any(|block| irreducible.contains(&block)))
        .then(|| proven_finite_loop(func, cfg, &domtree, &lpt, lp))
        .flatten();
    }

    let mut preserved: Vec<BlockId> = irreducible.into_iter().collect();
    for lp in lpt.loops().filter(|&lp| finite_loops[lp].is_none()) {
        let header = lpt.loop_header(lp);
        if sccs
            .scc_of(header)
            .is_some_and(|scc| reaches_real_exit[scc])
        {
            preserved.push(header);
            preserved.extend(
                cfg.preds_of(header)
                    .copied()
                    .filter(|&pred| domtree.is_reachable(pred) && domtree.dominates(header, pred)),
            );
        }
    }
    let finite = lpt.loops().filter_map(|lp| finite_loops[lp]).collect();
    (preserved, finite)
}

/// A basic induction variable of a loop: `phi` takes `step_value` from the
/// latch, `phi` moved by `magnitude`, up or down modulo its width.
struct LoopIv {
    phi: ValueId,
    step_value: ValueId,
    ty: Type,
    upward: bool,
    magnitude: U256,
}

/// `lp`, if it has a single latch and runs a test on every iteration that
/// leaves the loop once a basic induction variable passes a loop-invariant
/// bound it cannot step over without wrapping.
fn proven_finite_loop(
    func: &Function,
    cfg: &ControlFlowGraph,
    domtree: &DomTree,
    lpt: &LoopTree,
    lp: Loop,
) -> Option<FiniteLoop> {
    let header = lpt.loop_header(lp);
    let latch = unique_latch(cfg, lpt, lp, header)?;

    // The step must run once on every iteration of `lp` itself.
    let ivs: SmallVec<[LoopIv; 4]> = func
        .layout
        .iter_inst(header)
        .map_while(|inst| Some((inst, func.dfg.cast_phi(inst)?)))
        .filter_map(|(inst, phi)| {
            let phi_value = func.dfg.inst_result(inst)?;
            let ty = func.dfg.value_ty(phi_value);
            let step_value = phi_backedge_with_outside_preds(phi, latch, lp, lpt)?;
            let (step_inst, step) = detect_basic_iv_step(func, phi_value, step_value)?;
            let (upward, magnitude) = step.direction()?;
            let step_block = func.layout.inst_block(step_inst);
            (ty.is_integral()
                && lpt.loop_of_block(step_block) == Some(lp)
                && domtree.dominates(step_block, latch))
            .then_some(LoopIv {
                phi: phi_value,
                step_value,
                ty,
                upward,
                magnitude,
            })
        })
        .collect();

    lpt.iter_blocks_post_order(cfg, lp).find_map(|block| {
        if lpt.loop_of_block(block) != Some(lp) || !domtree.dominates(block, latch) {
            return None;
        }
        let br = func.dfg.downcast::<&Br>(func.layout.last_inst_of(block)?)?;
        let stay_on_true = lpt.is_in_loop(*br.nz_dest(), lp);
        let iv = (stay_on_true != lpt.is_in_loop(*br.z_dest(), lp))
            .then(|| branch_bounds_loop(func, lpt, lp, *br.cond(), stay_on_true, &ivs))??;
        Some(FiniteLoop {
            header,
            latch,
            iv: iv.phi,
            step: iv.step_value,
            exit: block,
        })
    })
}

/// The one of `ivs` that staying in `lp` while `cond` is `stay_on_true`
/// bounds, if any does.
fn branch_bounds_loop<'a>(
    func: &Function,
    lpt: &LoopTree,
    lp: Loop,
    cond: ValueId,
    stay_on_true: bool,
    ivs: &'a [LoopIv],
) -> Option<&'a LoopIv> {
    let is_iv = |iv: &LoopIv, value| value == iv.phi || value == iv.step_value;
    let unit_iv = |value| {
        ivs.iter()
            .find(|iv| is_iv(iv, value) && iv.magnitude == U256::one())
    };
    let (kind, lhs, rhs, stay) = match normalize_condition(func, &RangeEnv::default(), cond) {
        NormalizedCond::Constant(_) => return None,
        // Staying while a unit-step variable is non-zero: it reaches zero.
        NormalizedCond::Value { value, invert } => {
            return unit_iv(value).filter(|_| stay_on_true != invert);
        }
        NormalizedCond::ZeroTest { value, invert } => {
            return unit_iv(value).filter(|_| stay_on_true == invert);
        }
        NormalizedCond::Compare {
            kind,
            lhs,
            rhs,
            invert,
        } => (kind, lhs, rhs, stay_on_true != invert),
    };

    ivs.iter().find(|iv| {
        let (bound, iv_on_left) = if is_iv(iv, lhs) {
            (rhs, true)
        } else if is_iv(iv, rhs) {
            (lhs, false)
        } else {
            return false;
        };
        if func.dfg.value_ty(bound) != iv.ty
            || !is_loop_invariant_value(func, lpt, lp, bound, &mut FxHashSet::default())
        {
            return false;
        }
        // `normalize_condition` gives only `<`, `<=`, their signed forms, `==`
        // and `!=`; any other kind proves nothing.
        let (strict, signed) = match kind {
            BinaryInstKind::Eq | BinaryInstKind::Ne => {
                // Staying while `!=` holds: a unit step meets the bound.
                return (kind == BinaryInstKind::Ne) == stay && iv.magnitude == U256::one();
            }
            BinaryInstKind::Lt => (true, false),
            BinaryInstKind::Le => (false, false),
            BinaryInstKind::Slt => (true, true),
            BinaryInstKind::Sle => (false, true),
            _ => return false,
        };
        // Staying while the variable is below the bound needs it to go up.
        let (upward, strict) = if stay {
            (iv_on_left, strict)
        } else {
            (!iv_on_left, !strict)
        };
        if upward != iv.upward {
            return false;
        }
        if strict && iv.magnitude == U256::one() {
            return true;
        }
        let Some(bound) = func.dfg.value_const_imm(bound) else {
            return false;
        };
        // Order the bound as an unsigned value in the direction of the step:
        // flip the sign bit for a signed compare and reflect for a downward
        // step. The last value that stays must then step without wrapping.
        let umax = type_mask(iv.ty);
        let mut ordered = imm_to_unsigned(bound);
        if signed {
            ordered ^= umax ^ (umax >> 1usize);
        }
        if !upward {
            ordered ^= umax;
        }
        ordered <= umax - iv.magnitude + U256::from(u8::from(strict))
    })
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

    if func.dfg.downcast::<&Alloca>(inst_id).is_some() {
        return false;
    }

    func.dfg.may_mutate_state(inst_id) || func.dfg.may_transfer_control(inst_id)
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{BlockId, FuncEffectSummary, Module, ir_writer::FuncWriter};

    use crate::{
        analysis::func_behavior,
        object::lowering::{FiniteLoop, FuncSnap, StepKind},
        optim::steps::StepLog,
    };

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

    /// A dead loop over the `i8` induction variable `v1`, starting at `v0`,
    /// that stays in the loop while `v2 = test` is `stay` and steps `v3 = step`.
    fn counted_loop(test: &str, stay: bool, step: &str) -> String {
        let (on_true, on_false) = if stay {
            ("block2", "block3")
        } else {
            ("block3", "block2")
        };
        format!(
            r#"
target = "evm-ethereum-osaka"

func private %f(v0.i8) -> i256 {{
    block0:
        jump block1;

    block1:
        v1.i8 = phi (v0 block0) (v3 block2);
        v2.i1 = {test};
        br v2 {on_true} {on_false};

    block2:
        v3.i8 = {step};
        jump block1;

    block3:
        return 7.i256;
}}
"#
        )
    }

    fn assert_loop_removed(source: &str, removed: bool, what: &str) {
        let (_, dumped) = run_default_adce(source);
        assert_eq!(
            !dumped.contains(" = phi "),
            removed,
            "{what}: expected the loop {}:\n{dumped}",
            if removed { "removed" } else { "kept" }
        );
    }

    #[test]
    fn finiteness_proof_decides_single_loops() {
        for (test, stay, step, removed) in [
            // The comparison must point the way the step goes.
            ("lt v1 100.i8", true, "sub v1 1.i8", false),
            ("slt v1 100.i8", true, "add v1 -1.i8", false),
            ("gt v1 100.i8", true, "add v1 1.i8", false),
            ("sgt v1 100.i8", true, "add v1 1.i8", false),
            // `>=` must leave room for the last step above the type minimum.
            ("ge v1 1.i8", true, "sub v1 1.i8", true),
            ("ge v1 0.i8", true, "sub v1 1.i8", false),
            ("ge v1 v0", true, "sub v1 1.i8", false),
            ("sge v1 -127.i8", true, "add v1 -1.i8", true),
            ("sge v1 -128.i8", true, "add v1 -1.i8", false),
            ("ge v1 2.i8", true, "sub v1 2.i8", true),
            ("ge v1 1.i8", true, "sub v1 2.i8", false),
            // `<=` must leave room below the type maximum.
            ("le v1 -2.i8", true, "add v1 1.i8", true),
            ("le v1 -1.i8", true, "add v1 1.i8", false),
            // The branch polarity and the side of the induction variable.
            ("lt v1 v0", false, "add v1 1.i8", false),
            ("ge v1 v0", false, "add v1 1.i8", true),
            ("gt v0 v1", true, "add v1 1.i8", true),
            ("lt v0 v1", true, "add v1 1.i8", false),
            // `!=` holds only for a unit step; staying on `==` is not proven.
            ("ne v1 v0", true, "add v1 1.i8", true),
            ("ne v1 v0", true, "sub v1 1.i8", true),
            ("ne v1 v0", true, "add v1 2.i8", false),
            ("eq v1 v0", true, "add v1 1.i8", false),
            ("eq v1 v0", false, "add v1 1.i8", true),
        ] {
            let what = format!("`{test}` staying on {stay} with `{step}`");
            assert_loop_removed(&counted_loop(test, stay, step), removed, &what);
        }
    }

    #[test]
    fn steps_list_the_finite_loops_a_round_may_remove() {
        let parsed = parse_module(&counted_loop("le v1 -2.i8", true, "add v1 1.i8"));
        let func_ref = only_func_ref(&parsed.module);
        let value = |name| parsed.debug.value(func_ref, name).unwrap();
        let mut log = parsed.module.func_store.view(func_ref, |func| {
            StepLog::new(FuncSnap::capture(func_ref, func))
        });
        parsed.module.func_store.modify(func_ref, |func| {
            AdceSolver::new().run_with_steps(func, Some(&mut log), 0)
        });
        let (kind, _, _, step) = &log.steps[0];
        assert_eq!(*kind, StepKind::Adce);
        assert_eq!(
            step.as_ref()
                .expect("the loop is removed")
                .facts
                .finite_loops,
            [FiniteLoop {
                header: BlockId(1),
                latch: BlockId(2),
                iv: value("v1"),
                step: value("v3"),
                exit: BlockId(1),
            }]
        );
    }

    #[test]
    fn finiteness_proof_rejects_unproven_shapes() {
        let variant_bound = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v3 block2);
        v4.i256 = phi (v0 block0) (v5 block2);
        v2.i1 = lt v1 v4;
        br v2 block2 block3;

    block2:
        v3.i256 = add v1 1.i256;
        v5.i256 = add v4 1.i256;
        jump block1;

    block3:
        return 7.i256;
}
"#;
        let two_latches = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256, v1.i1) -> i256 {
    block0:
        jump block1;

    block1:
        v2.i256 = phi (0.i256 block0) (v4 block2) (v4 block4);
        v3.i1 = lt v2 v0;
        br v3 block2 block3;

    block2:
        v4.i256 = add v2 1.i256;
        br v1 block1 block4;

    block4:
        jump block1;

    block3:
        return 7.i256;
}
"#;
        let test_off_every_path = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256, v1.i1) -> i256 {
    block0:
        jump block1;

    block1:
        v2.i256 = phi (0.i256 block0) (v4 block4);
        br v1 block2 block4;

    block2:
        v3.i1 = lt v2 v0;
        br v3 block4 block3;

    block4:
        v4.i256 = add v2 1.i256;
        jump block1;

    block3:
        return 7.i256;
}
"#;
        let derived_test = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v3 block2);
        v4.i256 = mul v1 2.i256;
        v2.i1 = lt v4 v0;
        br v2 block2 block3;

    block2:
        v3.i256 = add v1 1.i256;
        jump block1;

    block3:
        return 7.i256;
}
"#;
        let unproven_inner = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v2.i256 = phi (0.i256 block0) (v4 block5);
        v3.i1 = lt v2 v0;
        br v3 block2 block6;

    block2:
        v5.i256 = phi (0.i256 block1) (v7 block3);
        v6.i1 = ne v5 v1;
        br v6 block3 block5;

    block3:
        v7.i256 = add v5 2.i256;
        jump block2;

    block5:
        v4.i256 = add v2 1.i256;
        jump block1;

    block6:
        return 7.i256;
}
"#;
        for (what, source) in [
            ("a bound that is not loop-invariant", variant_bound),
            ("two latches", two_latches),
            (
                "an exit test that does not dominate the latch",
                test_off_every_path,
            ),
            ("a test of `i * 2`", derived_test),
            (
                "an outer loop around an unproven inner loop",
                unproven_inner,
            ),
        ] {
            assert_loop_removed(source, false, what);
        }
    }

    #[test]
    fn finiteness_proof_accepts_bound_computed_in_loop_from_invariants() {
        // `v4` is computed in the loop, but from `v0` and a constant only.
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v3 block2);
        v4.i256 = add v0 1.i256;
        v2.i1 = lt v1 v4;
        br v2 block2 block3;

    block2:
        v3.i256 = add v1 1.i256;
        jump block1;

    block3:
        return 7.i256;
}
"#;
        assert_loop_removed(source, true, "a bound computed in the loop from invariants");
    }

    #[test]
    fn finiteness_proof_accepts_outer_latch_at_inner_header() {
        // `block2` heads the inner loop and is the outer loop's latch.
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v2.i256 = phi (0.i256 block0) (v4 block2);
        v3.i1 = lt v2 v0;
        br v3 block5 block4;

    block5:
        v4.i256 = add v2 1.i256;
        jump block2;

    block2:
        v5.i256 = phi (0.i256 block5) (v7 block3);
        v6.i1 = lt v5 v1;
        br v6 block3 block1;

    block3:
        v7.i256 = add v5 1.i256;
        jump block2;

    block4:
        return 7.i256;
}
"#;
        assert_loop_removed(source, true, "an outer latch at an inner header");
    }

    #[test]
    fn finite_loop_with_effects_is_kept() {
        let store = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v3 block2);
        v2.i1 = lt v1 v0;
        br v2 block2 block3;

    block2:
        evm_mstore v1 v1;
        v3.i256 = add v1 1.i256;
        jump block1;

    block3:
        return 7.i256;
}
"#;
        let (_, dumped) = run_default_adce(store);
        assert!(
            dumped.contains("evm_mstore v1 v1;") && dumped.contains(" = phi "),
            "ADCE must keep a finite loop that stores:\n{dumped}"
        );

        let call = r#"
target = "evm-ethereum-osaka"

func private %maybe_spin(v0.i256) {
    block0:
        v1.i1 = is_zero v0;
        br v1 block1 block2;

    block1:
        jump block1;

    block2:
        return;
}

func public %f(v0.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v3 block2);
        v2.i1 = lt v1 v0;
        br v2 block2 block3;

    block2:
        call %maybe_spin v1;
        v3.i256 = add v1 1.i256;
        jump block1;

    block3:
        return 7.i256;
}
"#;
        let parsed = parse_module(call);
        func_behavior::analyze_module(&parsed.module);
        let func_ref = find_func(&parsed.module, "f");
        parsed.module.func_store.modify(func_ref, |func| {
            AdceSolver::with_call_policy(AdceCallPolicy::UseCurrentFuncEffects).run(func);
        });
        let dumped = parsed.module.func_store.view(func_ref, |func| {
            FuncWriter::new(func_ref, func).dump_string()
        });
        assert!(
            dumped.contains("call %maybe_spin v1;") && dumped.contains(" = phi "),
            "ADCE must keep a finite loop that calls a function that may not return:\n{dumped}"
        );
    }

    #[test]
    fn removes_empty_mcopy_and_dead_addresses_but_keeps_operand_effects() {
        let source = r#"
target = "evm-ethereum-osaka"
func private %f(v0.i256) -> i256 {
block0:
    evm_sstore 7.i256 v0;
    v1.i256 = add v0 32.i256;
    v2.i256 = evm_mload v1;
    evm_mcopy v1 v2 0.i256;
    v3.i256 = call %f v0;
    evm_mcopy v3 v3 0.i256;
    evm_mcopy v0 v0 1.i256;
    evm_mcopy v0 v0 v0;
    evm_return_data_copy v0 1.i256 0.i256;
    return v0;
}
"#;
        let (changed, dumped) = run_default_adce(source);
        assert!(changed);
        assert!(
            !dumped.contains("add ") && !dumped.contains("evm_mload"),
            "{dumped}"
        );
        assert_eq!(dumped.matches("evm_mcopy").count(), 2, "{dumped}");
        assert!(dumped.contains("evm_sstore 7.i256 v0;"), "{dumped}");
        assert!(dumped.contains("call %f v0;"), "{dumped}");
        assert!(
            dumped.contains("evm_return_data_copy v0 1.i256 0.i256;"),
            "{dumped}"
        );
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
    fn removes_unused_alloca() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f() {
    block0:
        v0.*i256 = alloca i256;
        return;
}
"#;

        let (changed, dumped) = run_default_adce(source);

        assert!(changed);
        assert!(
            !dumped.contains("alloca"),
            "unused alloca should not be an ADCE root:\n{dumped}"
        );
    }

    #[test]
    fn keeps_alloca_used_by_live_instruction() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f() -> i256 {
    block0:
        v0.*i256 = alloca i256;
        mstore v0 42.i256 i256;
        v1.i256 = mload v0 i256;
        return v1;
}
"#;

        let (changed, dumped) = run_default_adce(source);

        assert!(!changed);
        assert!(
            dumped.contains("alloca"),
            "live pointer users should keep alloca live:\n{dumped}"
        );
    }

    #[test]
    fn removes_dead_ssa_cycle_in_live_blocks() {
        let source = r#"
target = "evm-ethereum-osaka"

type @pair = {i256, i256};

func private %f(v0.i1) {
    block0:
        v2.@pair = agg.make @pair 4.i256 4.i256;
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

    #[test]
    fn preserves_unproven_loop_with_exit_but_removes_dead_body_insts() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256, v1.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v2.i256 = phi (v0 block0) (v4 block2);
        v3.i1 = ne v2 v1;
        br v3 block2 block3;

    block2:
        v5.i256 = mul v2 3.i256;
        v4.i256 = add v2 2.i256;
        jump block1;

    block3:
        return 7.i256;
}
"#;

        let (changed, dumped) = run_default_adce(source);
        assert!(changed, "dead mul inside loop should be removed:\n{dumped}");
        assert!(
            !dumped.contains("mul "),
            "ADCE should still remove dead pure instructions inside preserved loops:\n{dumped}"
        );
        assert!(
            dumped.contains("ne v2 v1")
                && dumped.contains("add v2 2.i256")
                && dumped.contains("jump block1;"),
            "ADCE must preserve loops with step 2 and dynamic != bound:\n{dumped}"
        );
    }

    #[test]
    fn removes_dead_proven_finite_unsigned_range_loop() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v3 block2);
        v2.i1 = lt v1 v0;
        br v2 block2 block3;

    block2:
        v4.i256 = mul v1 3.i256;
        v3.i256 = add v1 1.i256;
        jump block1;

    block3:
        return 7.i256;
}
"#;

        let (changed, dumped) = run_default_adce(source);
        assert!(changed);
        assert!(
            !dumped.contains("phi") && !dumped.contains("lt ") && !dumped.contains("add "),
            "ADCE should eliminate dead finite unsigned range loop:\n{dumped}"
        );
        assert!(dumped.contains("return 7.i256;"), "{dumped}");
    }

    #[test]
    fn removes_dead_proven_finite_latch_tested_rotated_loop() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i256) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i256 = phi (0.i256 block0) (v2 block1);
        v2.i256 = add v1 1.i256;
        v3.i1 = lt v2 v0;
        br v3 block1 block2;

    block2:
        return 9.i256;
}
"#;

        let (changed, dumped) = run_default_adce(source);
        assert!(changed);
        assert!(
            !dumped.contains("phi") && !dumped.contains("br "),
            "ADCE should eliminate dead rotated finite loop:\n{dumped}"
        );
        assert!(dumped.contains("return 9.i256;"), "{dumped}");
    }

    #[test]
    fn removes_dead_proven_finite_countdown_and_ne_unit_step_loops() {
        let source_sub = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i64, v1.i64) -> i256 {
    block0:
        jump block1;

    block1:
        v2.i64 = phi (v0 block0) (v4 block2);
        v3.i1 = gt v2 v1;
        br v3 block2 block3;

    block2:
        v4.i64 = add v2 -1.i64;
        jump block1;

    block3:
        return 1.i256;
}
"#;
        let (changed, dumped) = run_default_adce(source_sub);
        assert!(changed);
        assert!(
            !dumped.contains("phi") && !dumped.contains("gt "),
            "ADCE should eliminate countdown loop using add -1:\n{dumped}"
        );

        let source_is_zero = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i64) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i64 = phi (v0 block0) (v3 block2);
        v2.i1 = is_zero v1;
        br v2 block3 block2;

    block2:
        v3.i64 = sub v1 1.i64;
        jump block1;

    block3:
        return 2.i256;
}
"#;
        let (changed, dumped) = run_default_adce(source_is_zero);
        assert!(changed);
        assert!(
            !dumped.contains("phi") && !dumped.contains("is_zero"),
            "ADCE should eliminate unit-step countdown tested with is_zero:\n{dumped}"
        );
    }

    #[test]
    fn preserves_wrapping_hazard_loops_and_removes_safe_const_bound_loops() {
        // Dynamic <= bound can be UMAX, wrapping i += 1 forever.
        let dynamic_le = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i8) -> i256 {
    block0:
        jump block1;

    block1:
        v1.i8 = phi (0.i8 block0) (v3 block2);
        v2.i1 = le v1 v0;
        br v2 block2 block3;

    block2:
        v3.i8 = add v1 1.i8;
        jump block1;

    block3:
        return 0.i256;
}
"#;
        let (_, dumped) = run_default_adce(dynamic_le);
        assert!(
            dumped.contains("le v1 v0") && dumped.contains("jump block1;"),
            "ADCE must preserve dynamic <= loop (wrap hazard at UMAX):\n{dumped}"
        );

        // Step 2 with bound 255 on i8 can wrap (254 + 2 == 0 < 255).
        let unsafe_step2 = r#"
target = "evm-ethereum-osaka"

func private %f() -> i256 {
    block0:
        jump block1;

    block1:
        v1.i8 = phi (0.i8 block0) (v3 block2);
        v2.i1 = lt v1 -1.i8;
        br v2 block2 block3;

    block2:
        v3.i8 = add v1 2.i8;
        jump block1;

    block3:
        return 0.i256;
}
"#;
        let (_, dumped) = run_default_adce(unsafe_step2);
        assert!(
            dumped.contains("lt v0 -1.i8") && dumped.contains("jump block1;"),
            "ADCE must preserve i8 loop with lt 255 and step 2:\n{dumped}"
        );

        // Step 2 with bound 254 (-2i8) on i8 cannot wrap (max 253 + 2 = 255 >= 254).
        let safe_step2 = r#"
target = "evm-ethereum-osaka"

func private %f() -> i256 {
    block0:
        jump block1;

    block1:
        v1.i8 = phi (0.i8 block0) (v3 block2);
        v2.i1 = lt v1 -2.i8;
        br v2 block2 block3;

    block2:
        v3.i8 = add v1 2.i8;
        jump block1;

    block3:
        return 0.i256;
}
"#;
        let (changed, dumped) = run_default_adce(safe_step2);
        assert!(changed);
        assert!(
            !dumped.contains("phi") && !dumped.contains("lt "),
            "ADCE should eliminate i8 loop with lt 254 and step 2:\n{dumped}"
        );

        // Signed <= 126 with step 1 on i8 is safe; <= 127 wraps.
        let safe_sle = r#"
target = "evm-ethereum-osaka"

func private %f() -> i256 {
    block0:
        jump block1;

    block1:
        v1.i8 = phi (-128.i8 block0) (v3 block2);
        v2.i1 = sle v1 126.i8;
        br v2 block2 block3;

    block2:
        v3.i8 = add v1 1.i8;
        jump block1;

    block3:
        return 0.i256;
}
"#;
        let (changed, dumped) = run_default_adce(safe_sle);
        assert!(changed);
        assert!(
            !dumped.contains("phi") && !dumped.contains("sle "),
            "ADCE should eliminate i8 loop with sle 126 and step 1:\n{dumped}"
        );

        let unsafe_sle = r#"
target = "evm-ethereum-osaka"

func private %f() -> i256 {
    block0:
        jump block1;

    block1:
        v1.i8 = phi (-128.i8 block0) (v3 block2);
        v2.i1 = sle v1 127.i8;
        br v2 block2 block3;

    block2:
        v3.i8 = add v1 1.i8;
        jump block1;

    block3:
        return 0.i256;
}
"#;
        let (_, dumped) = run_default_adce(unsafe_sle);
        assert!(
            dumped.contains("sle v0 127.i8") && dumped.contains("jump block1;"),
            "ADCE must preserve i8 loop with sle 127 and step 1:\n{dumped}"
        );
    }

    #[test]
    fn preserves_irreducible_cycle_with_exit() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i1, v1.i1, v2.i1) -> i256 {
    block0:
        br v0 block1 block2;

    block1:
        br v1 block2 block3;

    block2:
        br v2 block1 block3;

    block3:
        return 5.i256;
}
"#;

        let (_, dumped) = run_default_adce(source);
        assert!(
            dumped.contains("br v1 block2 block3;") && dumped.contains("br v2 block1 block3;"),
            "ADCE must preserve irreducible cycles with an exit:\n{dumped}"
        );
    }

    #[test]
    fn eliminates_finite_inner_loop_inside_preserved_outer_loop() {
        let source = r#"
target = "evm-ethereum-osaka"

func private %f(v0.i1, v1.i256) -> i256 {
    block0:
        jump block1;

    block1:
        br v0 block2 block5;

    block2:
        v2.i256 = phi (0.i256 block1) (v4 block3);
        v3.i1 = lt v2 v1;
        br v3 block3 block4;

    block3:
        v4.i256 = add v2 1.i256;
        jump block2;

    block4:
        jump block1;

    block5:
        return 3.i256;
}
"#;

        let (changed, dumped) = run_default_adce(source);
        assert!(changed);
        assert!(
            !dumped.contains("phi") && !dumped.contains("lt ") && !dumped.contains("add "),
            "ADCE should eliminate dead proven-finite inner loop:\n{dumped}"
        );
        assert!(
            dumped.contains("br v0 "),
            "ADCE must keep unproven outer loop:\n{dumped}"
        );
    }
}
