use std::collections::BTreeSet;

use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::control_flow::Jump,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CleanupMode {
    Strict,
    RepairWithUndef,
}

/// Structured CFG editing helpers that keep CFG preds and phi incoming sets consistent.
///
/// Passes that mutate terminators directly without repairing successor phis should run a
/// cleanup pass (e.g. `CfgCleanup`) before relying on CFG/phi invariants.
pub struct CfgEditor<'f> {
    func: &'f mut Function,
    cfg: ControlFlowGraph,
    mode: CleanupMode,
}

impl<'f> CfgEditor<'f> {
    pub fn new(func: &'f mut Function, mode: CleanupMode) -> Self {
        let mut cfg = ControlFlowGraph::default();
        cfg.compute(func);
        Self { func, cfg, mode }
    }

    pub fn func(&self) -> &Function {
        self.func
    }

    pub fn func_mut(&mut self) -> &mut Function {
        self.func
    }

    pub fn cfg(&self) -> &ControlFlowGraph {
        &self.cfg
    }

    pub fn recompute_cfg(&mut self) {
        self.cfg.compute(self.func);
    }

    pub fn trim_after_terminator(&mut self) -> bool {
        let mut changed = false;

        let blocks: Vec<_> = self.func.layout.iter_block().collect();
        for block in blocks {
            let mut found_term = false;
            let mut next_inst = self.func.layout.first_inst_of(block);
            while let Some(inst) = next_inst {
                next_inst = self.func.layout.next_inst_of(inst);
                if found_term {
                    InstInserter::at_location(CursorLocation::At(inst)).remove_inst(self.func);
                    changed = true;
                    continue;
                }

                found_term = self.func.dfg.is_terminator(inst);
            }
        }

        if changed {
            self.recompute_cfg();
        }
        changed
    }

    pub fn remove_succ(&mut self, from: BlockId, to: BlockId) -> bool {
        let Some(term) = self.func.layout.last_inst_of(from) else {
            panic!("block {from:?} has no terminator");
        };
        assert!(
            self.func.dfg.is_terminator(term),
            "block {from:?} does not end with a terminator"
        );

        let Some(branch_info) = self.func.dfg.branch_info(term) else {
            return false;
        };

        if !branch_info.dests().into_iter().any(|dest| dest == to) {
            return false;
        }

        self.func.dfg.remove_branch_dest(term, to);

        if !self.func.layout.is_block_inserted(to) {
            if matches!(self.mode, CleanupMode::Strict) {
                panic!("branch target {to:?} is not inserted");
            }
            self.recompute_cfg();
            return true;
        }

        remove_phi_incoming_from(self.func, to, from);
        simplify_trivial_phis_in_block(self.func, to);

        self.recompute_cfg();
        true
    }

    pub fn remove_edge(&mut self, from: BlockId, to: BlockId) -> bool {
        self.remove_succ(from, to)
    }

    pub fn split_block_at(&mut self, at: InstId) -> (BlockId, BlockId) {
        assert!(self.func.layout.is_inst_inserted(at));
        assert!(!self.func.dfg.is_phi(at), "cannot split at a phi");

        let from = self.func.layout.inst_block(at);
        let Some(term) = self.func.layout.last_inst_of(from) else {
            panic!("block {from:?} has no terminator");
        };
        assert!(
            self.func.dfg.is_terminator(term),
            "block {from:?} does not end with a terminator"
        );

        let succs: BTreeSet<_> = self
            .func
            .dfg
            .branch_info(term)
            .map_or_else(BTreeSet::new, |bi| bi.dests().into_iter().collect());

        let new_block = self.func.dfg.make_block();
        InstInserter::at_location(CursorLocation::BlockTop(from))
            .insert_block(self.func, new_block);

        let mut insts = Vec::new();
        let mut next_inst = Some(at);
        while let Some(inst) = next_inst {
            insts.push(inst);
            next_inst = self.func.layout.next_inst_of(inst);
        }
        for inst in insts {
            self.func.layout.remove_inst(inst);
            self.func.layout.append_inst(inst, new_block);
        }

        assert!(
            !self
                .func
                .layout
                .last_inst_of(from)
                .is_some_and(|inst| self.func.dfg.is_terminator(inst)),
            "split moved range did not include the terminator of {from:?}"
        );

        InstInserter::at_location(CursorLocation::BlockBottom(from))
            .insert_inst_data(self.func, self.func.dfg.make_jump(new_block));

        for succ in succs {
            if !self.func.layout.is_block_inserted(succ) {
                if matches!(self.mode, CleanupMode::Strict) {
                    panic!("branch target {succ:?} is not inserted");
                }
                continue;
            }

            replace_phi_incoming_block(self.func, succ, from, new_block);
            simplify_trivial_phis_in_block(self.func, succ);
        }

        self.recompute_cfg();
        (from, new_block)
    }

    pub fn split_edge(&mut self, from: BlockId, to: BlockId) -> BlockId {
        assert!(self.func.layout.is_block_inserted(from));
        assert!(self.func.layout.is_block_inserted(to));

        let Some(term) = self.func.layout.last_inst_of(from) else {
            panic!("block {from:?} has no terminator");
        };
        assert!(
            self.func.dfg.is_terminator(term),
            "block {from:?} does not end with a terminator"
        );

        let Some(branch_info) = self.func.dfg.branch_info(term) else {
            panic!("terminator {term:?} has no branch info");
        };
        assert!(
            branch_info.dests().into_iter().any(|dest| dest == to),
            "edge {from:?} -> {to:?} does not exist"
        );

        let mid = self.func.dfg.make_block();
        let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(to));
        cursor.insert_block_before(self.func, mid);
        cursor.set_location(CursorLocation::BlockTop(mid));
        cursor.append_inst_data(self.func, Jump::new(self.func.dfg.inst_set().jump(), to));

        self.func.dfg.rewrite_branch_dest(term, to, mid);
        replace_phi_incoming_block(self.func, to, from, mid);

        self.recompute_cfg();
        mid
    }

    /// Create or reuse a loop preheader for `lp_header` using predecessors outside the loop.
    ///
    /// Returns:
    /// - `Some(preheader)` when an existing preheader can be reused or a new one is created.
    /// - `None` in the entry-header edge case where preheader creation is not valid.
    pub fn create_or_reuse_loop_preheader(
        &mut self,
        lp_header: BlockId,
        outside_preds: &[BlockId],
    ) -> Option<BlockId> {
        assert!(self.func.layout.is_block_inserted(lp_header));

        let is_entry_header = self.func.layout.entry_block() == Some(lp_header);
        let header_starts_with_phi = self
            .func
            .layout
            .first_inst_of(lp_header)
            .is_some_and(|inst| self.func.dfg.is_phi(inst));
        if outside_preds.is_empty() && (!is_entry_header || header_starts_with_phi) {
            return None;
        }

        if outside_preds.len() == 1 && self.cfg.succs_of(outside_preds[0]).count() == 1 {
            return Some(outside_preds[0]);
        }

        let new_preheader = self.func.dfg.make_block();
        let mut inserter = InstInserter::at_location(CursorLocation::BlockTop(lp_header));
        inserter.insert_block_before(self.func, new_preheader);

        inserter.set_location(CursorLocation::BlockTop(new_preheader));
        inserter.append_inst_data(
            self.func,
            Jump::new(self.func.dfg.inst_set().jump(), lp_header),
        );

        for &pred in outside_preds {
            assert!(
                self.func.layout.is_block_inserted(pred),
                "preheader predecessor {pred:?} is not inserted"
            );

            let Some(last_inst) = self.func.layout.last_inst_of(pred) else {
                panic!("block {pred:?} has no terminator");
            };
            assert!(
                self.func.dfg.is_terminator(last_inst),
                "block {pred:?} does not end with a terminator"
            );

            let Some(branch_info) = self.func.dfg.branch_info(last_inst) else {
                panic!("terminator {last_inst:?} has no branch info");
            };
            assert!(
                branch_info
                    .dests()
                    .into_iter()
                    .any(|dest| dest == lp_header),
                "edge {pred:?} -> {lp_header:?} does not exist"
            );

            self.func
                .dfg
                .rewrite_branch_dest(last_inst, lp_header, new_preheader);
        }

        self.rewrite_loop_header_phis_for_preheader(lp_header, outside_preds, new_preheader);
        self.recompute_cfg();
        Some(new_preheader)
    }

    pub fn fold_trampoline_block(&mut self, block: BlockId) -> bool {
        if !self.func.layout.is_block_inserted(block)
            || self.func.layout.entry_block() == Some(block)
        {
            return false;
        }

        let Some(term) = self.func.layout.last_inst_of(block) else {
            return false;
        };
        let Some(jump) = self.func.dfg.cast_jump(term) else {
            return false;
        };
        let succ = *jump.dest();

        if self.func.layout.first_inst_of(block) != Some(term) {
            return false;
        }

        let preds: Vec<_> = self.cfg.preds_of(block).copied().collect();
        let [pred] = preds.as_slice() else {
            return false;
        };
        let pred = *pred;
        if pred == succ {
            return false;
        }

        if iter_phis_in_block(self.func, succ).any(|phi_inst| {
            self.func
                .dfg
                .cast_phi(phi_inst)
                .unwrap()
                .args()
                .iter()
                .any(|(_, b)| *b == pred)
        }) {
            return false;
        }

        let Some(pred_term) = self.func.layout.last_inst_of(pred) else {
            panic!("block {pred:?} has no terminator");
        };
        assert!(
            self.func.dfg.is_terminator(pred_term),
            "block {pred:?} does not end with a terminator"
        );
        let Some(pred_branch) = self.func.dfg.branch_info(pred_term) else {
            return false;
        };
        if !pred_branch.dests().into_iter().any(|dest| dest == block) {
            return false;
        }

        self.func.dfg.rewrite_branch_dest(pred_term, block, succ);
        replace_phi_incoming_block(self.func, succ, block, pred);
        simplify_trivial_phis_in_block(self.func, succ);
        InstInserter::at_location(CursorLocation::BlockTop(block)).remove_block(self.func);

        self.recompute_cfg();
        true
    }

    pub fn delete_block_unreachable(&mut self, b: BlockId) -> bool {
        if !self.func.layout.is_block_inserted(b) {
            return false;
        }

        let preds: Vec<_> = self.cfg.preds_of(b).copied().collect();
        for pred in preds {
            if self.func.layout.is_block_inserted(pred) {
                let removed = self.remove_edge(pred, b);
                assert!(removed, "edge {pred:?} -> {b:?} does not exist");
            }
        }

        let succs: Vec<_> = self.cfg.succs_of(b).copied().collect();
        for succ in succs {
            if self.func.layout.is_block_inserted(succ) {
                remove_phi_incoming_from(self.func, succ, b);
                simplify_trivial_phis_in_block(self.func, succ);
            }
        }

        InstInserter::at_location(CursorLocation::BlockTop(b)).remove_block(self.func);
        self.recompute_cfg();
        true
    }

    pub fn replace_succ(
        &mut self,
        from: BlockId,
        old_to: BlockId,
        new_to: BlockId,
        phi_inputs: &[(InstId, ValueId)],
    ) {
        let replaced = self.replace_succ_inner(from, old_to, new_to, phi_inputs, false);
        assert!(replaced, "edge {from:?} -> {old_to:?} does not exist");
    }

    /// Replace successor `old_to` with `new_to`.
    ///
    /// Unlike [`replace_succ`], this variant allows retargeting to a destination that
    /// already has `from` as a predecessor. In that case, `phi_inputs` must be empty.
    pub fn replace_succ_allow_existing_pred(
        &mut self,
        from: BlockId,
        old_to: BlockId,
        new_to: BlockId,
        phi_inputs: &[(InstId, ValueId)],
    ) -> bool {
        self.replace_succ_inner(from, old_to, new_to, phi_inputs, true)
    }

    pub fn retarget_edge_with_phi_mapping(
        &mut self,
        from: BlockId,
        old_to: BlockId,
        new_to: BlockId,
        phi_inputs: &[(InstId, ValueId)],
    ) {
        self.replace_succ(from, old_to, new_to, phi_inputs)
    }

    fn replace_succ_inner(
        &mut self,
        from: BlockId,
        old_to: BlockId,
        new_to: BlockId,
        phi_inputs: &[(InstId, ValueId)],
        allow_existing_pred: bool,
    ) -> bool {
        assert!(self.func.layout.is_block_inserted(from));
        assert!(self.func.layout.is_block_inserted(new_to));
        let old_to_inserted = self.func.layout.is_block_inserted(old_to);
        if !old_to_inserted && matches!(self.mode, CleanupMode::Strict) {
            panic!("branch target {old_to:?} is not inserted");
        }

        let Some(term) = self.func.layout.last_inst_of(from) else {
            panic!("block {from:?} has no terminator");
        };
        assert!(
            self.func.dfg.is_terminator(term),
            "block {from:?} does not end with a terminator"
        );

        let Some(branch_info) = self.func.dfg.branch_info(term) else {
            panic!("terminator {term:?} has no branch info");
        };
        if !branch_info.dests().into_iter().any(|dest| dest == old_to) {
            return false;
        }

        let from_already_preds_new_to = self.cfg.preds_of(new_to).any(|pred| *pred == from);

        self.func.dfg.rewrite_branch_dest(term, old_to, new_to);

        if old_to_inserted {
            remove_phi_incoming_from(self.func, old_to, from);
            simplify_trivial_phis_in_block(self.func, old_to);
        }

        if from_already_preds_new_to && allow_existing_pred {
            assert!(
                phi_inputs.is_empty(),
                "phi mapping must be empty when {from:?} already precedes {new_to:?}"
            );
        } else {
            let expected: BTreeSet<_> = iter_phis_in_block(self.func, new_to).collect();
            let provided: BTreeSet<_> = phi_inputs.iter().map(|(phi, _)| *phi).collect();
            assert_eq!(expected, provided, "phi mapping is incomplete");

            for &(phi_inst, incoming) in phi_inputs {
                self.func.dfg.untrack_inst(phi_inst);
                let phi = self.func.dfg.cast_phi_mut(phi_inst).unwrap();
                assert!(
                    !phi.args().iter().any(|(_, pred)| *pred == from),
                    "phi {phi_inst:?} already has incoming from {from:?}"
                );
                phi.append_phi_arg(incoming, from);
                self.func.dfg.attach_user(phi_inst);
            }
        }

        self.recompute_cfg();
        true
    }

    fn rewrite_loop_header_phis_for_preheader(
        &mut self,
        lp_header: BlockId,
        outside_preds: &[BlockId],
        new_preheader: BlockId,
    ) {
        if outside_preds.is_empty() {
            return;
        }

        let mut inserted_phis = FxHashMap::default();

        let mut next_inst = self.func.layout.first_inst_of(lp_header);
        while let Some(phi_inst_id) = next_inst {
            if self.func.dfg.cast_phi(phi_inst_id).is_none() {
                break;
            }

            let phi_result = self
                .func
                .dfg
                .inst_result(phi_inst_id)
                .unwrap_or_else(|| panic!("phi {phi_inst_id:?} has no result"));
            let phi_ty = self.func.dfg.value_ty(phi_result);

            let mut new_phi = self.func.dfg.make_phi(vec![]);
            self.func.dfg.untrack_inst(phi_inst_id);
            let old_phi = self.func.dfg.cast_phi_mut(phi_inst_id).unwrap();

            for &pred in outside_preds {
                let value = old_phi.remove_phi_arg(pred).unwrap_or_else(|| {
                    panic!("phi {phi_inst_id:?} in {lp_header:?} missing incoming from {pred:?}")
                });
                new_phi.append_phi_arg(value, pred);
            }

            let preheader_phi_result = match inserted_phis.get(&new_phi) {
                Some(&value) => value,
                None => {
                    let mut inserter =
                        InstInserter::at_location(CursorLocation::BlockTop(new_preheader));
                    let new_phi_inst = inserter.insert_inst_data(self.func, new_phi.clone());
                    let result = inserter.make_result(self.func, new_phi_inst, phi_ty);
                    inserter.attach_result(self.func, new_phi_inst, result);
                    inserted_phis.insert(new_phi, result);
                    result
                }
            };

            self.func
                .dfg
                .append_phi_arg(phi_inst_id, preheader_phi_result, new_preheader);
            next_inst = self.func.layout.next_inst_of(phi_inst_id);
        }
    }
}

fn iter_phis_in_block(func: &Function, block: BlockId) -> impl Iterator<Item = InstId> + '_ {
    let mut next_inst = func.layout.first_inst_of(block);
    std::iter::from_fn(move || {
        let inst = next_inst?;
        func.dfg.cast_phi(inst)?;
        next_inst = func.layout.next_inst_of(inst);
        Some(inst)
    })
}

pub(crate) fn remove_phi_incoming_from(func: &mut Function, block: BlockId, pred: BlockId) {
    for phi_inst in iter_phis_in_block(func, block).collect::<Vec<_>>() {
        func.dfg.untrack_inst(phi_inst);
        let phi = func.dfg.cast_phi_mut(phi_inst).unwrap();
        phi.retain(|b| b != pred);
        func.dfg.attach_user(phi_inst);
    }
}

fn replace_phi_incoming_block(
    func: &mut Function,
    block: BlockId,
    old_pred: BlockId,
    new_pred: BlockId,
) {
    for phi_inst in iter_phis_in_block(func, block).collect::<Vec<_>>() {
        let phi = func.dfg.cast_phi_mut(phi_inst).unwrap();
        assert!(
            !phi.args().iter().any(|(_, pred)| *pred == new_pred),
            "phi {phi_inst:?} already has incoming from {new_pred:?}"
        );
        let mut replaced = false;
        for (_, pred) in phi.args_mut() {
            if *pred == old_pred {
                *pred = new_pred;
                replaced = true;
            }
        }
        assert!(
            replaced,
            "phi {phi_inst:?} in {block:?} missing incoming from {old_pred:?}"
        );
    }
}

pub(crate) fn simplify_trivial_phis_in_block(func: &mut Function, block: BlockId) -> bool {
    let mut changed = false;
    let mut next_inst = func.layout.first_inst_of(block);
    while let Some(phi_inst) = next_inst {
        next_inst = func.layout.next_inst_of(phi_inst);
        if func.dfg.cast_phi(phi_inst).is_none() {
            break;
        }
        changed |= simplify_trivial_phi(func, phi_inst);
    }
    changed
}

pub(crate) fn simplify_trivial_phi(func: &mut Function, phi_inst: InstId) -> bool {
    let phi_value = func.dfg.inst_result(phi_inst).expect("phi has no result");
    let ty = func.dfg.value_ty(phi_value);

    let phi = func.dfg.cast_phi(phi_inst).unwrap();
    let arg = match phi.args().first() {
        None => func.dfg.make_undef_value(ty),
        Some(&(first, _)) if phi.args().iter().all(|(value, _)| *value == first) => {
            if first == phi_value {
                func.dfg.make_undef_value(ty)
            } else {
                first
            }
        }
        _ => return false,
    };

    func.dfg.change_to_alias(phi_value, arg);
    InstInserter::at_location(CursorLocation::At(phi_inst)).remove_inst(func);
    true
}

pub fn prune_phi_to_preds(
    func: &mut Function,
    block: BlockId,
    preds: &BTreeSet<BlockId>,
    mode: CleanupMode,
) -> bool {
    let mut changed = false;

    for phi_inst in iter_phis_in_block(func, block).collect::<Vec<_>>() {
        func.dfg.untrack_inst(phi_inst);
        let phi_result = func.dfg.inst_result(phi_inst).expect("phi has no result");
        let ty = func.dfg.value_ty(phi_result);
        let mut missing = Vec::new();
        {
            let phi = func.dfg.cast_phi_mut(phi_inst).unwrap();
            let old_len = phi.args().len();
            phi.retain(|pred| preds.contains(&pred));
            changed |= phi.args().len() != old_len;

            let mut seen = BTreeSet::new();
            for &(_, pred) in phi.args() {
                assert!(
                    seen.insert(pred),
                    "phi {phi_inst:?} in {block:?} has duplicate incoming from {pred:?}"
                );
            }

            for &pred in preds {
                if seen.contains(&pred) {
                    continue;
                }

                match mode {
                    CleanupMode::Strict => {
                        panic!("phi {phi_inst:?} in {block:?} missing incoming from {pred:?}");
                    }
                    CleanupMode::RepairWithUndef => missing.push(pred),
                }
            }
        }

        if matches!(mode, CleanupMode::RepairWithUndef) && !missing.is_empty() {
            let undef = func.dfg.make_undef_value(ty);
            let phi = func.dfg.cast_phi_mut(phi_inst).unwrap();
            for pred in missing {
                phi.append_phi_arg(undef, pred);
            }
            changed = true;
        }

        func.dfg.attach_user(phi_inst);
    }

    changed
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use sonatina_ir::{
        Type,
        builder::test_util::{dump_func, test_func_builder, test_module_builder},
        inst::{
            arith::{Add, Sub},
            cmp::Slt,
            control_flow::{Br, Jump, Phi, Return},
        },
        isa::Isa,
    };

    use super::{CfgEditor, CleanupMode};

    #[test]
    fn replace_succ_allow_existing_pred_does_not_duplicate_phi_inputs() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1], Type::I32);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let cond = builder.args()[0];

        builder.switch_to_block(b0);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b1, b2));

        builder.switch_to_block(b1);
        builder.insert_inst_no_result_with(|| Jump::new(is, b2));

        builder.switch_to_block(b2);
        let one = builder.make_imm_value(1i32);
        let two = builder.make_imm_value(2i32);
        let phi = builder.insert_inst_with(|| Phi::new(is, vec![(one, b0), (two, b1)]), Type::I32);
        builder.insert_inst_no_result_with(|| Return::new(is, Some(phi)));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            let mut editor = CfgEditor::new(func, CleanupMode::Strict);
            assert!(editor.replace_succ_allow_existing_pred(b0, b1, b2, &[]));

            let phi_inst = editor.func().layout.first_inst_of(b2).unwrap();
            let phi = editor.func().dfg.cast_phi(phi_inst).unwrap();
            assert_eq!(phi.args().len(), 2);
            assert_eq!(phi.args().iter().filter(|(_, pred)| *pred == b0).count(), 1);
            assert_eq!(phi.args().iter().filter(|(_, pred)| *pred == b1).count(), 1);

            let term = editor.func().layout.last_inst_of(b0).unwrap();
            let jump = editor.func().dfg.cast_jump(term).unwrap();
            assert_eq!(*jump.dest(), b2);
        });
    }

    #[test]
    fn create_or_reuse_loop_preheader_factors_header_phis() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[Type::I1, Type::I32], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        let b1 = builder.append_block();
        let b2 = builder.append_block();
        let b3 = builder.append_block();
        let b4 = builder.append_block();
        let b5 = builder.append_block();

        let cond = builder.args()[0];
        let base = builder.args()[1];

        builder.switch_to_block(b0);
        let one = builder.make_imm_value(1i32);
        builder.insert_inst_with(|| Add::new(is, base, one), Type::I32);
        let one_again = builder.make_imm_value(1i32);
        let v3 = builder.insert_inst_with(|| Sub::new(is, base, one_again), Type::I32);
        builder.insert_inst_no_result_with(|| Br::new(is, cond, b1, b2));

        builder.switch_to_block(b1);
        builder.insert_inst_no_result_with(|| Jump::new(is, b3));

        builder.switch_to_block(b2);
        builder.insert_inst_no_result_with(|| Jump::new(is, b3));

        builder.switch_to_block(b3);
        let phi_seed_1 = builder.make_imm_value(1i32);
        let phi_seed_2 = builder.make_imm_value(2i32);
        let v4 = builder.insert_inst_with(
            || Phi::new(is, vec![(phi_seed_1, b1), (phi_seed_2, b2)]),
            Type::I32,
        );
        builder.insert_inst_no_result_with(|| Jump::new(is, b4));

        builder.switch_to_block(b4);
        let v6 = builder.insert_inst_with(|| Add::new(is, v4, v3), Type::I32);
        let ten = builder.make_imm_value(10i32);
        let v7 = builder.insert_inst_with(|| Slt::new(is, v6, ten), Type::I1);
        builder.insert_inst_no_result_with(|| Br::new(is, v7, b3, b5));
        builder.append_phi_arg(v4, v6, b4);

        builder.switch_to_block(b5);
        builder.insert_inst_no_result_with(|| Return::new(is, None));

        builder.seal_all();
        builder.finish();

        let module = mb.build();
        let func_ref = module.funcs()[0];
        module.func_store.modify(func_ref, |func| {
            let mut editor = CfgEditor::new(func, CleanupMode::Strict);
            let preheader = editor
                .create_or_reuse_loop_preheader(b3, &[b1, b2])
                .expect("preheader must be created");
            assert_ne!(preheader, b1);
            assert_ne!(preheader, b2);

            let b1_term = editor.func().layout.last_inst_of(b1).unwrap();
            let b1_jump = editor.func().dfg.cast_jump(b1_term).unwrap();
            assert_eq!(*b1_jump.dest(), preheader);
            let b2_term = editor.func().layout.last_inst_of(b2).unwrap();
            let b2_jump = editor.func().dfg.cast_jump(b2_term).unwrap();
            assert_eq!(*b2_jump.dest(), preheader);

            let pre_term = editor.func().layout.last_inst_of(preheader).unwrap();
            let pre_jump = editor.func().dfg.cast_jump(pre_term).unwrap();
            assert_eq!(*pre_jump.dest(), b3);

            let header_phi_inst = editor.func().layout.first_inst_of(b3).unwrap();
            let header_phi = editor.func().dfg.cast_phi(header_phi_inst).unwrap();
            assert_eq!(header_phi.args().len(), 2);
            assert!(header_phi.args().iter().any(|(_, pred)| *pred == b4));
            assert!(header_phi.args().iter().any(|(_, pred)| *pred == preheader));

            let preheader_phi_inst = editor.func().layout.first_inst_of(preheader).unwrap();
            let preheader_phi = editor.func().dfg.cast_phi(preheader_phi_inst).unwrap();
            assert_eq!(preheader_phi.args().len(), 2);
            assert!(preheader_phi.args().iter().any(|(_, pred)| *pred == b1));
            assert!(preheader_phi.args().iter().any(|(_, pred)| *pred == b2));

            let preds: BTreeSet<_> = editor.cfg().preds_of(b3).copied().collect();
            assert_eq!(preds, BTreeSet::from([b4, preheader]));
        });

        let output = dump_func(&module, func_ref);
        assert!(output.contains("phi"));
    }
}
