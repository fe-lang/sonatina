use std::collections::BTreeSet;

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
        assert!(self.func.layout.is_block_inserted(from));
        assert!(self.func.layout.is_block_inserted(old_to));
        assert!(self.func.layout.is_block_inserted(new_to));

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
            branch_info.dests().into_iter().any(|dest| dest == old_to),
            "edge {from:?} -> {old_to:?} does not exist"
        );

        self.func.dfg.rewrite_branch_dest(term, old_to, new_to);

        remove_phi_incoming_from(self.func, old_to, from);
        simplify_trivial_phis_in_block(self.func, old_to);

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

        self.recompute_cfg();
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

fn remove_phi_incoming_from(func: &mut Function, block: BlockId, pred: BlockId) {
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
