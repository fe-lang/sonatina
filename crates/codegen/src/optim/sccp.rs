//! This module contains a solver for Sparse Conditional Constant Propagation.
//!
//! The algorithm is based on Mark N. Wegman., Frank Kcnncth Zadeck.: Constant
//! propagation with conditional branches: ACM Transactions on Programming
//! Languages and Systems Volume 13 Issue 2 April 1991 pp 181–210: <https://doi.org/10.1145/103135.103136>

use std::collections::BTreeSet;

use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    BlockId, ControlFlowGraph, DataFlowGraph, Function, Immediate, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::control_flow::{BranchInfo, BranchKind},
    interpret::{Action, EvalValue, Interpret, State},
    prelude::*,
};

use super::sccp_simplify::{SimplifyResult, simplify_inst};
use crate::cfg_edit::{remove_phi_incoming_from, simplify_trivial_phis_in_block};

#[derive(Debug)]
pub struct SccpSolver {
    lattice: SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: SecondaryMap<ValueId, bool>,
    reachable_edges: BTreeSet<FlowEdge>,
    reachable_blocks: BTreeSet<BlockId>,

    flow_work: Vec<FlowEdge>,
    ssa_work: Vec<ValueId>,
}

impl SccpSolver {
    pub fn new() -> Self {
        Self {
            lattice: SecondaryMap::default(),
            may_be_undef: SecondaryMap::default(),
            reachable_edges: BTreeSet::default(),
            reachable_blocks: BTreeSet::default(),
            flow_work: Vec::default(),
            ssa_work: Vec::default(),
        }
    }
    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) {
        self.clear();

        let entry_block = match func.layout.entry_block() {
            Some(block) => block,
            _ => return,
        };

        // Function arguments must be `LatticeCell::Top`
        for arg in &func.arg_values {
            self.lattice[*arg] = LatticeCell::Top;
        }

        // Evaluate all values in entry block.
        self.reachable_blocks.insert(entry_block);
        self.eval_insts_in(func, entry_block);

        while !(self.flow_work.is_empty() && self.ssa_work.is_empty()) {
            while let Some(edge) = self.flow_work.pop() {
                self.eval_edge(func, edge);
            }

            while let Some(value) = self.ssa_work.pop() {
                for &user in func.dfg.users(value) {
                    let user_block = func.layout.inst_block(user);
                    if self.reachable_blocks.contains(&user_block) {
                        if func.dfg.is_phi(user) {
                            self.eval_phi(func, user);
                        } else {
                            self.eval_inst(func, user);
                        }
                    }
                }
            }
        }

        #[cfg(debug_assertions)]
        self.assert_no_executable_inst_results_are_bot(func);

        self.remove_unreachable_edges(func);
        cfg.compute(func);
        self.fold_insts(func, cfg);
    }

    pub fn clear(&mut self) {
        self.lattice.clear();
        self.may_be_undef.clear();
        self.reachable_edges.clear();
        self.reachable_blocks.clear();
        self.flow_work.clear();
        self.ssa_work.clear();
    }

    fn eval_edge(&mut self, func: &mut Function, edge: FlowEdge) {
        let dest = edge.to;

        if self.reachable_edges.contains(&edge) {
            return;
        }
        self.reachable_edges.insert(edge);

        if self.reachable_blocks.contains(&dest) {
            self.eval_phis_in(func, dest);
        } else {
            self.reachable_blocks.insert(dest);
            self.eval_insts_in(func, dest);
        }
    }

    fn eval_phis_in(&mut self, func: &Function, block: BlockId) {
        for inst in func.layout.iter_inst(block) {
            if func.dfg.is_phi(inst) {
                self.eval_phi(func, inst);
            }
        }
    }

    fn eval_phi(&mut self, func: &Function, inst: InstId) {
        debug_assert!(
            self.reachable_blocks
                .contains(&func.layout.inst_block(inst))
        );

        let block = func.layout.inst_block(inst);
        let phi = func.dfg.cast_phi(inst).unwrap();

        let mut eval_result = LatticeCell::Bot;
        let mut eval_may_be_undef = false;
        for (val, from) in phi.args() {
            if self.is_reachable(func, *from, block) {
                let v_cell = self.cell_of(func, *val);
                eval_result = eval_result.join(v_cell);
                eval_may_be_undef |= self.may_be_undef_of(func, *val);
            }
        }

        let phi_value = func.dfg.inst_result(inst).unwrap();
        self.set_lattice_cell(phi_value, eval_result);
        self.set_may_be_undef(phi_value, eval_may_be_undef);
    }

    fn eval_insts_in(&mut self, func: &Function, block: BlockId) {
        for inst in func.layout.iter_inst(block) {
            if func.dfg.is_phi(inst) {
                self.eval_phi(func, inst);
            } else {
                self.eval_inst(func, inst);
            }
        }
    }

    fn eval_inst(&mut self, func: &Function, inst_id: InstId) {
        debug_assert!(!func.dfg.is_phi(inst_id));
        if let Some(bi) = func.dfg.branch_info(inst_id) {
            self.eval_branch(func, inst_id, bi);
            return;
        };

        let Some(inst_result) = func.dfg.inst_result(inst_id) else {
            return;
        };

        let inst = func.dfg.inst(inst_id);
        if func.dfg.side_effect(inst_id).has_effect() {
            self.set_lattice_cell(inst_result, LatticeCell::Top);
            return;
        }

        match simplify_inst(func, &self.lattice, &self.may_be_undef, inst_id) {
            SimplifyResult::Const(imm) => {
                self.set_lattice_cell(inst_result, LatticeCell::Const(imm));
                self.set_may_be_undef(inst_result, false);
                return;
            }
            SimplifyResult::Copy(src) => {
                let src_cell = self.cell_of(func, src);
                self.set_lattice_cell(inst_result, src_cell);
                self.set_may_be_undef(inst_result, self.may_be_undef_of(func, src));
                return;
            }
            SimplifyResult::NoChange => {}
        }

        let mut result_may_be_undef = false;
        inst.for_each_value(&mut |value| {
            result_may_be_undef |= self.may_be_undef_of(func, value);
        });

        let mut cell_state = CellState::new(&self.lattice, &func.dfg);
        let value = InstDowncast::map(func.inst_set(), inst, |i: &dyn Interpret| {
            i.interpret(&mut cell_state)
        });

        let cell = match value {
            Some(EvalValue::Imm(value)) => LatticeCell::Const(value),
            Some(_) => cell_state.nonconst_result_cell(),
            None => LatticeCell::Top,
        };

        self.set_lattice_cell(inst_result, cell);
        self.set_may_be_undef(inst_result, result_may_be_undef);
    }

    fn eval_branch(&mut self, func: &Function, inst: InstId, bi: &dyn BranchInfo) {
        match bi.branch_kind() {
            BranchKind::Jump(jump) => {
                self.flow_work.push(FlowEdge::new(inst, *jump.dest()));
            }

            BranchKind::Br(br) => {
                let v_cell = self.cell_of(func, *br.cond());

                match v_cell {
                    LatticeCell::Const(_) if v_cell.is_zero() => {
                        self.flow_work.push(FlowEdge::new(inst, *br.z_dest()));
                    }
                    LatticeCell::Const(_) => {
                        self.flow_work.push(FlowEdge::new(inst, *br.nz_dest()));
                    }
                    LatticeCell::Top | LatticeCell::Bot => {
                        self.flow_work.push(FlowEdge::new(inst, *br.z_dest()));
                        self.flow_work.push(FlowEdge::new(inst, *br.nz_dest()));
                    }
                }
            }

            BranchKind::BrTable(brt) => {
                let scrutinee_cell = self.cell_of(func, *brt.scrutinee());

                match scrutinee_cell {
                    LatticeCell::Const(scrutinee) => {
                        for (case_value, dest) in brt.table() {
                            match self.cell_of(func, *case_value) {
                                LatticeCell::Const(case) => {
                                    if case == scrutinee {
                                        self.flow_work.push(FlowEdge::new(inst, *dest));
                                        return;
                                    }
                                }
                                LatticeCell::Top | LatticeCell::Bot => {
                                    self.flow_work.push(FlowEdge::new(inst, *dest));
                                }
                            }
                        }

                        if let Some(default) = brt.default() {
                            self.flow_work.push(FlowEdge::new(inst, *default));
                        }
                    }
                    LatticeCell::Top | LatticeCell::Bot => {
                        if let Some(default) = brt.default() {
                            self.flow_work.push(FlowEdge::new(inst, *default));
                        }
                        for (_, dest) in brt.table() {
                            self.flow_work.push(FlowEdge::new(inst, *dest));
                        }
                    }
                }
            }
        }
    }

    /// Remove unreachable edges and blocks.
    fn remove_unreachable_edges(&self, func: &mut Function) {
        let entry_block = func.layout.entry_block().unwrap();
        let mut inserter = InstInserter::at_location(CursorLocation::BlockTop(entry_block));

        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(block) => {
                    if !self.reachable_blocks.contains(&block) {
                        self.prune_phi_incoming_from_removed_block(func, block);
                        inserter.remove_block(func);
                    } else {
                        inserter.proceed(func);
                    }
                }

                CursorLocation::BlockBottom(..) => inserter.proceed(func),

                CursorLocation::At(inst) => {
                    if let Some(bi) = func.dfg.branch_info(inst) {
                        let from = func.layout.inst_block(inst);
                        for dest in bi.dests() {
                            if !self.is_reachable_edge(inst, dest) {
                                func.dfg.remove_branch_dest(inst, dest);
                                if func.layout.is_block_inserted(dest) {
                                    remove_phi_incoming_from(func, dest, from);
                                    simplify_trivial_phis_in_block(func, dest);
                                }
                            }
                        }
                    }
                    inserter.proceed(func);
                }

                CursorLocation::NoWhere => break,
            }
        }
    }

    fn prune_phi_incoming_from_removed_block(&self, func: &mut Function, block: BlockId) {
        assert!(func.layout.is_block_inserted(block));
        let term = func.layout.last_inst_of(block).expect("empty block");
        assert!(func.dfg.is_terminator(term));
        if let Some(bi) = func.dfg.branch_info(term) {
            for succ in bi.dests() {
                let inserted = func.layout.is_block_inserted(succ);
                assert!(inserted || !self.reachable_blocks.contains(&succ));
                if inserted {
                    remove_phi_incoming_from(func, succ, block);
                    simplify_trivial_phis_in_block(func, succ);
                }
            }
        }
    }

    fn is_reachable_edge(&self, inst: InstId, dest: BlockId) -> bool {
        self.reachable_edges.contains(&FlowEdge::new(inst, dest))
    }

    fn fold_insts(&mut self, func: &mut Function, cfg: &ControlFlowGraph) {
        let mut rpo: Vec<_> = cfg.post_order().collect();
        rpo.reverse();

        for block in rpo {
            let mut next_inst = func.layout.first_inst_of(block);
            while let Some(inst) = next_inst {
                next_inst = func.layout.next_inst_of(inst);
                self.fold(func, inst);
            }
        }
    }

    fn fold(&self, func: &mut Function, inst: InstId) {
        let inst_result = match func.dfg.inst_result(inst) {
            Some(result) => result,
            None => return,
        };

        if !func.dfg.is_phi(inst)
            && let SimplifyResult::Copy(src) =
                simplify_inst(func, &self.lattice, &self.may_be_undef, inst)
        {
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            func.dfg.change_to_alias(inst_result, src);
            return;
        }

        match self.lattice[inst_result].to_imm() {
            Some(imm) => {
                let result_ty = func.dfg.value_ty(inst_result);
                debug_assert_eq!(
                    imm.ty(),
                    result_ty,
                    "SCCP tried to fold an immediate of a different type: {inst:?}"
                );
                if imm.ty() != result_ty {
                    return;
                }

                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                let new_value = func.dfg.make_imm_value(imm);
                func.dfg.change_to_alias(inst_result, new_value);
            }
            None => {
                if func.dfg.is_phi(inst) {
                    self.try_fold_phi(func, inst)
                }
            }
        }
    }

    fn try_fold_phi(&self, func: &mut Function, inst: InstId) {
        let block = func.layout.inst_block(inst);
        let phi_value = func.dfg.inst_result(inst).expect("phi has no result");
        let phi_ty = func.dfg.value_ty(phi_value);

        let reachable_preds: BTreeSet<_> = func
            .dfg
            .cast_phi(inst)
            .unwrap()
            .args()
            .iter()
            .map(|&(_, pred)| pred)
            .filter(|pred| self.is_reachable(func, *pred, block))
            .collect();

        func.dfg.untrack_inst(inst);

        let mut fold_arg = None;
        {
            let phi = func.dfg.cast_phi_mut(inst).unwrap();
            phi.retain(|pred| reachable_preds.contains(&pred));

            let mut seen = BTreeSet::new();
            for &(_, pred) in phi.args() {
                assert!(
                    seen.insert(pred),
                    "phi {inst:?} has duplicate incoming from {pred:?}"
                );
            }

            if phi.args().len() == 1 {
                fold_arg = Some(phi.args()[0].0);
            }
        }

        let fold_arg = if fold_arg.is_none() && func.dfg.cast_phi(inst).unwrap().args().is_empty() {
            Some(func.dfg.make_undef_value(phi_ty))
        } else {
            fold_arg
        };

        // Remove phi function if it has 0 or 1 arguments.
        if let Some(phi_arg) = fold_arg {
            let phi_arg = if phi_arg == phi_value {
                func.dfg.make_undef_value(phi_ty)
            } else {
                phi_arg
            };
            func.dfg.change_to_alias(phi_value, phi_arg);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        } else {
            func.dfg.attach_user(inst);
        }
    }

    fn is_reachable(&self, func: &Function, from: BlockId, to: BlockId) -> bool {
        if !func.layout.is_block_inserted(from) || !func.layout.is_block_inserted(to) {
            return false;
        }

        let Some(last_inst) = func.layout.last_inst_of(from) else {
            return false;
        };

        let Some(bi) = func.dfg.branch_info(last_inst) else {
            return false;
        };

        for dest in bi.dests() {
            if dest == to
                && self
                    .reachable_edges
                    .contains(&FlowEdge::new(last_inst, dest))
            {
                return true;
            }
        }
        false
    }

    fn set_lattice_cell(&mut self, value: ValueId, cell: LatticeCell) {
        let old_cell = &self.lattice[value];
        if old_cell != &cell {
            self.lattice[value] = cell;
            self.ssa_work.push(value);
        }
    }

    fn set_may_be_undef(&mut self, value: ValueId, may_be_undef: bool) {
        let old = self.may_be_undef.get(value).copied().unwrap_or_default();
        if old != may_be_undef {
            self.may_be_undef[value] = may_be_undef;
            self.ssa_work.push(value);
        }
    }

    fn cell_of(&self, func: &Function, value: ValueId) -> LatticeCell {
        match func.dfg.value(value) {
            Value::Immediate { imm, .. } => LatticeCell::Const(*imm),
            Value::Global { .. } | Value::Undef { .. } => LatticeCell::Top,
            Value::Arg { .. } | Value::Inst { .. } => {
                self.lattice.get(value).copied().unwrap_or_default()
            }
        }
    }

    fn may_be_undef_of(&self, func: &Function, value: ValueId) -> bool {
        match func.dfg.value(value) {
            Value::Undef { .. } => true,
            Value::Arg { .. } | Value::Immediate { .. } | Value::Global { .. } => false,
            Value::Inst { .. } => self.may_be_undef.get(value).copied().unwrap_or_default(),
        }
    }

    #[cfg(debug_assertions)]
    fn assert_no_executable_inst_results_are_bot(&self, func: &Function) {
        for &block in self.reachable_blocks.iter() {
            for inst in func.layout.iter_inst(block) {
                if func.dfg.is_phi(inst) || func.dfg.branch_info(inst).is_some() {
                    continue;
                }

                let inst_data = func.dfg.inst(inst);
                if inst_data.side_effect().has_effect() {
                    continue;
                }

                let Some(result) = func.dfg.inst_result(inst) else {
                    continue;
                };

                let mut operands_all_non_bot = true;
                inst_data.for_each_value(&mut |value| {
                    if self.cell_of(func, value).is_bot() {
                        operands_all_non_bot = false;
                    }
                });

                let result_cell = self.lattice.get(result).copied().unwrap_or_default();
                if operands_all_non_bot && result_cell.is_bot() {
                    panic!("SCCP produced Bot for executable inst result: {inst:?}");
                }
            }
        }
    }
}

impl Default for SccpSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct FlowEdge {
    inst: InstId,
    to: BlockId,
}

impl FlowEdge {
    fn new(inst: InstId, to: BlockId) -> Self {
        Self { inst, to }
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) enum LatticeCell {
    Top,
    Const(Immediate),
    #[default]
    Bot,
}

impl PartialEq for LatticeCell {
    fn eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (Self::Top, Self::Top) | (Self::Bot, Self::Bot) => true,
            (Self::Const(v1), Self::Const(v2)) => v1 == v2,
            _ => false,
        }
    }
}

impl LatticeCell {
    fn to_imm(self) -> Option<Immediate> {
        match self {
            Self::Top | Self::Bot => None,
            Self::Const(imm) => Some(imm),
        }
    }

    fn is_zero(self) -> bool {
        match self {
            Self::Top | Self::Bot => false,
            Self::Const(c) => c.is_zero(),
        }
    }

    fn is_bot(self) -> bool {
        matches!(self, Self::Bot)
    }

    fn join(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Const(v1), Self::Const(v2)) => {
                if v1 == v2 {
                    self
                } else {
                    Self::Top
                }
            }
            (Self::Bot, other) | (other, Self::Bot) => other,
        }
    }
}

struct CellState<'a, 'i> {
    map: &'i SecondaryMap<ValueId, LatticeCell>,
    used_has_top: bool,
    used_has_bot: bool,
    dfg: &'a DataFlowGraph,
}
impl<'a, 'i> CellState<'a, 'i> {
    fn new(map: &'i SecondaryMap<ValueId, LatticeCell>, dfg: &'a DataFlowGraph) -> Self {
        Self {
            map,
            used_has_top: false,
            used_has_bot: false,
            dfg,
        }
    }

    fn nonconst_result_cell(&self) -> LatticeCell {
        match (self.used_has_top, self.used_has_bot) {
            (true, _) => LatticeCell::Top,
            (false, true) => LatticeCell::Bot,
            (false, false) => LatticeCell::Top,
        }
    }
}

impl State for CellState<'_, '_> {
    fn lookup_val(&mut self, value: ValueId) -> EvalValue {
        let cell = match self.dfg.value(value) {
            Value::Immediate { imm, .. } => LatticeCell::Const(*imm),
            Value::Global { .. } | Value::Undef { .. } => LatticeCell::Top,
            Value::Arg { .. } | Value::Inst { .. } => {
                self.map.get(value).copied().unwrap_or_default()
            }
        };

        match cell {
            LatticeCell::Const(imm) => EvalValue::Imm(imm),
            LatticeCell::Top => {
                self.used_has_top = true;
                EvalValue::Undef
            }
            LatticeCell::Bot => {
                self.used_has_bot = true;
                EvalValue::Undef
            }
        }
    }

    fn call_func(
        &mut self,
        _func: sonatina_ir::module::FuncRef,
        _args: Vec<EvalValue>,
    ) -> EvalValue {
        panic!("call instuctuion must not be Interpreted")
    }

    fn set_action(&mut self, action: Action) {
        if action != Action::Continue {
            panic!("instruction with side effect must not be interpreted")
        }
    }

    fn prev_block(&mut self) -> BlockId {
        panic!("flow sensitive operation must not be interpreted")
    }

    fn load(&mut self, _addr: EvalValue, _ty: Type) -> EvalValue {
        panic!("instruction with side effect must not be interpreted")
    }

    fn store(&mut self, _addr: EvalValue, _value: EvalValue, _ty: Type) -> EvalValue {
        panic!("instruction with side effect must not be interpreted")
    }

    fn alloca(&mut self, _ty: Type) -> EvalValue {
        panic!("instruction with side effect must not be interpreted")
    }

    fn dfg(&self) -> &DataFlowGraph {
        self.dfg
    }
}
