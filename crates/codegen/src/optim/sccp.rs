//! This module contains a solver for Sparse Conditional Constant Propagation.
//!
//! The algorithm is based on Mark N. Wegman., Frank Kcnncth Zadeck.: Constant
//! propagation with conditional branches: ACM Transactions on Programming
//! Languages and Systems Volume 13 Issue 2 April 1991 pp 181–210: <https://doi.org/10.1145/103135.103136>

use std::collections::BTreeSet;

use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashSet;
use sonatina_ir::{
    BlockId, ControlFlowGraph, DataFlowGraph, Function, Immediate, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        arith,
        control_flow::{BranchInfo, BranchKind},
        downcast,
    },
    interpret::{Action, EvalValue, Interpret, State},
    prelude::*,
};

use super::{
    adce::AdceSolver,
    cfg_cleanup::CfgCleanup,
    sccp_simplify::{SimplifyResult, simplify_inst},
};
use crate::cfg_edit::{CfgEditor, CleanupMode};

#[derive(Debug)]
pub struct SccpSolver {
    lattice: SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: SecondaryMap<ValueId, bool>,
    reachable_edges: FxHashSet<FlowEdge>,
    reachable_blocks: SecondaryMap<BlockId, bool>,

    flow_work: Vec<FlowEdge>,
    ssa_work: Vec<ValueId>,

    flow_work_set: FxHashSet<FlowEdge>,
    ssa_work_set: SecondaryMap<ValueId, bool>,
}

impl SccpSolver {
    pub fn new() -> Self {
        Self {
            lattice: SecondaryMap::default(),
            may_be_undef: SecondaryMap::default(),
            reachable_edges: FxHashSet::default(),
            reachable_blocks: SecondaryMap::default(),
            flow_work: Vec::default(),
            ssa_work: Vec::default(),
            flow_work_set: FxHashSet::default(),
            ssa_work_set: SecondaryMap::default(),
        }
    }
    pub fn run(&mut self, func: &mut Function, cfg: &mut ControlFlowGraph) {
        self.clear();

        let cleanup_mode = if cfg!(debug_assertions) {
            CleanupMode::Strict
        } else {
            CleanupMode::RepairWithUndef
        };
        CfgCleanup::new(cleanup_mode).run(func);

        let Some(entry_block) = func.layout.entry_block() else {
            return;
        };

        // Function arguments must be `LatticeCell::Top`
        for arg in &func.arg_values {
            self.lattice[*arg] = LatticeCell::Top;
        }

        // Evaluate all values in entry block.
        self.reachable_blocks[entry_block] = true;
        self.eval_insts_in(func, entry_block);

        while !(self.flow_work.is_empty() && self.ssa_work.is_empty()) {
            while let Some(edge) = self.flow_work.pop() {
                self.flow_work_set.remove(&edge);
                self.eval_edge(func, edge);
            }

            while let Some(value) = self.ssa_work.pop() {
                self.ssa_work_set[value] = false;
                for &user in func.dfg.users(value) {
                    let user_block = func.layout.inst_block(user);
                    if self.reachable_blocks[user_block] {
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

        self.remove_unreachable_edges(func, cleanup_mode);
        cfg.compute(func);
        self.fold_insts(func, cfg);

        CfgCleanup::new(cleanup_mode).run(func);
        cfg.compute(func);

        AdceSolver::new().run(func);
        cfg.compute(func);
    }

    pub fn clear(&mut self) {
        self.lattice.clear();
        self.may_be_undef.clear();
        self.reachable_edges.clear();
        self.reachable_blocks.clear();
        self.flow_work.clear();
        self.ssa_work.clear();
        self.flow_work_set.clear();
        self.ssa_work_set.clear();
    }

    fn push_flow_work(&mut self, edge: FlowEdge) {
        if self.reachable_edges.contains(&edge) || self.flow_work_set.contains(&edge) {
            return;
        }

        self.flow_work.push(edge);
        self.flow_work_set.insert(edge);
    }

    fn push_ssa_work(&mut self, value: ValueId) {
        if self.ssa_work_set[value] {
            return;
        }

        self.ssa_work.push(value);
        self.ssa_work_set[value] = true;
    }

    fn eval_edge(&mut self, func: &mut Function, edge: FlowEdge) {
        let dest = edge.to;

        if self.reachable_edges.contains(&edge) {
            return;
        }
        self.reachable_edges.insert(edge);

        if self.reachable_blocks[dest] {
            self.eval_phis_in(func, dest);
        } else {
            self.reachable_blocks[dest] = true;
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
        debug_assert!(self.reachable_blocks[func.layout.inst_block(inst)]);

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

        // SCCP here is intraprocedural. Do not attempt to interpret calls even
        // when callee attrs classify them as effect-free.
        if func.dfg.is_call(inst_id) {
            self.set_lattice_cell(inst_result, LatticeCell::Top);
            return;
        }

        let inst = func.dfg.inst(inst_id);
        if func.dfg.side_effect(inst_id).has_effect() {
            self.set_lattice_cell(inst_result, LatticeCell::Top);
            return;
        }
        if func.dfg.is_call(inst_id) {
            self.set_lattice_cell(inst_result, LatticeCell::Top);
            return;
        }

        match simplify_inst(func, &self.lattice, &self.may_be_undef, inst_id) {
            SimplifyResult::Const(imm) => {
                let imm = self.normalize_const_imm_for_value(func, inst_result, imm);
                self.set_lattice_cell(inst_result, LatticeCell::Const(imm));
                self.set_may_be_undef(inst_result, false);
                return;
            }
            SimplifyResult::Copy(src) => {
                let src_cell =
                    self.normalize_cell_for_value(func, inst_result, self.cell_of(func, src));
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
            Some(EvalValue::Imm(value)) => {
                let value = self.normalize_const_imm_for_value(func, inst_result, value);
                LatticeCell::Const(value)
            }
            Some(_) => cell_state.nonconst_result_cell(),
            None => LatticeCell::Top,
        };

        result_may_be_undef |= self.is_arith_div_or_rem_by_zero(func, inst_id);

        self.set_lattice_cell(inst_result, cell);
        self.set_may_be_undef(inst_result, result_may_be_undef);
    }

    fn is_arith_div_or_rem_by_zero(&self, func: &Function, inst_id: InstId) -> bool {
        let inst = func.dfg.inst(inst_id);
        let is = func.inst_set();

        let Some(rhs) = downcast::<&arith::Udiv>(is, inst)
            .map(|i| *i.rhs())
            .or_else(|| downcast::<&arith::Sdiv>(is, inst).map(|i| *i.rhs()))
            .or_else(|| downcast::<&arith::Umod>(is, inst).map(|i| *i.rhs()))
            .or_else(|| downcast::<&arith::Smod>(is, inst).map(|i| *i.rhs()))
        else {
            return false;
        };

        self.cell_of(func, rhs)
            .to_imm()
            .is_some_and(|imm| imm.is_zero())
    }

    fn eval_branch(&mut self, func: &Function, inst: InstId, bi: &dyn BranchInfo) {
        match bi.branch_kind() {
            BranchKind::Jump(jump) => {
                self.push_flow_work(FlowEdge::new(inst, *jump.dest()));
            }

            BranchKind::Br(br) => {
                let v_cell = self.cell_of(func, *br.cond());

                match v_cell {
                    LatticeCell::Const(_) if v_cell.is_zero() => {
                        self.push_flow_work(FlowEdge::new(inst, *br.z_dest()));
                    }
                    LatticeCell::Const(_) => {
                        self.push_flow_work(FlowEdge::new(inst, *br.nz_dest()));
                    }
                    LatticeCell::Top => {
                        self.push_flow_work(FlowEdge::new(inst, *br.z_dest()));
                        self.push_flow_work(FlowEdge::new(inst, *br.nz_dest()));
                    }
                    LatticeCell::Bot => {}
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
                                        self.push_flow_work(FlowEdge::new(inst, *dest));
                                        return;
                                    }
                                }
                                LatticeCell::Top | LatticeCell::Bot => {
                                    self.push_flow_work(FlowEdge::new(inst, *dest));
                                }
                            }
                        }

                        if let Some(default) = brt.default() {
                            self.push_flow_work(FlowEdge::new(inst, *default));
                        }
                    }
                    LatticeCell::Top => {
                        if let Some(default) = brt.default() {
                            self.push_flow_work(FlowEdge::new(inst, *default));
                        }
                        for (_, dest) in brt.table() {
                            self.push_flow_work(FlowEdge::new(inst, *dest));
                        }
                    }
                    LatticeCell::Bot => {}
                }
            }
        }
    }

    /// Remove unreachable edges and blocks.
    fn remove_unreachable_edges(&self, func: &mut Function, mode: CleanupMode) {
        let mut editor = CfgEditor::new(func, mode);

        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        for block in blocks {
            if !self.reachable_blocks[block] {
                editor.delete_block_unreachable(block);
            }
        }

        let blocks: Vec<_> = editor.func().layout.iter_block().collect();
        for block in blocks {
            if !self.reachable_blocks[block] {
                continue;
            }

            let Some(term) = editor.func().layout.last_inst_of(block) else {
                continue;
            };
            let Some(branch_info) = editor.func().dfg.branch_info(term) else {
                continue;
            };

            for dest in branch_info.dests() {
                if !self.is_reachable_edge(term, dest) {
                    editor.remove_succ(block, dest);
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
            self.push_ssa_work(value);
        }
    }

    fn set_may_be_undef(&mut self, value: ValueId, may_be_undef: bool) {
        let old = self.may_be_undef.get(value).copied().unwrap_or_default();
        if old != may_be_undef {
            self.may_be_undef[value] = may_be_undef;
            self.push_ssa_work(value);
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

    fn normalize_const_imm_for_value(
        &self,
        func: &Function,
        value: ValueId,
        imm: Immediate,
    ) -> Immediate {
        let ty = func.dfg.value_ty(value);
        if imm.ty() == ty {
            imm
        } else {
            Immediate::from_i256(imm.as_i256(), ty)
        }
    }

    fn normalize_cell_for_value(
        &self,
        func: &Function,
        value: ValueId,
        cell: LatticeCell,
    ) -> LatticeCell {
        if let LatticeCell::Const(imm) = cell {
            LatticeCell::Const(self.normalize_const_imm_for_value(func, value, imm))
        } else {
            cell
        }
    }

    #[cfg(debug_assertions)]
    fn assert_no_executable_inst_results_are_bot(&self, func: &Function) {
        for block in func.layout.iter_block() {
            if !self.reachable_blocks[block] {
                continue;
            }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[cfg(test)]
mod tests {
    use super::*;

    use sonatina_ir::{
        Linkage, Signature, Type,
        builder::test_util::test_module_builder,
        inst::{control_flow::Return, logic},
    };

    #[derive(Clone, Copy)]
    struct XorShift64(u64);

    impl XorShift64 {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn pick<T>(self, values: &[T]) -> usize {
            (self.0 as usize) % values.len()
        }
    }

    #[test]
    fn sccp_smoke_fuzz_no_panics() {
        for seed in 0..8u64 {
            let mb = test_module_builder();
            let sig = Signature::new("fuzz", Linkage::Public, &[], Type::I256);
            let func_ref = mb.declare_function(sig).unwrap();

            let mut fb = mb.func_builder::<InstInserter>(func_ref);
            let block0 = fb.append_block();
            fb.switch_to_block(block0);

            let ty = Type::I256;
            let is = fb.func.inst_set();

            let mut values = vec![
                fb.make_imm_value(Immediate::zero(ty)),
                fb.make_imm_value(Immediate::one(ty)),
            ];

            let mut rng = XorShift64(seed.wrapping_add(1));
            for _ in 0..64 {
                let lhs = values[rng.pick(&values)];
                rng.next();
                let rhs = values[rng.pick(&values)];
                let op = rng.next() % 9;

                let value = match op {
                    0 => fb.insert_inst(arith::Add::new_unchecked(is, lhs, rhs), ty),
                    1 => fb.insert_inst(arith::Sub::new_unchecked(is, lhs, rhs), ty),
                    2 => fb.insert_inst(arith::Mul::new_unchecked(is, lhs, rhs), ty),
                    3 => fb.insert_inst(arith::Shl::new_unchecked(is, lhs, rhs), ty),
                    4 => fb.insert_inst(arith::Shr::new_unchecked(is, lhs, rhs), ty),
                    5 => fb.insert_inst(arith::Sar::new_unchecked(is, lhs, rhs), ty),
                    6 => fb.insert_inst(logic::And::new_unchecked(is, lhs, rhs), ty),
                    7 => fb.insert_inst(logic::Or::new_unchecked(is, lhs, rhs), ty),
                    _ => fb.insert_inst(logic::Xor::new_unchecked(is, lhs, rhs), ty),
                };

                values.push(value);
            }

            let ret = *values.last().unwrap();
            fb.insert_inst_no_result(Return::new_unchecked(is, Some(ret)));
            fb.seal_all();
            fb.finish();

            let mut cfg = ControlFlowGraph::default();
            mb.func_store.modify(func_ref, |func| {
                cfg.compute(func);
                let mut solver = SccpSolver::new();
                solver.run(func, &mut cfg);
                CfgCleanup::new(CleanupMode::Strict).run(func);
            });
        }
    }
}
