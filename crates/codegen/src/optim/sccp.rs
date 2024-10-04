//! This module contains a solver for Sparse Conditional Constant Propagation.
//!
//! The algorithm is based on Mark N. Wegman., Frank Kcnncth Zadeck.: Constant
//! propagation with conditional branches: ACM Transactions on Programming
//! Languages and Systems Volume 13 Issue 2 April 1991 pp 181–210: <https://doi.org/10.1145/103135.103136>

use std::collections::BTreeSet;

use cranelift_entity::SecondaryMap;
use rustc_hash::FxHashSet;
use sonatina_ir::{
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::control_flow::{Branch, BranchInfo},
    interpret::{EvalValue, Interpret, Interpretable, State},
    prelude::*,
    BlockId, ControlFlowGraph, Function, Immediate, InstId, ValueId,
};

#[derive(Debug)]
pub struct SccpSolver {
    lattice: SecondaryMap<ValueId, LatticeCell>,
    reachable_edges: BTreeSet<FlowEdge>,
    reachable_blocks: BTreeSet<BlockId>,

    flow_work: Vec<FlowEdge>,
    ssa_work: Vec<ValueId>,
}

impl SccpSolver {
    pub fn new() -> Self {
        Self {
            lattice: SecondaryMap::default(),
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

        let mut changed = true;
        while changed {
            changed = false;

            while let Some(edge) = self.flow_work.pop() {
                changed = true;
                self.eval_edge(func, edge);
            }

            while let Some(value) = self.ssa_work.pop() {
                changed = true;
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

        self.remove_unreachable_edges(func);
        cfg.compute(func);
        self.fold_insts(func, cfg);
    }

    pub fn clear(&mut self) {
        self.lattice.clear();
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

        if let Some(last_inst) = func.layout.last_inst_of(dest) {
            let Some(bi) = func.dfg.branch_info(last_inst) else {
                return;
            };
            if bi.num_dests() == 1 {
                self.flow_work.push(FlowEdge::new(last_inst, bi.dests()[0]))
            }
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
        debug_assert!(self
            .reachable_blocks
            .contains(&func.layout.inst_block(inst)));

        func.dfg.inst(inst).visit_values(&mut |value| {
            if let Some(imm) = func.dfg.value_imm(value) {
                self.set_lattice_cell(value, LatticeCell::Const(imm));
            }
        });

        let block = func.layout.inst_block(inst);
        let phi = func.dfg.cast_phi(inst).unwrap();

        let mut eval_result = LatticeCell::Bot;
        for (val, from) in phi.args() {
            if self.is_reachable(func, *from, block) {
                let v_cell = self.lattice[*val];
                eval_result = eval_result.join(v_cell);
            }
        }

        let phi_value = func.dfg.inst_result(inst).unwrap();
        if eval_result != self.lattice[phi_value] {
            self.ssa_work.push(phi_value);
            self.lattice[phi_value] = eval_result;
        }
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
        func.dfg.inst(inst_id).visit_values(&mut |value| {
            if let Some(imm) = func.dfg.value_imm(value) {
                self.set_lattice_cell(value, LatticeCell::Const(imm));
            }
        });

        if let Some(bi) = func.dfg.branch_info(inst_id) {
            self.eval_branch(inst_id, bi);
            return;
        };

        let inst = func.dfg.inst(inst_id);
        if inst.has_side_effect() {
            return;
        }

        let mut cell_state = CellState::new(&self.lattice);
        let value = Interpretable::map(func.inst_set(), inst, |i| i.interpret(&mut cell_state));

        let inst_result = func.dfg.inst_result(inst_id).unwrap();
        let cell = if let Some(EvalValue::Imm(value)) = value {
            LatticeCell::Const(value)
        } else {
            cell_state.cell()
        };

        self.set_lattice_cell(inst_result, cell);
    }

    fn eval_branch(&mut self, inst: InstId, bi: BranchInfo) {
        match bi {
            BranchInfo::Jump(jump) => {
                self.flow_work.push(FlowEdge::new(inst, *jump.dest()));
            }

            BranchInfo::Br(br) => {
                let v_cell = self.lattice[*br.cond()];

                if v_cell.is_top() {
                    self.flow_work.push(FlowEdge::new(inst, *br.z_dest()));
                    self.flow_work.push(FlowEdge::new(inst, *br.nz_dest()));
                } else if v_cell.is_bot() {
                    unreachable!();
                } else if v_cell.is_zero() {
                    self.flow_work.push(FlowEdge::new(inst, *br.z_dest()));
                } else {
                    self.flow_work.push(FlowEdge::new(inst, *br.nz_dest()));
                }
            }

            BranchInfo::BrTable(brt) => {
                // An closure that add all destinations of the `BrTable.
                let mut add_all_dest = || {
                    if let Some(default) = brt.default() {
                        self.flow_work.push(FlowEdge::new(inst, *default));
                    }
                    for (_, dest) in brt.table() {
                        self.flow_work.push(FlowEdge::new(inst, *dest));
                    }
                };

                let v_cell = self.lattice[*brt.scrutinee()];

                // If the argument of the `BrTable` is top, then add all destinations.
                if v_cell.is_top() {
                    add_all_dest();
                    return;
                }

                // Verifier verifies that the use of the argument must dominated by the its
                // definition, so `v_cell` must not be bot.
                if v_cell.is_bot() {
                    unreachable!()
                }

                let mut contains_top = false;
                for (value, dest) in brt.table() {
                    if self.lattice[*value] == v_cell {
                        self.flow_work.push(FlowEdge::new(inst, *dest));
                        return;
                    } else if v_cell.is_top() {
                        contains_top = true;
                    }
                }

                if contains_top {
                    // If one of the table value is top, then add all dests.
                    add_all_dest();
                } else {
                    // If all table values is not top, then just add default destination.
                    if let Some(default) = brt.default() {
                        self.flow_work.push(FlowEdge::new(inst, *default));
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
                        inserter.remove_block(func);
                    } else {
                        inserter.proceed(func);
                    }
                }

                CursorLocation::BlockBottom(..) => inserter.proceed(func),

                CursorLocation::At(inst) => {
                    if let Some(bi) = func.dfg.branch_info(inst) {
                        for dest in bi.dests() {
                            if !self.is_reachable_edge(inst, dest) {
                                func.dfg.remove_branch_dest(inst, dest);
                            }
                        }
                    }
                    inserter.proceed(func);
                }

                CursorLocation::NoWhere => break,
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

        match self.lattice[inst_result].to_imm() {
            Some(imm) => {
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
        let phi = func.dfg.cast_phi_mut(inst).unwrap();
        phi.retain(|block| self.reachable_blocks.contains(&block));

        // Remove phi function if it has just one argument.
        if phi.args().len() == 1 {
            let phi_arg = phi.args()[0].0;
            let phi_value = func.dfg.inst_result(inst).unwrap();
            func.dfg.change_to_alias(phi_value, phi_arg);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        }
    }

    fn is_reachable(&self, func: &Function, from: BlockId, to: BlockId) -> bool {
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

#[derive(Debug, Clone, Copy)]
enum LatticeCell {
    Top,
    Const(Immediate),
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

    fn is_top(self) -> bool {
        matches!(self, Self::Top)
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

impl Default for LatticeCell {
    fn default() -> Self {
        Self::Bot
    }
}

struct CellState<'i> {
    map: &'i SecondaryMap<ValueId, LatticeCell>,
    used_val: FxHashSet<ValueId>,
}
impl<'i> CellState<'i> {
    fn new(map: &'i SecondaryMap<ValueId, LatticeCell>) -> Self {
        Self {
            map,
            used_val: Default::default(),
        }
    }

    fn cell(&self) -> LatticeCell {
        for &used in self.used_val.iter() {
            if self.map[used] == LatticeCell::Top {
                return LatticeCell::Top;
            }
        }

        LatticeCell::Bot
    }
}

impl<'i> State for CellState<'i> {
    fn lookup_val(&mut self, value: ValueId) -> EvalValue {
        self.used_val.insert(value);

        match self.map.get(value) {
            Some(LatticeCell::Const(imm)) => EvalValue::Imm(*imm),
            _ => EvalValue::Undef,
        }
    }

    fn eval_func(
        &mut self,
        _func: sonatina_ir::module::FuncRef,
        _args: Vec<EvalValue>,
    ) -> EvalValue {
        panic!("call instuctuion must not be Interpreted")
    }

    fn set_action(&mut self, _action: sonatina_ir::interpret::Action) {
        panic!("instruction with side effect must not be interpreted")
    }

    fn prev_block(&mut self) -> BlockId {
        panic!("flow sensitive operation must not be interpreted")
    }
}
