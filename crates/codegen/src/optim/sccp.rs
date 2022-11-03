//! This module contains a solver for Sparse Conditional Constant Propagation.
//!
//! The algorithm is based on Mark N. Wegman., Frank Kcnncth Zadeck.: Constant propagation with conditional branches:  
//! ACM Transactions on Programming Languages and Systems Volume 13 Issue 2 April 1991 pp 181–210:  
//! <https://doi.org/10.1145/103135.103136>

use std::{collections::BTreeSet, ops};

use cranelift_entity::SecondaryMap;

use crate::cfg::ControlFlowGraph;

use sonatina_ir::{
    func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    insn::{BinaryOp, CastOp, InsnData, UnaryOp},
    Block, Function, Immediate, Insn, Type, Value,
};

#[derive(Debug)]
pub struct SccpSolver {
    lattice: SecondaryMap<Value, LatticeCell>,
    reachable_edges: BTreeSet<FlowEdge>,
    reachable_blocks: BTreeSet<Block>,

    flow_work: Vec<FlowEdge>,
    ssa_work: Vec<Value>,
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
        self.eval_insns_in(func, entry_block);

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
                    let user_block = func.layout.insn_block(user);
                    if self.reachable_blocks.contains(&user_block) {
                        if func.dfg.is_phi(user) {
                            self.eval_phi(func, user);
                        } else {
                            self.eval_insn(func, user);
                        }
                    }
                }
            }
        }

        self.remove_unreachable_edges(func);
        cfg.compute(func);
        self.fold_insns(func, cfg);
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
            self.eval_insns_in(func, dest);
        }

        if let Some(last_insn) = func.layout.last_insn_of(dest) {
            let branch_info = func.dfg.analyze_branch(last_insn);
            if branch_info.dests_num() == 1 {
                self.flow_work.push(FlowEdge::new(
                    last_insn,
                    branch_info.iter_dests().next().unwrap(),
                ))
            }
        }
    }

    fn eval_phis_in(&mut self, func: &Function, block: Block) {
        for insn in func.layout.iter_insn(block) {
            if func.dfg.is_phi(insn) {
                self.eval_phi(func, insn);
            }
        }
    }

    fn eval_phi(&mut self, func: &Function, insn: Insn) {
        debug_assert!(func.dfg.is_phi(insn));
        debug_assert!(self
            .reachable_blocks
            .contains(&func.layout.insn_block(insn)));

        for &arg in func.dfg.insn_args(insn) {
            if let Some(imm) = func.dfg.value_imm(arg) {
                self.set_lattice_cell(arg, LatticeCell::Const(imm));
            }
        }

        let block = func.layout.insn_block(insn);

        let mut eval_result = LatticeCell::Bot;
        for (i, from) in func.dfg.phi_blocks(insn).iter().enumerate() {
            if self.is_reachable(func, *from, block) {
                let phi_arg = func.dfg.insn_arg(insn, i);
                let v_cell = self.lattice[phi_arg];
                eval_result = eval_result.join(v_cell);
            }
        }

        let phi_value = func.dfg.insn_result(insn).unwrap();
        if eval_result != self.lattice[phi_value] {
            self.ssa_work.push(phi_value);
            self.lattice[phi_value] = eval_result;
        }
    }

    fn eval_insns_in(&mut self, func: &Function, block: Block) {
        for insn in func.layout.iter_insn(block) {
            if func.dfg.is_phi(insn) {
                self.eval_phi(func, insn);
            } else {
                self.eval_insn(func, insn);
            }
        }
    }

    fn eval_insn(&mut self, func: &Function, insn: Insn) {
        debug_assert!(!func.dfg.is_phi(insn));
        for &arg in func.dfg.insn_args(insn) {
            if let Some(imm) = func.dfg.value_imm(arg) {
                self.set_lattice_cell(arg, LatticeCell::Const(imm));
            }
        }

        let cell = match func.dfg.insn_data(insn) {
            InsnData::Unary { code, args } => {
                let arg_cell = self.lattice[args[0]];
                match *code {
                    UnaryOp::Not => arg_cell.not(),
                    UnaryOp::Neg => arg_cell.neg(),
                }
            }

            InsnData::Binary { code, args } => {
                let lhs = self.lattice[args[0]];
                let rhs = self.lattice[args[1]];
                match *code {
                    BinaryOp::Add => lhs.add(rhs),
                    BinaryOp::Sub => lhs.sub(rhs),
                    BinaryOp::Mul => lhs.mul(rhs),
                    BinaryOp::Udiv => lhs.udiv(rhs),
                    BinaryOp::Sdiv => lhs.sdiv(rhs),
                    BinaryOp::Lt => lhs.lt(rhs),
                    BinaryOp::Gt => lhs.gt(rhs),
                    BinaryOp::Slt => lhs.slt(rhs),
                    BinaryOp::Sgt => lhs.sgt(rhs),
                    BinaryOp::Le => lhs.le(rhs),
                    BinaryOp::Ge => lhs.ge(rhs),
                    BinaryOp::Sle => lhs.sle(rhs),
                    BinaryOp::Sge => lhs.sge(rhs),
                    BinaryOp::Eq => lhs.eq(rhs),
                    BinaryOp::Ne => lhs.ne(rhs),
                    BinaryOp::And => lhs.and(rhs),
                    BinaryOp::Or => lhs.or(rhs),
                    BinaryOp::Xor => lhs.xor(rhs),
                }
            }

            InsnData::Cast { code, args, ty } => {
                let arg_cell = self.lattice[args[0]];
                match code {
                    CastOp::Sext => arg_cell.sext(*ty),
                    CastOp::Zext => arg_cell.zext(*ty),
                    CastOp::Trunc => arg_cell.trunc(*ty),
                }
            }

            InsnData::Load { .. } => LatticeCell::Top,

            InsnData::Call { .. } => LatticeCell::Top,

            InsnData::Jump { dests, .. } => {
                self.flow_work.push(FlowEdge::new(insn, dests[0]));
                return;
            }

            InsnData::Branch { args, dests } => {
                let v_cell = self.lattice[args[0]];

                if v_cell.is_top() {
                    // Add both then and else edges.
                    self.flow_work.push(FlowEdge::new(insn, dests[0]));
                    self.flow_work.push(FlowEdge::new(insn, dests[1]));
                } else if v_cell.is_bot() {
                    unreachable!();
                } else if v_cell.is_zero() {
                    // Add else edge.
                    self.flow_work.push(FlowEdge::new(insn, dests[1]));
                } else {
                    // Add then edge.
                    self.flow_work.push(FlowEdge::new(insn, dests[0]));
                }

                return;
            }

            InsnData::BrTable {
                args,
                default,
                table,
            } => {
                // An closure that add all destinations of the `BrTable.
                let mut add_all_dest = || {
                    if let Some(default) = default {
                        self.flow_work.push(FlowEdge::new(insn, *default));
                    }
                    for dest in table {
                        self.flow_work.push(FlowEdge::new(insn, *dest));
                    }
                };

                let v_cell = self.lattice[args[0]];

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
                for (value, dest) in args[1..].iter().zip(table.iter()) {
                    if self.lattice[*value] == v_cell {
                        self.flow_work.push(FlowEdge::new(insn, *dest));
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
                    if let Some(default) = default {
                        self.flow_work.push(FlowEdge::new(insn, *default));
                    }
                }

                return;
            }

            InsnData::Alloca { .. } => LatticeCell::Top,

            InsnData::Store { .. } | InsnData::Return { .. } => {
                // No insn result. Do nothing.
                return;
            }

            InsnData::Phi { .. } => unreachable!(),
        };

        let insn_result = func.dfg.insn_result(insn).unwrap();
        self.set_lattice_cell(insn_result, cell);
    }

    /// Remove unreachable edges and blocks.
    fn remove_unreachable_edges(&self, func: &mut Function) {
        let entry_block = func.layout.entry_block().unwrap();
        let mut inserter = InsnInserter::new(func, CursorLocation::BlockTop(entry_block));

        loop {
            match inserter.loc() {
                CursorLocation::BlockTop(block) => {
                    if !self.reachable_blocks.contains(&block) {
                        inserter.remove_block();
                    } else {
                        inserter.proceed();
                    }
                }

                CursorLocation::BlockBottom(..) => inserter.proceed(),

                CursorLocation::At(insn) => {
                    if inserter.func().dfg.is_branch(insn) {
                        let branch_info = inserter.func().dfg.analyze_branch(insn);
                        for dest in branch_info.iter_dests().collect::<Vec<_>>() {
                            if !self.is_reachable_edge(insn, dest) {
                                inserter.func_mut().dfg.remove_branch_dest(insn, dest);
                            }
                        }
                    }
                    inserter.proceed();
                }

                CursorLocation::NoWhere => break,
            }
        }
    }

    fn is_reachable_edge(&self, insn: Insn, dest: Block) -> bool {
        self.reachable_edges.contains(&FlowEdge::new(insn, dest))
    }

    fn fold_insns(&mut self, func: &mut Function, cfg: &ControlFlowGraph) {
        let mut rpo: Vec<_> = cfg.post_order().collect();
        rpo.reverse();

        for block in rpo {
            let mut next_insn = func.layout.first_insn_of(block);
            while let Some(insn) = next_insn {
                next_insn = func.layout.next_insn_of(insn);
                self.fold(func, insn);
            }
        }
    }

    fn fold(&self, func: &mut Function, insn: Insn) {
        let insn_result = match func.dfg.insn_result(insn) {
            Some(result) => result,
            None => return,
        };

        match self.lattice[insn_result].to_imm() {
            Some(imm) => {
                InsnInserter::new(func, CursorLocation::At(insn)).remove_insn();
                let new_value = func.dfg.make_imm_value(imm);
                func.dfg.change_to_alias(insn_result, new_value);
            }
            None => {
                if func.dfg.is_phi(insn) {
                    self.try_fold_phi(func, insn)
                }
            }
        }
    }

    fn try_fold_phi(&self, func: &mut Function, insn: Insn) {
        debug_assert!(func.dfg.is_phi(insn));

        let mut blocks = func.dfg.phi_blocks(insn).to_vec();
        blocks.retain(|block| !self.reachable_blocks.contains(block));
        for block in blocks {
            func.dfg.remove_phi_arg(insn, block);
        }

        // Remove phi function if it has just one argument.
        if func.dfg.insn_args_num(insn) == 1 {
            let phi_value = func.dfg.insn_result(insn).unwrap();
            func.dfg
                .change_to_alias(phi_value, func.dfg.insn_arg(insn, 0));
            InsnInserter::new(func, CursorLocation::At(insn)).remove_insn();
        }
    }

    fn is_reachable(&self, func: &Function, from: Block, to: Block) -> bool {
        let last_insn = if let Some(insn) = func.layout.last_insn_of(from) {
            insn
        } else {
            return false;
        };
        for dest in func.dfg.analyze_branch(last_insn).iter_dests() {
            if dest == to
                && self
                    .reachable_edges
                    .contains(&FlowEdge::new(last_insn, dest))
            {
                return true;
            }
        }
        false
    }

    fn set_lattice_cell(&mut self, value: Value, cell: LatticeCell) {
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
    insn: Insn,
    to: Block,
}

impl FlowEdge {
    fn new(insn: Insn, to: Block) -> Self {
        Self { insn, to }
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

    fn apply_unop<F>(self, f: F) -> Self
    where
        F: FnOnce(Immediate) -> Immediate,
    {
        match self {
            Self::Top => Self::Top,
            Self::Const(lhs) => Self::Const(f(lhs)),
            Self::Bot => Self::Bot,
        }
    }

    fn apply_binop<F>(self, rhs: Self, f: F) -> Self
    where
        F: FnOnce(Immediate, Immediate) -> Immediate,
    {
        match (self, rhs) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Const(lhs), Self::Const(rhs)) => Self::Const(f(lhs, rhs)),
            (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
        }
    }

    fn not(self) -> Self {
        self.apply_unop(ops::Not::not)
    }

    fn neg(self) -> Self {
        self.apply_unop(ops::Neg::neg)
    }

    fn add(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::Add::add)
    }

    fn sub(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::Sub::sub)
    }

    fn mul(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::Mul::mul)
    }

    fn udiv(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::udiv)
    }

    fn sdiv(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::sdiv)
    }

    fn lt(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::lt)
    }

    fn gt(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::gt)
    }

    fn slt(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::slt)
    }

    fn sgt(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::sgt)
    }

    fn le(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::le)
    }

    fn ge(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::ge)
    }

    fn sle(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::sle)
    }

    fn sge(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::sge)
    }

    fn eq(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::imm_eq)
    }

    fn ne(self, rhs: Self) -> Self {
        self.apply_binop(rhs, Immediate::imm_ne)
    }

    fn and(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::BitAnd::bitand)
    }

    fn or(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::BitOr::bitor)
    }

    fn xor(self, rhs: Self) -> Self {
        self.apply_binop(rhs, ops::BitXor::bitxor)
    }

    fn sext(self, ty: Type) -> Self {
        self.apply_unop(|val| Immediate::sext(val, ty))
    }

    fn zext(self, ty: Type) -> Self {
        self.apply_unop(|val| Immediate::zext(val, ty))
    }

    fn trunc(self, ty: Type) -> Self {
        self.apply_unop(|val| Immediate::trunc(val, ty))
    }
}

impl Default for LatticeCell {
    fn default() -> Self {
        Self::Bot
    }
}
