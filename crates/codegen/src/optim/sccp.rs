//! This module contains a solver for Sparse Conditional Constant Propagation.
//!
//! The algorithm is based on Mark N. Wegman., Frank Kcnncth Zadeck.: Constant propagation with conditional branches:  
//! ACM Transactions on Programming Languages and Systems Volume 13 Issue 2 April 1991 pp 181–210:  
//! <https://doi.org/10.1145/103135.103136>

use std::{cmp::Ordering, collections::BTreeSet};

use cranelift_entity::SecondaryMap;

use crate::{
    cfg::ControlFlowGraph,
    ir::func_cursor::{CursorLocation, FuncCursor, InsnInserter},
    ir::insn::{BinaryOp, CastOp, InsnData, JumpOp},
    ir::types::{Type, U256},
    ir::Immediate,
    Block, Function, Insn, Value,
};

#[derive(Debug, Default)]
pub struct SccpSolver {
    lattice: SecondaryMap<Value, LatticeCell>,
    reachable_edges: BTreeSet<FlowEdge>,
    reachable_blocks: BTreeSet<Block>,

    flow_work: Vec<FlowEdge>,
    ssa_work: Vec<Value>,
}

impl SccpSolver {
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

        self.remove_unreachable_blocks(func);
        self.fold_insns(func);
        cfg.compute(func);
    }

    pub fn clear(&mut self) {
        self.lattice.clear();
        self.reachable_edges.clear();
        self.reachable_blocks.clear();
        self.flow_work.clear();
        self.ssa_work.clear();
    }

    fn eval_edge(&mut self, func: &mut Function, edge: FlowEdge) {
        let dests = func.dfg.branch_dests(edge.insn);
        let dest_idx = edge.dest_idx;

        if self.reachable_edges.contains(&edge) {
            return;
        }
        self.reachable_edges.insert(edge);

        let dest = dests[dest_idx];
        if self.reachable_blocks.contains(&dest) {
            self.eval_phis_in(func, dest);
        } else {
            self.reachable_blocks.insert(dest);
            self.eval_insns_in(func, dest);
        }

        if let Some(dest_last_insn) = func.layout.last_insn_of(dest) {
            if func.dfg.branch_dests(dest_last_insn).len() == 1 {
                self.flow_work.push(FlowEdge::new(dest_last_insn, 0))
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

        match func.dfg.insn_data(insn) {
            InsnData::Binary { code, args } => {
                let lhs = self.lattice[args[0]];
                let rhs = self.lattice[args[1]];
                let new_cell = match *code {
                    BinaryOp::Add => lhs.add(rhs),
                    BinaryOp::Sub => lhs.sub(rhs),
                    BinaryOp::Mul => lhs.mul(rhs),
                    BinaryOp::UDiv => lhs.udiv(rhs),
                    BinaryOp::SDiv => lhs.sdiv(rhs),
                    BinaryOp::Lt => lhs.lt(rhs),
                    BinaryOp::Gt => lhs.gt(rhs),
                    BinaryOp::Slt => lhs.slt(rhs),
                    BinaryOp::Sgt => lhs.sgt(rhs),
                    BinaryOp::Eq => lhs.const_eq(rhs),
                    BinaryOp::And => lhs.and(rhs),
                    BinaryOp::Or => lhs.or(rhs),
                };

                let insn_result = func.dfg.insn_result(insn).unwrap();
                self.set_lattice_cell(insn_result, new_cell);
            }

            InsnData::Cast { code, args, ty } => {
                let arg_cell = self.lattice[args[0]];
                let new_cell = match code {
                    CastOp::Sext => arg_cell.sext(ty),
                    CastOp::Zext => arg_cell.zext(ty),
                    CastOp::Trunc => arg_cell.trunc(ty),
                };

                let insn_result = func.dfg.insn_result(insn).unwrap();
                self.set_lattice_cell(insn_result, new_cell);
            }

            InsnData::Load { .. } => {
                let insn_result = func.dfg.insn_result(insn).unwrap();
                self.set_lattice_cell(insn_result, LatticeCell::Top);
            }

            InsnData::Jump { .. } => {
                self.flow_work.push(FlowEdge::new(insn, 0));
            }

            InsnData::Branch { args, .. } => {
                let v_cell = self.lattice[args[0]];

                if v_cell.is_top() {
                    // Add both then and else edges.
                    self.flow_work.push(FlowEdge::new(insn, 0));
                    self.flow_work.push(FlowEdge::new(insn, 1));
                } else if v_cell.is_bot() {
                    unreachable!();
                } else if v_cell.is_zero() {
                    // Add else edge.
                    self.flow_work.push(FlowEdge::new(insn, 1));
                } else {
                    // Add then edge.
                    self.flow_work.push(FlowEdge::new(insn, 0));
                }
            }

            InsnData::Store { .. } | InsnData::Return { .. } => {
                // No insn result. Do nothing.
            }

            InsnData::Phi { .. } => unreachable!(),
        }
    }

    fn remove_unreachable_blocks(&mut self, func: &mut Function) {
        let mut next_block = func.layout.entry_block();
        while let Some(block) = next_block {
            next_block = func.layout.next_block_of(block);
            if !self.reachable_blocks.contains(&block) {
                InsnInserter::new(func, CursorLocation::BlockTop(block)).remove_block();
            }
        }
    }

    fn fold_insns(&mut self, func: &mut Function) {
        let mut next_block = func.layout.entry_block();
        while let Some(block) = next_block {
            let mut next_insn = func.layout.first_insn_of(block);
            while let Some(insn) = next_insn {
                next_insn = func.layout.next_insn_of(insn);
                if !self.fold(func, insn) && func.dfg.is_phi(insn) {
                    self.try_fold_phi(func, insn);
                }
            }

            next_block = func.layout.next_block_of(block);
        }
    }

    fn fold(&mut self, func: &mut Function, insn: Insn) -> bool {
        if let InsnData::Branch { args, dests } = func.dfg.insn_data(insn) {
            let cell = self.lattice[args[0]];
            let insn_data = if cell.is_top() {
                return false;
            } else if cell.is_bot() {
                unreachable!();
            } else if cell.is_zero() {
                // A then  edge is unreachable. Replace `br` to `jump else`.
                InsnData::Jump {
                    code: JumpOp::Jump,
                    dests: [dests[1]],
                }
            } else {
                // An else edge is unreachable. Replace `br` to `jump then`.
                InsnData::Jump {
                    code: JumpOp::Jump,
                    dests: [dests[0]],
                }
            };
            InsnInserter::new(func, CursorLocation::At(insn)).replace(insn_data);
            true
        } else {
            let insn_result = match func.dfg.insn_result(insn) {
                Some(result) => result,
                None => return false,
            };

            let imm = match self.lattice[insn_result].to_imm() {
                Some(imm) => imm,
                None => return false,
            };

            InsnInserter::new(func, CursorLocation::At(insn)).remove_insn();
            let new_value = func.dfg.make_imm_value(imm);
            func.dfg.change_to_alias(insn_result, new_value);
            true
        }
    }

    fn try_fold_phi(&mut self, func: &mut Function, insn: Insn) {
        debug_assert!(func.dfg.is_phi(insn));

        let mut blocks = func.dfg.phi_blocks(insn).to_vec();
        blocks.retain(|block| !self.reachable_blocks.contains(block));
        for block in blocks {
            func.dfg.remove_phi_arg_from_block(insn, block);
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
        let dests = func.dfg.branch_dests(last_insn);
        for (i, dest) in dests.iter().enumerate() {
            if *dest == to && self.reachable_edges.contains(&FlowEdge::new(last_insn, i)) {
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct FlowEdge {
    insn: Insn,
    dest_idx: usize,
}

impl FlowEdge {
    fn new(insn: Insn, dest_idx: usize) -> Self {
        Self { insn, dest_idx }
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

macro_rules! impl_lattice_binary_ops {
    ($($name:ident,)*) => {
        $(
            fn $name(self, rhs: Self) -> Self {
                match (self, rhs) {
                    (Self::Top, _) | (_, Self::Top) => Self::Top,
                    (Self::Const(v1), Self::Const(v2)) => Self::Const(v1.$name(v2)),
                    (Self::Bot, _) | (_, Self::Bot) => Self::Bot,
                }
            }
        )*
    };
}

macro_rules! impl_lattice_cast_ops {
    ($($name:ident,)*) => {
        $(
            fn $name(self, ty: &Type) -> Self {
                match (self) {
                    Self::Top  => Self::Top,
                    Self::Const(v1) => Self::Const(v1.$name(ty)),
                    Self::Bot => Self::Bot,
                }
            }
        )*
    };
}

impl LatticeCell {
    fn to_imm(self) -> Option<Immediate> {
        match self {
            Self::Top => None,
            Self::Bot => None,
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

    impl_lattice_binary_ops! {
        add,
        sub,
        mul,
        udiv,
        sdiv,
        lt,
        gt,
        slt,
        sgt,
        const_eq,
        and,
        or,
    }

    impl_lattice_cast_ops! {
        sext,
        zext,
        trunc,
    }
}

impl Default for LatticeCell {
    fn default() -> Self {
        Self::Bot
    }
}

macro_rules! apply_binop {
    ($lhs:expr, $rhs:expr, $op:ident) => {
        match ($lhs, $rhs) {
            (Self::I8(lhs), Self::I8(rhs)) => lhs.$op(rhs).into(),
            (Self::I16(lhs), Self::I16(rhs)) => lhs.$op(rhs).into(),
            (Self::I32(lhs), Self::I32(rhs)) => lhs.$op(rhs).into(),
            (Self::I64(lhs), Self::I64(rhs)) => lhs.$op(rhs).into(),
            (Self::I128(lhs), Self::I128(rhs)) => lhs.$op(rhs).into(),
            (Self::U256(lhs), Self::U256(rhs)) => lhs.$op(rhs).into(),
            _ => unreachable!(),
        }
    };

    ($lhs:expr, $rhs:ident, $op:ident, unsigned) => {
        match ($lhs, $rhs) {
            (Self::I8(lhs), Self::I8(rhs)) => lhs.to_unsigned().$op(rhs.to_unsigned()).into(),
            (Self::I16(lhs), Self::I16(rhs)) => lhs.to_unsigned().$op(rhs.to_unsigned()).into(),
            (Self::I32(lhs), Self::I32(rhs)) => lhs.to_unsigned().$op(rhs.to_unsigned()).into(),
            (Self::I64(lhs), Self::I64(rhs)) => lhs.to_unsigned().$op(rhs.to_unsigned()).into(),
            (Self::I128(lhs), Self::I128(rhs)) => lhs.to_unsigned().$op(rhs.to_unsigned()).into(),
            (Self::U256(lhs), Self::U256(rhs)) => lhs.to_unsigned().$op(rhs.to_unsigned()).into(),
            _ => unreachable!(),
        }
    };

    ($lhs:expr, &$rhs:ident, $op:ident, unsigned) => {
        match ($lhs, $rhs) {
            (Self::I8(lhs), Self::I8(rhs)) => lhs.to_unsigned().$op(&rhs.to_unsigned()).into(),
            (Self::I16(lhs), Self::I16(rhs)) => lhs.to_unsigned().$op(&rhs.to_unsigned()).into(),
            (Self::I32(lhs), Self::I32(rhs)) => lhs.to_unsigned().$op(&rhs.to_unsigned()).into(),
            (Self::I64(lhs), Self::I64(rhs)) => lhs.to_unsigned().$op(&rhs.to_unsigned()).into(),
            (Self::I128(lhs), Self::I128(rhs)) => lhs.to_unsigned().$op(&rhs.to_unsigned()).into(),
            (Self::U256(lhs), Self::U256(rhs)) => lhs.to_unsigned().$op(&rhs.to_unsigned()).into(),
            _ => unreachable!(),
        }
    };
}

impl Immediate {
    fn add(self, rhs: Self) -> Self {
        apply_binop!(self, rhs, overflowing_add)
    }

    fn sub(self, rhs: Self) -> Self {
        apply_binop!(self, rhs, overflowing_sub)
    }

    fn mul(self, rhs: Self) -> Self {
        apply_binop!(self, rhs, overflowing_mul)
    }

    fn udiv(self, rhs: Self) -> Self {
        use std::ops::Div;
        apply_binop!(self, rhs, div, unsigned)
    }

    fn sdiv(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Self::I8(lhs), Self::I8(rhs)) => lhs.overflowing_div(rhs).into(),
            (Self::I16(lhs), Self::I16(rhs)) => lhs.overflowing_div(rhs).into(),
            (Self::I32(lhs), Self::I32(rhs)) => lhs.overflowing_div(rhs).into(),
            (Self::I64(lhs), Self::I64(rhs)) => lhs.overflowing_div(rhs).into(),
            (Self::I128(lhs), Self::I128(rhs)) => lhs.overflowing_div(rhs).into(),
            (Self::U256(lhs), Self::U256(rhs)) => {
                (lhs.to_signed().overflowing_div(rhs.to_signed()))
                    .0
                    .to_unsigned()
                    .into()
            }
            _ => unreachable!(),
        }
    }

    fn and(self, rhs: Self) -> Self {
        use std::ops::BitAnd;
        apply_binop!(self, rhs, bitand)
    }

    fn or(self, rhs: Self) -> Self {
        use std::ops::BitOr;
        apply_binop!(self, rhs, bitor)
    }

    fn lt(self, rhs: Self) -> Self {
        if apply_binop!(self, &rhs, lt, unsigned) {
            self.one()
        } else {
            self.zero()
        }
    }

    fn gt(self, rhs: Self) -> Self {
        if apply_binop!(self, &rhs, gt, unsigned) {
            self.one()
        } else {
            self.zero()
        }
    }

    fn const_eq(self, rhs: Self) -> Self {
        if self == rhs {
            self.one()
        } else {
            self.zero()
        }
    }

    fn slt(self, rhs: Self) -> Self {
        if apply_binop!(self, &rhs, lt) {
            self.one()
        } else {
            self.zero()
        }
    }

    fn sgt(self, rhs: Self) -> Self {
        if apply_binop!(self, &rhs, gt) {
            self.one()
        } else {
            self.zero()
        }
    }

    fn zero(self) -> Self {
        match self {
            Self::I8(_) => 0i8.into(),
            Self::I16(_) => 0i16.into(),
            Self::I32(_) => 0i32.into(),
            Self::I64(_) => 0i64.into(),
            Self::I128(_) => 0i128.into(),
            Self::U256(_) => U256::zero().into(),
        }
    }

    fn zext(self, to: &Type) -> Self {
        let panic_msg = "attempt to zext the value to same or smaller type, or non scalar type";
        match self {
            Self::I8(val) => match to {
                Type::I16 => Self::I16(val.to_unsigned().into()),
                Type::I32 => Self::I32(val.to_unsigned().into()),
                Type::I64 => Self::I64(val.to_unsigned().into()),
                Type::I128 => Self::I128(val.to_unsigned().into()),
                Type::I256 => Self::U256(val.to_unsigned().into()),
                _ => panic!("{}", panic_msg),
            },
            Self::I16(val) => match to {
                Type::I32 => Self::I32(val.to_unsigned().into()),
                Type::I64 => Self::I64(val.to_unsigned().into()),
                Type::I128 => Self::I128(val.to_unsigned().into()),
                Type::I256 => Self::U256(val.to_unsigned().into()),
                _ => panic!("{}", panic_msg),
            },
            Self::I32(val) => match to {
                Type::I64 => Self::I64(val.to_unsigned().into()),
                Type::I128 => Self::I128(val.to_unsigned().into()),
                Type::I256 => Self::U256(val.to_unsigned().into()),
                _ => panic!("{}", panic_msg),
            },
            Self::I64(val) => match to {
                Type::I128 => Self::I128(val.to_unsigned().into()),
                Type::I256 => Self::U256(val.to_unsigned().into()),
                _ => panic!("{}", panic_msg),
            },
            Self::I128(val) => match to {
                Type::I256 => Self::U256(val.to_unsigned().into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U256(_) => panic!("{}", panic_msg),
        }
    }

    fn sext(self, to: &Type) -> Self {
        let panic_msg = "attempt to sext the value to same or smaller type, or non scalar type";
        match self {
            Self::I8(val) => match to {
                Type::I16 => Self::I16(val as i16),
                Type::I32 => Self::I32(val as i32),
                Type::I64 => Self::I64(val as i64),
                Type::I128 => Self::I128(val as i128),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::I16(val) => match to {
                Type::I32 => Self::I32(val.into()),
                Type::I64 => Self::I64(val.into()),
                Type::I128 => Self::I128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::I32(val) => match to {
                Type::I64 => Self::I64(val.into()),
                Type::I128 => Self::I128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::I64(val) => match to {
                Type::I128 => Self::I128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::I128(val) => match to {
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U256(_) => panic!("{}", panic_msg),
        }
    }

    fn trunc(self, to: &Type) -> Self {
        let panic_msg = "attempt to trunc the value to same or larger type, or non scalar type";

        match self {
            Self::I8(_) => panic!("{}", panic_msg),
            Self::I16(val) => match to {
                Type::I8 => Self::I8(val as i8),
                _ => panic!("{}", panic_msg),
            },
            Self::I32(val) => match to {
                Type::I8 => Self::I8(val as i8),
                Type::I16 => Self::I16(val as i16),
                _ => panic!("{}", panic_msg),
            },
            Self::I64(val) => match to {
                Type::I8 => Self::I8(val as i8),
                Type::I16 => Self::I16(val as i16),
                Type::I32 => Self::I32(val as i32),
                _ => panic!("{}", panic_msg),
            },
            Self::I128(val) => match to {
                Type::I8 => Self::I8(val as i8),
                Type::I16 => Self::I16(val as i16),
                Type::I32 => Self::I32(val as i32),
                Type::I64 => Self::I64(val as i64),
                _ => panic!("{}", panic_msg),
            },
            Self::U256(val) => match to {
                Type::I8 => Self::I8(val.low_u32() as i8),
                Type::I16 => Self::I16(val.low_u32() as i16),
                Type::I32 => Self::I32(val.low_u32() as i32),
                Type::I64 => Self::I64(val.low_u64() as i64),
                Type::I128 => Self::I128(val.low_u128() as i128),
                _ => panic!("{}", panic_msg),
            },
        }
    }

    fn one(self) -> Self {
        match self {
            Self::I8(_) => 1i8.into(),
            Self::I16(_) => 1i16.into(),
            Self::I32(_) => 1i32.into(),
            Self::I64(_) => 1i64.into(),
            Self::I128(_) => 1i128.into(),
            Self::U256(_) => U256::one().into(),
        }
    }

    fn is_zero(self) -> bool {
        match self {
            Self::I8(val) => val == 0,
            Self::I16(val) => val == 0,
            Self::I32(val) => val == 0,
            Self::I64(val) => val == 0,
            Self::I128(val) => val == 0,
            Self::U256(val) => val.is_zero(),
        }
    }
}

macro_rules! impl_const_value_conversion {
    ($(($from:ty, $contr:expr),)*) => {
        $(
            // For `overflowing_*` operation.
            impl From<($from, bool)> for Immediate {
                fn from(v: ($from, bool)) -> Self {
                    v.0.into()
                }
            }
        )*
    };
}

impl_const_value_conversion! {
    (u8, Immediate::I8),
    (u16, Immediate::I16),
    (u32, Immediate::I32),
    (u64, Immediate::I64),
    (u128, Immediate::I128),
    (U256, Immediate::U256),
    (i8, Immediate::I8),
    (i16, Immediate::I16),
    (i32, Immediate::I32),
    (i64, Immediate::I64),
    (i128, Immediate::I128),
}

trait SignCast {
    type Signed;
    type Unsigned;

    fn to_signed(self) -> Self::Signed;
    fn to_unsigned(self) -> Self::Unsigned;
}

macro_rules! impl_sign_cast {
    ($unsigned:ty, $signed:ty) => {
        impl SignCast for $unsigned {
            type Signed = $signed;
            type Unsigned = $unsigned;

            fn to_signed(self) -> Self::Signed {
                self as $signed
            }

            fn to_unsigned(self) -> Self::Unsigned {
                self as $unsigned
            }
        }

        impl SignCast for $signed {
            type Signed = $signed;
            type Unsigned = $unsigned;

            fn to_signed(self) -> Self::Signed {
                self as $signed
            }

            fn to_unsigned(self) -> Self::Unsigned {
                self as $unsigned
            }
        }
    };
}

impl_sign_cast!(u8, i8);
impl_sign_cast!(u16, i16);
impl_sign_cast!(u32, i32);
impl_sign_cast!(u64, i64);
impl_sign_cast!(u128, i128);

impl SignCast for U256 {
    type Signed = I256;
    type Unsigned = U256;

    fn to_signed(self) -> Self::Signed {
        I256::from_u256(self)
    }

    fn to_unsigned(self) -> Self::Unsigned {
        self
    }
}

impl SignCast for I256 {
    type Signed = I256;
    type Unsigned = U256;

    fn to_signed(self) -> Self::Signed {
        self
    }

    fn to_unsigned(self) -> Self::Unsigned {
        self.to_u256()
    }
}

const I256_MASK: U256 = primitive_types::U256([
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x7fff_ffff_ffff_ffff,
]);

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
struct I256 {
    is_positive: bool,
    abs: U256,
}

impl I256 {
    fn from_u256(val: U256) -> Self {
        let is_positive = (val & I256_MASK) == val;
        let abs = if is_positive { val } else { !val + U256::one() };

        Self { is_positive, abs }
    }

    fn to_u256(self) -> U256 {
        if self.is_positive {
            self.abs
        } else {
            !self.abs + U256::one()
        }
    }

    fn make_positive(abs: U256) -> Self {
        Self {
            is_positive: true,
            abs,
        }
    }

    fn make_negative(abs: U256) -> Self {
        Self {
            is_positive: false,
            abs,
        }
    }

    fn is_zero(self) -> bool {
        self.abs.is_zero()
    }

    fn is_minimum(self) -> bool {
        !self.is_positive && self.abs != U256::zero() && (self.abs & I256_MASK) == U256::zero()
    }

    fn overflowing_div(self, rhs: I256) -> (I256, bool) {
        if rhs.is_zero() {
            panic!("attempt to divide by zero");
        }

        if self.is_minimum() && !rhs.is_positive && rhs.abs == U256::one() {
            return (self, true);
        }

        let div_abs = self.abs / rhs.abs;

        match (self.is_positive, rhs.is_positive) {
            (true, true) | (false, false) => (I256::make_positive(div_abs), false),
            _ => (I256::make_negative(div_abs), false),
        }
    }
}

impl Ord for I256 {
    fn cmp(&self, rhs: &I256) -> Ordering {
        match (self.is_positive, rhs.is_positive) {
            (true, true) => self.abs.cmp(&rhs.abs),
            (true, false) => Ordering::Greater,
            (false, true) => Ordering::Less,
            (false, false) => self.abs.cmp(&rhs.abs).reverse(),
        }
    }
}

impl PartialOrd<I256> for I256 {
    fn partial_cmp(&self, other: &I256) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i256_conversion() {
        let v_u256 = U256::zero();
        let v_i256 = v_u256.to_signed();
        assert!(v_i256.is_positive);
        assert!(v_i256.is_zero());
        assert_eq!(v_i256.abs, v_u256);
        assert_eq!(v_i256.to_unsigned(), v_u256);

        let v_u256 = U256::one();
        let v_i256 = v_u256.to_signed();
        assert!(v_i256.is_positive);
        assert_eq!(v_i256.abs, v_u256);
        assert_eq!(v_i256.to_unsigned(), v_u256);

        let v_u256 = U256::MAX;
        let v_i256 = v_u256.to_signed();
        assert!(!v_i256.is_positive);
        assert_eq!(v_i256.abs, U256::from(1));
        assert_eq!(v_i256.to_unsigned(), v_u256);

        let v_u256 = U256::one() << 255;
        let v_i256 = v_u256.to_signed();
        assert!(!v_i256.is_positive);
        assert_eq!(v_i256.abs, v_u256);
        assert_eq!(v_i256.to_unsigned(), v_u256);
    }

    #[test]
    fn i256_ord() {
        let zero = U256::zero().to_signed();

        let one = U256::one().to_signed();
        let maximum = (!(U256::one() << 255)).to_signed();

        let minus_one = U256::MAX.to_signed();
        let minimum = (U256::one() << 255).to_signed();

        assert!(zero < one);
        assert!(zero < maximum);
        assert!(minus_one < zero);
        assert!(minimum < zero);

        assert!(one < maximum);
        assert!(minimum < minus_one);

        assert!(minus_one < one);
        assert!(minus_one < maximum);
        assert!(minimum < one);
        assert!(minimum < maximum);
    }

    #[test]
    fn i256_div() {
        let two = (U256::one() * U256::from(2)).to_signed();
        let four = (U256::one() * U256::from(4)).to_signed();
        assert_eq!(four.overflowing_div(two).0, two);
        assert!(!four.overflowing_div(two).1);
        assert_eq!(two.overflowing_div(four).0, U256::zero().to_signed());

        let minus_two = (U256::one() * U256::from(2)).to_signed();
        let minus_four = (U256::one() * U256::from(4)).to_signed();
        assert_eq!(minus_four.overflowing_div(minus_two).0, two);
        assert_eq!(
            minus_two.overflowing_div(minus_four).0,
            U256::zero().to_signed()
        );

        assert_eq!(four.overflowing_div(minus_two).0, minus_two);
        assert_eq!(two.overflowing_div(minus_four).0, U256::zero().to_signed());
        assert_eq!(minus_four.overflowing_div(two).0, minus_two);
        assert_eq!(minus_two.overflowing_div(four).0, U256::zero().to_signed());
    }

    #[test]
    fn i256_div_overflow() {
        let minus_one = U256::MAX.to_signed();
        let minimum = (U256::one() << 255).to_signed();
        let div_res = minimum.overflowing_div(minus_one);
        assert_eq!(div_res.0, minimum);
        assert!(div_res.1);
    }

    #[should_panic]
    #[test]
    fn i256_zero_division() {
        let one = U256::one().to_signed();
        let zero = U256::zero().to_signed();
        one.overflowing_div(zero);
    }
}
