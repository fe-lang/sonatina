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
    ir::insn::{BinaryOp, CastOp, ImmediateOp, InsnData, JumpOp},
    ir::types::{Type, U256},
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

        let entry_block = match func.layout.first_block() {
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

        loop {
            let mut changed = false;

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

            if !changed {
                break;
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

        match func.dfg.insn_data(insn) {
            InsnData::Immediate { code } => {
                let new_cell = LatticeCell::from_imm_op(*code);

                let insn_result = func.dfg.insn_result(insn).unwrap();
                self.set_lattice_cell(insn_result, new_cell);
            }

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
        let mut next_block = func.layout.first_block();
        while let Some(block) = next_block {
            next_block = func.layout.next_block_of(block);
            if !self.reachable_blocks.contains(&block) {
                InsnInserter::new(func, CursorLocation::BlockTop(block)).remove_block();
            }
        }
    }

    fn fold_insns(&mut self, func: &mut Function) {
        let mut next_block = func.layout.first_block();
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
        let new_insn_data = if let InsnData::Branch { args, dests } = func.dfg.insn_data(insn) {
            let cell = self.lattice[args[0]];
            if cell.is_top() {
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
            }
        } else {
            let insn_result = match func.dfg.insn_result(insn) {
                Some(result) => result,
                None => return false,
            };
            match self.lattice[insn_result].to_imm_op() {
                Some(op) => InsnData::Immediate { code: op },
                None => return false,
            }
        };

        let mut insn_inserter = InsnInserter::new(func, CursorLocation::At(insn));
        insn_inserter.replace(new_insn_data);
        true
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
                .replace_value(phi_value, func.dfg.insn_arg(insn, 0));
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
    Const(ConstValue),
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
    fn from_imm_op(op: ImmediateOp) -> Self {
        match op {
            ImmediateOp::I8(value) => Self::Const(value.into()),
            ImmediateOp::I16(value) => Self::Const(value.into()),
            ImmediateOp::I32(value) => Self::Const(value.into()),
            ImmediateOp::I64(value) => Self::Const(value.into()),
            ImmediateOp::I128(value) => Self::Const(value.into()),
            ImmediateOp::U8(value) => Self::Const(value.into()),
            ImmediateOp::U16(value) => Self::Const(value.into()),
            ImmediateOp::U32(value) => Self::Const(value.into()),
            ImmediateOp::U64(value) => Self::Const(value.into()),
            ImmediateOp::U128(value) => Self::Const(value.into()),
            ImmediateOp::U256(value) => Self::Const(value.into()),
        }
    }

    fn to_imm_op(self) -> Option<ImmediateOp> {
        match self {
            Self::Top => None,
            Self::Bot => None,
            Self::Const(c) => Some(match c {
                ConstValue::U8(v) => ImmediateOp::U8(v),
                ConstValue::U16(v) => ImmediateOp::U16(v),
                ConstValue::U32(v) => ImmediateOp::U32(v),
                ConstValue::U64(v) => ImmediateOp::U64(v),
                ConstValue::U128(v) => ImmediateOp::U128(v),
                ConstValue::U256(v) => ImmediateOp::U256(v),
            }),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConstValue {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    U256(U256),
}

macro_rules! apply_binop {
    ($lhs:expr, $rhs:expr, $op:ident) => {
        match ($lhs, $rhs) {
            (Self::U8(lhs), Self::U8(rhs)) => lhs.$op(rhs).into(),
            (Self::U16(lhs), Self::U16(rhs)) => lhs.$op(rhs).into(),
            (Self::U32(lhs), Self::U32(rhs)) => lhs.$op(rhs).into(),
            (Self::U64(lhs), Self::U64(rhs)) => lhs.$op(rhs).into(),
            (Self::U128(lhs), Self::U128(rhs)) => lhs.$op(rhs).into(),
            (Self::U256(lhs), Self::U256(rhs)) => lhs.$op(rhs).into(),
            _ => unreachable!(),
        }
    };

    ($lhs:expr, $rhs:ident, $op:ident, signed) => {
        match ($lhs, $rhs) {
            (Self::U8(lhs), Self::U8(rhs)) => lhs.to_signed().$op(rhs.to_signed()).into(),
            (Self::U16(lhs), Self::U16(rhs)) => lhs.to_signed().$op(rhs.to_signed()).into(),
            (Self::U32(lhs), Self::U32(rhs)) => lhs.to_signed().$op(rhs.to_signed()).into(),
            (Self::U64(lhs), Self::U64(rhs)) => lhs.to_signed().$op(rhs.to_signed()).into(),
            (Self::U128(lhs), Self::U128(rhs)) => lhs.to_signed().$op(rhs.to_signed()).into(),
            (Self::U256(lhs), Self::U256(rhs)) => lhs.to_signed().$op(rhs.to_signed()).into(),
            _ => unreachable!(),
        }
    };

    ($lhs:expr, &$rhs:ident, $op:ident, signed) => {
        match ($lhs, $rhs) {
            (Self::U8(lhs), Self::U8(rhs)) => lhs.to_signed().$op(&rhs.to_signed()).into(),
            (Self::U16(lhs), Self::U16(rhs)) => lhs.to_signed().$op(&rhs.to_signed()).into(),
            (Self::U32(lhs), Self::U32(rhs)) => lhs.to_signed().$op(&rhs.to_signed()).into(),
            (Self::U64(lhs), Self::U64(rhs)) => lhs.to_signed().$op(&rhs.to_signed()).into(),
            (Self::U128(lhs), Self::U128(rhs)) => lhs.to_signed().$op(&rhs.to_signed()).into(),
            (Self::U256(lhs), Self::U256(rhs)) => lhs.to_signed().$op(&rhs.to_signed()).into(),
            _ => unreachable!(),
        }
    };
}

impl ConstValue {
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
        apply_binop!(self, rhs, div)
    }

    fn sdiv(self, rhs: Self) -> Self {
        apply_binop!(self, rhs, overflowing_div, signed)
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
        if apply_binop!(self, &rhs, lt) {
            self.one()
        } else {
            self.zero()
        }
    }

    fn gt(self, rhs: Self) -> Self {
        if apply_binop!(self, &rhs, gt) {
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
        if apply_binop!(self, &rhs, lt, signed) {
            self.one()
        } else {
            self.zero()
        }
    }

    fn sgt(self, rhs: Self) -> Self {
        if apply_binop!(self, &rhs, gt, signed) {
            self.one()
        } else {
            self.zero()
        }
    }

    fn zero(self) -> Self {
        match self {
            Self::U8(_) => 0u8.into(),
            Self::U16(_) => 0u16.into(),
            Self::U32(_) => 0u32.into(),
            Self::U64(_) => 0u64.into(),
            Self::U128(_) => 0u128.into(),
            Self::U256(_) => U256::zero().into(),
        }
    }
    fn zext(self, to: &Type) -> Self {
        let panic_msg = "attempt to zext the value to same or smaller type, or non scalar type";
        match self {
            Self::U8(val) => match to {
                Type::I16 => Self::U16(val.into()),
                Type::I32 => Self::U32(val.into()),
                Type::I64 => Self::U64(val.into()),
                Type::I128 => Self::U128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U16(val) => match to {
                Type::I32 => Self::U32(val.into()),
                Type::I64 => Self::U64(val.into()),
                Type::I128 => Self::U128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U32(val) => match to {
                Type::I64 => Self::U64(val.into()),
                Type::I128 => Self::U128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U64(val) => match to {
                Type::I128 => Self::U128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U128(val) => match to {
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U256(_) => panic!("{}", panic_msg),
        }
    }

    fn sext(self, to: &Type) -> Self {
        let panic_msg = "attempt to sext the value to same or smaller type, or non scalar type";
        match self {
            Self::U8(val) => match to {
                Type::I16 => Self::U16((val.to_signed() as i16).to_unsigned()),
                Type::I32 => Self::U32((val.to_signed() as i32).to_unsigned()),
                Type::I64 => Self::U64((val.to_signed() as i64).to_unsigned()),
                Type::I128 => Self::U128((val.to_signed() as i128).to_unsigned()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U16(val) => match to {
                Type::I32 => Self::U32(val.into()),
                Type::I64 => Self::U64(val.into()),
                Type::I128 => Self::U128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U32(val) => match to {
                Type::I64 => Self::U64(val.into()),
                Type::I128 => Self::U128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U64(val) => match to {
                Type::I128 => Self::U128(val.into()),
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U128(val) => match to {
                Type::I256 => Self::U256(val.into()),
                _ => panic!("{}", panic_msg),
            },
            Self::U256(_) => panic!("{}", panic_msg),
        }
    }

    fn trunc(self, to: &Type) -> Self {
        let panic_msg = "attempt to trunc the value to same or larger type, or non scalar type";

        match self {
            Self::U8(_) => panic!("{}", panic_msg),
            Self::U16(val) => match to {
                Type::I8 => Self::U8(val as u8),
                _ => panic!("{}", panic_msg),
            },
            Self::U32(val) => match to {
                Type::I8 => Self::U8(val as u8),
                Type::I16 => Self::U16(val as u16),
                _ => panic!("{}", panic_msg),
            },
            Self::U64(val) => match to {
                Type::I8 => Self::U8(val as u8),
                Type::I16 => Self::U16(val as u16),
                Type::I32 => Self::U32(val as u32),
                _ => panic!("{}", panic_msg),
            },
            Self::U128(val) => match to {
                Type::I8 => Self::U8(val as u8),
                Type::I16 => Self::U16(val as u16),
                Type::I32 => Self::U32(val as u32),
                Type::I64 => Self::U64(val as u64),
                _ => panic!("{}", panic_msg),
            },
            Self::U256(val) => match to {
                Type::I8 => Self::U8(val.low_u32() as u8),
                Type::I16 => Self::U16(val.low_u32() as u16),
                Type::I32 => Self::U32(val.low_u32()),
                Type::I64 => Self::U64(val.low_u64()),
                Type::I128 => Self::U128(val.low_u128()),
                _ => panic!("{}", panic_msg),
            },
        }
    }

    fn one(self) -> Self {
        match self {
            Self::U8(_) => 1u8.into(),
            Self::U16(_) => 1u16.into(),
            Self::U32(_) => 1u32.into(),
            Self::U64(_) => 1u64.into(),
            Self::U128(_) => 1u128.into(),
            Self::U256(_) => U256::one().into(),
        }
    }

    fn is_zero(self) -> bool {
        match self {
            Self::U8(val) => val == 0,
            Self::U16(val) => val == 0,
            Self::U32(val) => val == 0,
            Self::U64(val) => val == 0,
            Self::U128(val) => val == 0,
            Self::U256(val) => val == U256::zero(),
        }
    }
}

macro_rules! impl_const_value_conversion {
    ($(($from:ty, $contr:expr),)*) => {
        $(
            impl From<$from> for ConstValue {
                fn from(v: $from) -> Self {
                    $contr(v.to_unsigned())
                }
            }

            // For `overflowing_*` operation.
            impl From<($from, bool)> for ConstValue {
                fn from(v: ($from, bool)) -> Self {
                    $contr(v.0.to_unsigned())
                }
            }
        )*
    };
}

impl_const_value_conversion! {
    (u8, ConstValue::U8),
    (u16, ConstValue::U16),
    (u32, ConstValue::U32),
    (u64, ConstValue::U64),
    (u128, ConstValue::U128),
    (U256, ConstValue::U256),
    (i8, ConstValue::U8),
    (i16, ConstValue::U16),
    (i32, ConstValue::U32),
    (i64, ConstValue::U64),
    (i128, ConstValue::U128),
    (I256, ConstValue::U256),
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
