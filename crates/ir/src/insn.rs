//! This module contains Sonatine IR instructions definitions.

// TODO: Add type checker for instruction arguments.
use std::fmt;

use smallvec::SmallVec;

use crate::{
    function::Function,
    types::{CompoundTypeData, DisplayType},
    value::{DisplayArgValues, DisplayResultValue},
};

use super::{
    module::{DisplayCalleeFuncRef, FuncRef},
    Block, DataFlowGraph, Type, Value, ValueData,
};

/// An opaque reference to [`InsnData`]
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct Insn(pub u32);
cranelift_entity::entity_impl!(Insn);

pub struct DisplayInsn<'a> {
    insn: Insn,
    func: &'a Function,
}

impl<'a> DisplayInsn<'a> {
    pub fn new(insn: Insn, func: &'a Function) -> Self {
        Self { insn, func }
    }
}

impl<'a> fmt::Display for DisplayInsn<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Self { insn, func } = *self;

        let display_result = DisplayResultValue::new(insn, &func.dfg);
        write!(f, "{display_result}")?;

        let display_insn = DisplayInsnData::new(insn, func);
        write!(f, "{display_insn}")
    }
}

/// An instruction data definition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InsnData {
    /// Unary instructions.
    Unary {
        code: UnaryOp,
        args: [Value; 1],
    },

    /// Binary instructions.
    Binary {
        code: BinaryOp,
        args: [Value; 2],
    },

    /// Cast operations.
    Cast {
        code: CastOp,
        args: [Value; 1],
        ty: Type,
    },

    /// Load a value from memory or storage.
    Load {
        args: [Value; 1],
        loc: DataLocationKind,
    },

    /// Store a value to memory or storage.
    Store {
        args: [Value; 2],
        loc: DataLocationKind,
    },

    /// Call a function in the same contract.
    Call {
        func: FuncRef,
        args: SmallVec<[Value; 8]>,
        ret_ty: Type,
    },

    /// Unconditional jump instruction.
    Jump {
        code: JumpOp,
        dests: [Block; 1],
    },

    /// Conditional jump instruction.
    Branch {
        args: [Value; 1],
        dests: [Block; 2],
    },

    /// Indirect jump instruction.
    BrTable {
        args: SmallVec<[Value; 8]>,
        default: Option<Block>,
        table: SmallVec<[Block; 8]>,
    },

    /// Allocate a memory on the stack frame for the given type.
    Alloca {
        ty: Type,
    },

    /// Return.
    Return {
        args: Option<Value>,
    },

    Gep {
        args: SmallVec<[Value; 8]>,
    },

    /// Phi function.
    Phi {
        values: SmallVec<[Value; 8]>,
        blocks: SmallVec<[Block; 8]>,
        ty: Type,
    },
}

/// Indicates where the data is stored.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DataLocationKind {
    /// Volatile memory.
    Memory,
    /// Non-volatile storage.
    Storage,
}

impl fmt::Display for DataLocationKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use DataLocationKind::*;
        write!(
            f,
            "{}",
            match self {
                Memory => "mem",
                Storage => "store",
            }
        )
    }
}

impl InsnData {
    pub fn unary(code: UnaryOp, lhs: Value) -> Self {
        Self::Unary { code, args: [lhs] }
    }

    pub fn binary(code: BinaryOp, lhs: Value, rhs: Value) -> Self {
        Self::Binary {
            code,
            args: [lhs, rhs],
        }
    }

    pub fn cast(code: CastOp, arg: Value, ty: Type) -> Self {
        Self::Cast {
            code,
            args: [arg],
            ty,
        }
    }

    pub fn alloca(ty: Type) -> Self {
        Self::Alloca { ty }
    }

    pub fn jump(dest: Block) -> InsnData {
        InsnData::Jump {
            code: JumpOp::Jump,
            dests: [dest],
        }
    }

    pub fn phi(ty: Type) -> InsnData {
        InsnData::Phi {
            values: SmallVec::new(),
            blocks: SmallVec::new(),
            ty,
        }
    }

    pub fn analyze_branch(&self) -> BranchInfo {
        match self {
            Self::Jump { dests, .. } => BranchInfo::Jump { dest: dests[0] },

            Self::Branch { args, dests } => BranchInfo::Br {
                cond: args[0],
                dests,
            },

            Self::BrTable {
                args,
                default,
                table,
            } => BranchInfo::BrTable {
                args,
                default: *default,
                table,
            },

            _ => BranchInfo::NotBranch,
        }
    }

    pub fn remove_branch_dest(&mut self, dest: Block) {
        match self {
            Self::Jump { .. } => panic!("can't remove destination from `Jump` insn"),

            Self::Branch { dests, .. } => {
                let remain = if dests[0] == dest {
                    dests[1]
                } else if dests[1] == dest {
                    dests[0]
                } else {
                    panic!("no dests found in the branch destination")
                };
                *self = Self::jump(remain);
            }

            Self::BrTable { default, table, .. } => {
                if Some(dest) == *default {
                    *default = None;
                } else {
                    table.retain(|block| dest != *block);
                }

                let branch_info = self.analyze_branch();
                if branch_info.dests_num() == 1 {
                    *self = Self::jump(branch_info.iter_dests().next().unwrap());
                }
            }

            _ => panic!("not a branch"),
        }
    }

    pub fn rewrite_branch_dest(&mut self, from: Block, to: Block) {
        match self {
            Self::Jump { dests, .. } => {
                if dests[0] == from {
                    dests[0] = to
                }
            }

            Self::Branch { dests, .. } => {
                for block in dests.iter_mut() {
                    if *block == from {
                        *block = to;
                    }
                }
            }

            Self::BrTable { default, table, .. } => {
                match default {
                    Some(default_block) if *default_block == from => {
                        *default = Some(to);
                    }
                    _ => {}
                }

                for block in table.iter_mut() {
                    if *block == from {
                        *block = to
                    }
                }
            }

            _ => {}
        }
    }

    pub fn args(&self) -> &[Value] {
        match self {
            Self::Binary { args, .. } | Self::Store { args, .. } => args,

            Self::Unary { args, .. }
            | Self::Cast { args, .. }
            | Self::Load { args, .. }
            | Self::Branch { args, .. } => args,

            Self::Call { args, .. }
            | Self::BrTable { args, .. }
            | Self::Phi { values: args, .. } => args,

            Self::Return { args } => args.as_ref().map(core::slice::from_ref).unwrap_or_default(),

            _ => &[],
        }
    }

    pub fn args_mut(&mut self) -> &mut [Value] {
        match self {
            Self::Binary { args, .. } | Self::Store { args, .. } => args,

            Self::Unary { args, .. }
            | Self::Cast { args, .. }
            | Self::Load { args, .. }
            | Self::Branch { args, .. } => args,

            Self::Call { args, .. }
            | Self::BrTable { args, .. }
            | Self::Phi { values: args, .. } => args,

            Self::Return { args } => args.as_mut().map(core::slice::from_mut).unwrap_or_default(),

            _ => &mut [],
        }
    }

    pub fn append_phi_arg(&mut self, value: Value, block: Block) {
        match self {
            Self::Phi { values, blocks, .. } => {
                values.push(value);
                blocks.push(block)
            }
            _ => panic!("expects `InsnData::phi` but got `{:?}`", self),
        }
    }

    /// Remove phi arg that flow through the `from`.
    ///
    /// # Panics
    /// If `insn` is not a phi insn or there is no phi argument from the block, then the function panics.
    pub fn remove_phi_arg(&mut self, from: Block) -> Value {
        let (values, blocks) = match self {
            InsnData::Phi { values, blocks, .. } => (values, blocks),
            _ => panic!("insn is not a phi function"),
        };

        let mut index = None;
        for (i, block) in blocks.iter().enumerate() {
            if *block == from {
                index = Some(i);
                break;
            }
        }

        let index = index.unwrap();
        blocks.remove(index);
        values.remove(index)
    }

    pub fn phi_blocks(&self) -> &[Block] {
        match self {
            InsnData::Phi { blocks, .. } => blocks,
            _ => panic!("insn is not a phi function"),
        }
    }

    pub fn phi_blocks_mut(&mut self) -> &mut [Block] {
        match self {
            InsnData::Phi { blocks, .. } => blocks,
            _ => panic!("insn is not a phi function"),
        }
    }

    pub fn replace_arg(&mut self, new_arg: Value, idx: usize) {
        self.args_mut()[idx] = new_arg;
    }

    pub fn is_phi(&self) -> bool {
        matches!(self, InsnData::Phi { .. })
    }

    pub fn is_return(&self) -> bool {
        matches!(self, InsnData::Return { .. })
    }

    pub fn is_branch(&self) -> bool {
        matches!(
            self,
            InsnData::Jump { .. } | InsnData::Branch { .. } | InsnData::BrTable { .. }
        )
    }

    pub fn has_side_effect(&self) -> bool {
        matches!(
            self,
            InsnData::Load { .. }
                | InsnData::Store { .. }
                | InsnData::Call { .. }
                | InsnData::Return { .. }
                | InsnData::Alloca { .. }
        )
    }

    pub fn may_trap(&self) -> bool {
        match self {
            InsnData::Load { .. } | InsnData::Store { .. } | InsnData::Call { .. } => true,
            InsnData::Binary { code, .. } => matches!(code, BinaryOp::Udiv | BinaryOp::Sdiv),
            _ => false,
        }
    }

    pub fn result_type(&self, dfg: &DataFlowGraph) -> Option<Type> {
        match self {
            Self::Unary { args, .. } => Some(dfg.value_ty(args[0])),
            Self::Binary { code, args } => Some(code.result_type(dfg, args)),
            Self::Cast { ty, .. } => Some(*ty),
            Self::Load { args, .. } => {
                let ptr_ty = dfg.value_ty(args[0]);
                debug_assert!(dfg.ctx.with_ty_store(|s| s.is_ptr(ptr_ty)));
                dfg.ctx.with_ty_store(|s| s.deref(ptr_ty))
            }
            Self::Gep { args } => Some(get_gep_result_type(dfg, args[0], &args[1..])),
            Self::Call { ret_ty, .. } => Some(*ret_ty),
            Self::Phi { ty, .. } => Some(*ty),
            Self::Alloca { ty } => Some(dfg.ctx.with_ty_store_mut(|s| s.make_ptr(*ty))),
            _ => None,
        }
    }
}

pub struct DisplayInsnData<'a> {
    insn: Insn,
    func: &'a Function,
}

impl<'a> DisplayInsnData<'a> {
    pub fn new(insn: Insn, func: &'a Function) -> Self {
        Self { insn, func }
    }
}

impl<'a> fmt::Display for DisplayInsnData<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use InsnData::*;
        let Self { insn, func } = *self;
        let dfg = &func.dfg;
        let insn_data = dfg.insn_data(insn);
        match insn_data {
            Unary { code, args } => {
                let v = DisplayArgValues::new(args, dfg);
                write!(f, "{} {v};", code.as_str())
            }
            Binary { code, args } => {
                let v = DisplayArgValues::new(args, dfg);
                write!(f, "{} {v};", code.as_str(),)
            }
            Cast { code, args, .. } => {
                let v = DisplayArgValues::new(args, dfg);
                write!(f, "{} {v};", code.as_str())
            }
            Load { args, loc } => {
                let v = DisplayArgValues::new(args, dfg);
                write!(f, "{loc} load {v};")
            }
            Store { args, loc } => {
                let v = DisplayArgValues::new(args, dfg);
                write!(f, "store {loc} {v};")
            }
            Call {
                args, func: callee, ..
            } => {
                let v = DisplayArgValues::new(args, dfg);
                let callee = DisplayCalleeFuncRef::new(callee, func);
                write!(f, "call %{callee} {v};")
            }
            Jump { code, dests } => {
                let block = dests[0];
                write!(f, "{code} {block};")
            }
            Branch { args, dests } => {
                let v = DisplayArgValues::new(args, dfg);
                write!(f, "branch {v} {} {};", dests[0], dests[1])
            }
            BrTable {
                args,
                default,
                table,
            } => {
                let v = DisplayArgValues::new(args, dfg);
                write!(f, "br_table {v}")?;
                if let Some(block) = default {
                    write!(f, " {block}")?;
                }
                for block in &table[..table.len() - 2] {
                    write!(f, " {block}")?;
                }
                write!(f, " {};", table[table.len() - 1])
            }
            Alloca { ty } => {
                let display_ty = DisplayType::new(*ty, dfg);
                write!(f, "alloca {display_ty};")
            }
            Return { args } => {
                write!(f, "ret")?;
                if let Some(arg) = args {
                    let arg = [*arg];
                    let v = DisplayArgValues::new(&arg, dfg);
                    write!(f, " {v}")?;
                }
                write!(f, ";")
            }
            Gep { args } => {
                let v = DisplayArgValues::new(args, dfg);
                write!(f, "gep {v};")
            }
            Phi { values, blocks, .. } => {
                write!(f, "phi")?;
                for (value, block) in values.iter().zip(blocks.iter()) {
                    let value = [*value];
                    let v = DisplayArgValues::new(&value, dfg);
                    write!(f, " ({v} {block})")?;
                }
                write!(f, ";")
            }
        }
    }
}
/// Unary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Not,
    Neg,
}

impl UnaryOp {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Not => "not",
            Self::Neg => "neg",
        }
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Udiv,
    Sdiv,
    Lt,
    Gt,
    Slt,
    Sgt,
    Le,
    Ge,
    Sle,
    Sge,
    Eq,
    Ne,
    And,
    Or,
    Xor,
}

impl BinaryOp {
    pub fn is_commutative(self) -> bool {
        matches!(
            self,
            Self::Add | Self::Mul | Self::And | Self::Or | Self::Xor
        )
    }

    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::Udiv => "udiv",
            Self::Sdiv => "sdiv",
            Self::Lt => "lt",
            Self::Gt => "gt",
            Self::Slt => "slt",
            Self::Sgt => "sgt",
            Self::Le => "le",
            Self::Ge => "ge",
            Self::Sle => "sle",
            Self::Sge => "sge",
            Self::Eq => "eq",
            Self::Ne => "ne",
            Self::And => "and",
            Self::Or => "or",
            Self::Xor => "xor",
        }
    }

    fn result_type(self, dfg: &DataFlowGraph, args: &[Value; 2]) -> Type {
        if self.is_cmp() {
            Type::I1
        } else {
            dfg.value_ty(args[0])
        }
    }

    fn is_cmp(self) -> bool {
        matches!(
            self,
            Self::Eq
                | Self::Ne
                | Self::Lt
                | Self::Gt
                | Self::Slt
                | Self::Sgt
                | Self::Le
                | Self::Ge
                | Self::Sle
                | Self::Sge
        )
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CastOp {
    Sext,
    Zext,
    Trunc,
    BitCast,
}

impl CastOp {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Sext => "sext",
            Self::Zext => "zext",
            Self::Trunc => "trunc",
            Self::BitCast => "BitCast",
        }
    }
}

impl fmt::Display for CastOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Unconditional jump operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum JumpOp {
    Jump,
    FallThrough,
}

impl JumpOp {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Jump => "jump",
            Self::FallThrough => "fallthrough",
        }
    }
}

impl fmt::Display for JumpOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Clone, Copy)]
pub enum BranchInfo<'a> {
    NotBranch,

    /// Unconditional jump
    Jump {
        dest: Block,
    },

    /// Conditional jump.
    Br {
        cond: Value,
        dests: &'a [Block],
    },

    /// Indirect jump.
    BrTable {
        args: &'a [Value],
        default: Option<Block>,
        table: &'a [Block],
    },
}

impl<'a> BranchInfo<'a> {
    pub fn iter_dests(self) -> BranchDestIter<'a> {
        BranchDestIter {
            branch_info: self,
            idx: 0,
        }
    }

    pub fn dests_num(self) -> usize {
        match self {
            Self::NotBranch => 0,
            Self::Jump { .. } => 1,
            Self::Br { dests, .. } => dests.len(),
            Self::BrTable { default, table, .. } => table.len() + usize::from(default.is_some()),
        }
    }
}

#[derive(Clone, Copy)]
pub struct BranchDestIter<'a> {
    branch_info: BranchInfo<'a>,
    idx: usize,
}

impl<'a> Iterator for BranchDestIter<'a> {
    type Item = Block;

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.branch_info.dests_num() {
            return None;
        }

        match self.branch_info {
            BranchInfo::Jump { dest } => {
                self.idx += 1;
                Some(dest)
            }

            BranchInfo::Br { dests, .. } => {
                let dest = dests[self.idx];
                self.idx += 1;
                Some(dest)
            }

            BranchInfo::BrTable { default, table, .. } => {
                if let Some(default) = default {
                    let dest = if self.idx == 0 {
                        default
                    } else {
                        table[self.idx - 1]
                    };
                    self.idx += 1;
                    Some(dest)
                } else {
                    let dest = table[self.idx];
                    self.idx += 1;
                    Some(dest)
                }
            }

            BranchInfo::NotBranch => None,
        }
    }
}

fn get_gep_result_type(dfg: &DataFlowGraph, base: Value, indices: &[Value]) -> Type {
    let ctx = &dfg.ctx;
    let base_ty = ctx.with_ty_store(|s| {
        let ty = dfg.value_ty(base);
        debug_assert!(s.is_ptr(ty));
        s.deref(ty).unwrap()
    });

    let mut result_ty = base_ty;
    for &index in indices {
        let Type::Compound(compound) = result_ty else {
            unreachable!()
        };

        result_ty = ctx.with_ty_store(|s| match s.resolve_compound(compound) {
            CompoundTypeData::Array { elem, .. } | CompoundTypeData::Ptr(elem) => *elem,
            CompoundTypeData::Struct(s) => {
                let index = match dfg.value_data(index) {
                    ValueData::Immediate { imm, .. } => imm.as_usize(),
                    _ => unreachable!(),
                };
                s.fields[index]
            }
        });
    }

    ctx.with_ty_store_mut(|s| s.make_ptr(result_ty))
}
