//! This module contains Sonatine IR instructions definitions.

// TODO: Add type checker for instruction arguments.
use std::{fmt, str::FromStr};

use smallvec::SmallVec;

use crate::{
    function::Function,
    types::{CompoundTypeData, DisplayType},
    value::{display_arg_values, DisplayArgValue, DisplayResultValue},
};

use super::{
    module::{DisplayCalleeFuncRef, FuncRef},
    Block, DataFlowGraph, Type, Value, ValueData,
};

/// An opaque reference to [`InsnData`]
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord, Default)]
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

        let result = DisplayResultValue::new(insn, &func.dfg);
        write!(f, "{result}")?;

        let insn = DisplayInsnData::new(insn, func);
        write!(f, "{insn}")
    }
}

/// An instruction data definition.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum InsnData {
    /// Unary instructions.
    Unary { code: UnaryOp, args: [Value; 1] },

    /// Binary instructions.
    Binary { code: BinaryOp, args: [Value; 2] },

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
    Jump { dests: [Block; 1] },

    /// Conditional jump instruction.
    Branch { args: [Value; 1], dests: [Block; 2] },

    /// Indirect jump instruction.
    BrTable {
        args: SmallVec<[Value; 8]>,
        default: Option<Block>,
        table: SmallVec<[Block; 8]>,
    },

    /// Allocate a memory on the stack frame for the given type.
    Alloca { ty: Type },

    /// Return.
    Return { args: Option<Value> },

    /// Get element pointer.
    Gep { args: SmallVec<[Value; 8]> },

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

impl DataLocationKind {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Memory => "@memory",
            Self::Storage => "@storage",
        }
    }
}

impl FromStr for DataLocationKind {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "@memory" => Ok(Self::Memory),
            "@storage" => Ok(Self::Storage),
            _ => Err(()),
        }
    }
}

impl fmt::Display for DataLocationKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
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
        InsnData::Jump { dests: [dest] }
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
            Self::Jump { dests } => BranchInfo::Jump { dest: dests[0] },

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
            | Self::Phi { values: args, .. }
            | Self::Gep { args } => args,

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
            | Self::Phi { values: args, .. }
            | Self::Gep { args } => args,

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
                write!(f, "{} ", code.as_str())?;
                display_arg_values(f, args, dfg)?;
                ";".fmt(f)
            }
            Binary { code, args } => {
                write!(f, "{} ", code.as_str())?;
                display_arg_values(f, args, dfg)?;
                ";".fmt(f)
            }
            Cast { code, args, .. } => {
                write!(f, "{} ", code.as_str())?;
                display_arg_values(f, args, dfg)?;
                ";".fmt(f)
            }
            Load { args, loc } => {
                write!(f, "{loc} load ")?;
                display_arg_values(f, args, dfg)?;
                ";".fmt(f)
            }
            Store { args, loc } => {
                write!(f, "store {loc} ")?;
                display_arg_values(f, args, dfg)?;
                ";".fmt(f)
            }
            Call {
                args, func: callee, ..
            } => {
                let callee = DisplayCalleeFuncRef::new(*callee, func);
                write!(f, "call %{callee} ")?;
                display_arg_values(f, args, dfg)?;
                ";".fmt(f)
            }
            Jump { dests } => {
                let block = dests[0];
                write!(f, "jump {block};")
            }
            Branch { args, dests } => {
                "branch ".fmt(f)?;
                display_arg_values(f, args, dfg)?;
                write!(f, " {} {};", dests[0], dests[1])
            }
            BrTable {
                args,
                default,
                table,
            } => {
                "br_table ".fmt(f)?;
                display_arg_values(f, args, dfg)?;
                if let Some(block) = default {
                    write!(f, " {block}")?;
                }
                for block in table {
                    write!(f, " {block}")?;
                }
                ";".fmt(f)
            }
            Alloca { ty } => {
                let ty = DisplayType::new(*ty, dfg);
                write!(f, "alloca {ty};")
            }
            Return { args } => {
                "ret".fmt(f)?;
                if let Some(arg) = args {
                    let v = DisplayArgValue::new(*arg, dfg);
                    write!(f, " {v}")?;
                }
                ";".fmt(f)
            }
            Gep { args } => {
                "gep ".fmt(f)?;
                display_arg_values(f, args, dfg)?;
                ";".fmt(f)
            }
            Phi { values, blocks, .. } => {
                "phi".fmt(f)?;
                for (value, block) in values.iter().zip(blocks.iter()) {
                    let v = DisplayArgValue::new(*value, dfg);
                    write!(f, " ({v} {block})")?;
                }
                ";".fmt(f)
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

impl FromStr for UnaryOp {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "not" => Ok(Self::Not),
            "neg" => Ok(Self::Neg),
            _ => Err(()),
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

impl FromStr for BinaryOp {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "add" => Ok(Self::Add),
            "sub" => Ok(Self::Sub),
            "mul" => Ok(Self::Mul),
            "udiv" => Ok(Self::Udiv),
            "sdiv" => Ok(Self::Sdiv),
            "lt" => Ok(Self::Lt),
            "gt" => Ok(Self::Gt),
            "slt" => Ok(Self::Slt),
            "sgt" => Ok(Self::Sgt),
            "le" => Ok(Self::Le),
            "ge" => Ok(Self::Ge),
            "sle" => Ok(Self::Sle),
            "sge" => Ok(Self::Sge),
            "eq" => Ok(Self::Eq),
            "ne" => Ok(Self::Ne),
            "and" => Ok(Self::And),
            "or" => Ok(Self::Or),
            "xor" => Ok(Self::Xor),
            _ => Err(()),
        }
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
            Self::BitCast => "bitcast",
        }
    }
}

impl fmt::Display for CastOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl FromStr for CastOp {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "sext" => Ok(Self::Sext),
            "zext" => Ok(Self::Zext),
            "trunc" => Ok(Self::Trunc),
            "bitcast" => Ok(Self::BitCast),
            _ => Err(()),
        }
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
    for (i, &index) in indices.iter().enumerate() {
        let Type::Compound(compound) = result_ty else {
            if indices.len() - i == 1 {
                break;
            } else {
                unreachable!()
            }
        };

        result_ty = ctx.with_ty_store(|s| match s.resolve_compound(compound) {
            CompoundTypeData::Array { elem, .. } => *elem,
            CompoundTypeData::Ptr(_) => result_ty,
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
