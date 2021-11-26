//! This module contains Sonatine IR instructions definitions.

// TODO: Add type checker for instruction arguments.
use std::fmt;

use smallvec::SmallVec;

use super::{Block, DataFlowGraph, Type, Value};

/// An opaque reference to [`InsnData`]
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct Insn(pub u32);
cranelift_entity::entity_impl!(Insn);

/// An instruction data definition.
#[derive(Debug, Clone, PartialEq, Eq)]
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

    /// Load a value from memory.
    Load { args: [Value; 1], ty: Type },

    /// Store a value to memory.
    Store { args: [Value; 2] },

    /// Unconditional jump operaitons.
    Jump { code: JumpOp, dests: [Block; 1] },

    /// Conditional jump operations.
    Branch { args: [Value; 1], dests: [Block; 2] },

    /// Return.
    Return { args: SmallVec<[Value; 8]> },

    /// Phi funcion.
    Phi {
        values: SmallVec<[Value; 8]>,
        blocks: SmallVec<[Block; 8]>,
        ty: Type,
    },
}

impl InsnData {
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

    pub fn branch_dests(&self) -> &[Block] {
        match self {
            Self::Jump { dests, .. } => dests.as_ref(),
            Self::Branch { dests, .. } => dests.as_ref(),
            _ => &[],
        }
    }

    pub fn branch_dests_mut(&mut self) -> &mut [Block] {
        match self {
            Self::Jump { dests, .. } => dests.as_mut(),
            Self::Branch { dests, .. } => dests.as_mut(),
            _ => &mut [],
        }
    }

    pub fn args(&self) -> &[Value] {
        match self {
            Self::Binary { args, .. } | Self::Store { args, .. } => args,
            Self::Unary { args, .. }
            | Self::Cast { args, .. }
            | Self::Load { args, .. }
            | Self::Branch { args, .. } => args,
            Self::Phi { values: args, .. } | Self::Return { args } => args,
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
            Self::Phi { values, .. } => values,
            _ => &mut [],
        }
    }

    pub fn replace_arg(&mut self, new_arg: Value, idx: usize) {
        self.args_mut()[idx] = new_arg;
    }

    pub fn has_side_effect(&self) -> bool {
        // We assume `Load` has side effect because it may cause trap.
        matches!(
            self,
            InsnData::Load { .. } | InsnData::Store { .. } | InsnData::Return { .. }
        )
    }

    pub(super) fn result_type(&self, dfg: &DataFlowGraph) -> Option<Type> {
        match self {
            Self::Unary { args, .. } => Some(dfg.value_ty(args[0]).clone()),
            Self::Binary { code, args } => Some(code.result_type(dfg, args)),
            Self::Cast { ty, .. } | Self::Load { ty, .. } => Some(ty.clone()),
            Self::Phi { ty, .. } => Some(ty.clone()),
            _ => None,
        }
    }
}

/// Unary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Not,
}

impl UnaryOp {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Not => "not",
        }
    }
}

impl fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    Lt,
    Gt,
    Slt,
    Sgt,
    Eq,
    And,
    Or,
}

impl BinaryOp {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Add => "add",
            Self::Sub => "sub",
            Self::Mul => "mul",
            Self::UDiv => "udiv",
            Self::SDiv => "sdiv",
            Self::Lt => "lt",
            Self::Gt => "gt",
            Self::Slt => "slt",
            Self::Sgt => "sgt",
            Self::Eq => "eq",
            Self::And => "and",
            Self::Or => "or",
        }
    }

    // TODO: Add I1 type.
    fn result_type(self, dfg: &DataFlowGraph, args: &[Value; 2]) -> Type {
        dfg.value_ty(args[0]).clone()
    }
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastOp {
    Sext,
    Zext,
    Trunc,
}

impl CastOp {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Sext => "sext",
            Self::Zext => "zext",
            Self::Trunc => "trunc",
        }
    }
}

impl fmt::Display for CastOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Unconditional jump operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
