//! This module contains Sonatine IR instructions definitions.

// TODO: Add type checker for instruction arguments.

use std::collections::HashSet;

use id_arena::Id;
use primitive_types::U256;

use super::{Block, DataFlowGraph, Type, Value};

/// An opaque reference to [`InsnData`]
pub type Insn = Id<InsnData>;

/// An instruction data definition.
#[derive(Debug, Clone)]
pub enum InsnData {
    /// Immediate instruction.
    Immediate { code: ImmediateOp },

    /// Binary instruction.
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
    Jump {
        code: JumpOp,
        dest: Block,
        /// Block paramters.
        params: HashSet<Value>,
    },

    /// Conditional jump operations.
    Branch {
        code: BranchOp,
        args: [Value; 1],
        dest: Block,
        /// Block parameters.
        params: HashSet<Value>,
    },
}

impl InsnData {
    pub fn branch_dest(&self) -> Option<Block> {
        match self {
            Self::Jump { dest, .. } | Self::Branch { dest, .. } => Some(*dest),
            _ => None,
        }
    }

    pub fn args(&self) -> &[Value] {
        match self {
            Self::Binary { args, .. } | Self::Store { args, .. } => args,
            Self::Cast { args, .. } | Self::Load { args, .. } | Self::Branch { args, .. } => args,
            _ => &[],
        }
    }

    pub(super) fn result_type(&self, dfg: &DataFlowGraph) -> Option<Type> {
        match self {
            Self::Immediate { code } => Some(code.result_type()),
            Self::Binary { code, args } => Some(code.result_type(dfg, args)),
            Self::Cast { ty, .. } | Self::Load { ty, .. } => Some(ty.clone()),
            _ => None,
        }
    }
}

/// Immidiates.
#[derive(Debug, Clone)]
pub enum ImmediateOp {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    U256(U256),
}

impl ImmediateOp {
    fn result_type(&self) -> Type {
        match self {
            Self::I8(_) | Self::U8(_) => Type::I8,
            Self::I16(_) | Self::U16(_) => Type::I16,
            Self::I32(_) | Self::U32(_) => Type::I32,
            Self::I64(_) | Self::U64(_) => Type::I64,
            Self::U128(_) => Type::I128,
            Self::U256(_) => Type::I256,
        }
    }

    pub(super) fn to_string(&self) -> String {
        match self {
            Self::I8(value) => format!("imm.i8 {}", value.to_string()),
            Self::I16(value) => format!("imm.i16 {}", value.to_string()),
            Self::I32(value) => format!("imm.i32 {}", value.to_string()),
            Self::I64(value) => format!("imm.i64 {}", value.to_string()),
            Self::U8(value) => format!("imm.u8 {}", value.to_string()),
            Self::U16(value) => format!("imm.u16 {}", value.to_string()),
            Self::U32(value) => format!("imm.u32 {}", value.to_string()),
            Self::U64(value) => format!("imm.u64 {}", value.to_string()),
            Self::U128(value) => format!("imm.u128 {}", value.to_string()),
            Self::U256(value) => format!("imm.u256 {}", value.to_string()),
        }
    }
}

/// Binary operations.
#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
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
            Self::Div => "div",
            Self::Lt => "lt",
            Self::Gt => "gt",
            Self::Slt => "slt",
            Self::Sgt => "sgt",
            Self::Eq => "eq",
            Self::And => "and",
            Self::Or => "or",
        }
    }

    fn result_type(self, dfg: &DataFlowGraph, args: &[Value; 2]) -> Type {
        match self {
            Self::Add | Self::Sub | Self::Mul | Self::Div => dfg.value_ty(args[0]).clone(),
            _ => Type::Bool,
        }
    }
}

#[derive(Debug, Clone, Copy)]
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

/// Unconditional jump operations.
#[derive(Debug, Clone, Copy)]
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

/// Conditional jump operations.
#[derive(Debug, Clone, Copy)]
pub enum BranchOp {
    /// Branch if cond is zero.
    Brz,

    /// Branch if cond is non zero.
    Brnz,
}

impl BranchOp {
    pub(super) fn as_str(self) -> &'static str {
        match self {
            Self::Brz => "brz",
            Self::Brnz => "brnz",
        }
    }
}
