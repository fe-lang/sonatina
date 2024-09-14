use std::fmt;

use sonatina_ir::{
    insn::DisplayInsn,
    module::FuncRef,
    types::{CompoundType, DisplayCompoundType, DisplayType},
    value::DisplayArgValue,
    Block, Function, Insn, Type, Value,
};

#[derive(Debug, Clone, Copy)]
pub enum ErrorKind {
    // Function errors
    PhiInEntryBlock(Insn),
    // Block errors
    EmptyBlock(Block),
    TerminatorBeforeEnd(Insn),
    NotEndedByTerminator(Insn),
    InstructionMapMismatched(Insn),
    BranchBrokenLink(Insn),
    // Instruction errors
    ValueIsNullReference(Value),
    BlockIsNullReference(Block),
    FunctionIsNullReference(FuncRef),
    CompoundTypeIsNullReference(CompoundType),
    BranchToEntryBlock(Block),
    // SSA form errors
    ValueLeak(Value),
    // Type errors
    InsnArgWrongType(Type),
    InsnResultWrongType(Type),
    CalleeArgWrongType(Type),
    CalleeResultWrongType(Type),
}

pub struct DisplayErrorKind<'a> {
    kind: ErrorKind,
    func: &'a Function,
}

impl<'a> DisplayErrorKind<'a> {
    pub fn new(kind: ErrorKind, func: &'a Function) -> Self {
        Self { kind, func }
    }
}

impl<'a> fmt::Display for DisplayErrorKind<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { kind, func } = *self;
        use ErrorKind::*;
        match kind {
            PhiInEntryBlock(insn) => {
                let insn = DisplayInsn::new(insn, func);
                write!(f, "phi instruction in entry block, {insn}")
            }
            EmptyBlock(block) => write!(f, "empty block, {block}"),
            TerminatorBeforeEnd(insn) => {
                let insn = DisplayInsn::new(insn, func);
                write!(f, "terminator instruction mid-block, {insn}")
            }
            NotEndedByTerminator(insn) => {
                let insn = DisplayInsn::new(insn, func);
                write!(f, "last instruction not terminator, {insn}")
            }
            InstructionMapMismatched(insn) => {
                let insn = DisplayInsn::new(insn, func);
                write!(f, "instruction not mapped to block, {insn}")
            }
            BranchBrokenLink(insn) => {
                let insn = DisplayInsn::new(insn, func);
                write!(f, "branch instruction not linked in cfg, {insn}")
            }
            ValueIsNullReference(value) => {
                let v = DisplayArgValue::new(value, &func.dfg);
                write!(f, "instruction references inexistent value, {v}")
            }
            BlockIsNullReference(block) => {
                write!(f, "instruction references inexistent block, {block}")
            }
            FunctionIsNullReference(func_ref) => {
                write!(
                    f,
                    "instruction references inexistent function, opaque ref: {func_ref:?}"
                )
            }
            CompoundTypeIsNullReference(cmpd_ty) => {
                let cmpd_ty = DisplayCompoundType::new(cmpd_ty, &func.dfg);
                write!(f, "instruction references inexistent value, {cmpd_ty}")
            }
            BranchToEntryBlock(block) => write!(f, "branch to entry block, {block}"),
            ValueLeak(v) => {
                let v = DisplayArgValue::new(v, &func.dfg);
                write!(
                    f,
                    "value not assigned by instruction nor from function args, {v}"
                )
            }
            InsnArgWrongType(ty) => {
                let ty = DisplayType::new(ty, &func.dfg);
                write!(f, "argument type inconsistent with instruction, {ty}")
            }
            InsnResultWrongType(ty) => {
                let ty = DisplayType::new(ty, &func.dfg);
                write!(f, "argument type inconsistent with instruction, {ty}")
            }
            CalleeArgWrongType(ty) => {
                let ty = DisplayType::new(ty, &func.dfg);
                write!(f, "argument type inconsistent with callee signature, {ty}")
            }
            CalleeResultWrongType(ty) => {
                let ty = DisplayType::new(ty, &func.dfg);
                write!(f, "result type inconsistent with callee signature, {ty}")
            }
        }
    }
}
