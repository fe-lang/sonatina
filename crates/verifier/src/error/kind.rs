use std::fmt;

use sonatina_ir::{
    insn::DisplayInsn,
    module::FuncRef,
    types::{DisplayCompoundType, DisplayType},
    value::DisplayArgValue,
    BlockId, Function, Insn, Type, ValueId,
};

#[derive(Debug, Clone, Copy)]
pub enum ErrorKind {
    // Function errors
    PhiInEntryBlock(Insn),
    // Block errors
    EmptyBlock(BlockId),
    TerminatorBeforeEnd(Insn),
    NotEndedByTerminator(Insn),
    InstructionMapMismatched(Insn),
    BranchBrokenLink(Insn),
    // Instruction errors
    ValueIsNullReference(ValueId),
    BlockIsNullReference(BlockId),
    FunctionIsNullReference(FuncRef),
    BranchToEntryBlock(BlockId),
    // SSA form errors
    ValueLeak(ValueId),
    // Type errors
    InsnArgWrongType(Type),
    InsnResultWrongType(Type),
    CalleeArgWrongType(Type),
    CalleeResultWrongType(Type),
    CompoundTypeIsNullReference(Type),
}

impl ErrorKind {
    pub fn ir_source(&self) -> IrSource {
        use ErrorKind::*;

        match *self {
            PhiInEntryBlock(i) => IrSource::Insn(i),
            EmptyBlock(b) => IrSource::Block(b),
            TerminatorBeforeEnd(i)
            | NotEndedByTerminator(i)
            | InstructionMapMismatched(i)
            | BranchBrokenLink(i) => IrSource::Insn(i),
            ValueIsNullReference(v) => IrSource::Value(v),
            BlockIsNullReference(b) | BranchToEntryBlock(b) => IrSource::Block(b),
            FunctionIsNullReference(f) => IrSource::Callee(f),
            ValueLeak(v) => IrSource::Value(v),
            InsnArgWrongType(ty)
            | InsnResultWrongType(ty)
            | CalleeArgWrongType(ty)
            | CalleeResultWrongType(ty)
            | CompoundTypeIsNullReference(ty) => IrSource::Type(ty),
        }
    }
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
            CompoundTypeIsNullReference(ty) => {
                let Type::Compound(cmpd_ty) = ty else {
                    unreachable!("badly formed error");
                };
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

#[derive(Debug, Clone, Copy)]
pub enum IrSource {
    Callee(FuncRef),
    Block(BlockId),
    Insn(Insn),
    Value(ValueId),
    Type(Type),
}
