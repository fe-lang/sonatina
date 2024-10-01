use std::fmt;

use sonatina_ir::{
    ir_writer::{DisplayableWithFunc, DisplayableWithModule, ValueWithTy},
    module::FuncRef,
    types::CompoundType,
    BlockId, Function, Insn, InstId, Type, ValueId,
};

#[derive(Debug, Clone, Copy)]
pub enum ErrorKind {
    // Function errors
    PhiInEntryBlock(InstId),
    // Block errors
    EmptyBlock(BlockId),
    TerminatorBeforeEnd(InstId),
    NotEndedByTerminator(InstId),
    InstructionMapMismatched(InstId),
    BranchBrokenLink(InstId),
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
            PhiInEntryBlock(inst) => {
                let inst = DisplayableWithFunc(inst, func);
                write!(f, "phi instruction in entry block, {inst}")
            }
            EmptyBlock(block) => write!(f, "empty block, {block}"),
            TerminatorBeforeEnd(inst) => {
                let inst = DisplayableWithFunc(inst, func);
                write!(f, "terminator instruction mid-block, {inst}")
            }
            NotEndedByTerminator(inst) => {
                let inst = DisplayableWithFunc(inst, func);
                write!(f, "last instruction not terminator, {inst}")
            }
            InstructionMapMismatched(inst) => {
                let inst = DisplayableWithFunc(inst, func);
                write!(f, "instruction not mapped to block, {inst}")
            }
            BranchBrokenLink(inst) => {
                let inst = DisplayableWithFunc(inst, func);
                write!(f, "branch instruction not linked in cfg, {inst}")
            }
            ValueIsNullReference(value) => {
                let value = ValueWithTy(value);
                let value = DisplayableWithFunc(value, func);
                write!(f, "instruction references inexistent value, {value}")
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
                let cmpd_ty = DisplayableWithModule(cmpd_ty, &func.dfg.ctx);
                write!(f, "instruction references inexistent value, {cmpd_ty}")
            }
            BranchToEntryBlock(block) => write!(f, "branch to entry block, {block}"),
            ValueLeak(value) => {
                let value = ValueWithTy(value);
                let value = DisplayableWithFunc(value, func);
                write!(
                    f,
                    "value not assigned by instruction nor from function args, {value}"
                )
            }
            InsnArgWrongType(ty) => {
                let ty = DisplayableWithModule(ty, &func.dfg.ctx);
                write!(f, "argument type inconsistent with instruction, {ty}")
            }
            InsnResultWrongType(ty) => {
                let ty = DisplayableWithModule(ty, &func.dfg.ctx);
                write!(f, "argument type inconsistent with instruction, {ty}")
            }
            CalleeArgWrongType(ty) => {
                let ty = DisplayableWithModule(ty, &func.dfg.ctx);
                write!(f, "argument type inconsistent with callee signature, {ty}")
            }
            CalleeResultWrongType(ty) => {
                let ty = DisplayableWithModule(ty, &func.dfg.ctx);
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
