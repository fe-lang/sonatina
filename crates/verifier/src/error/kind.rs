use std::fmt;

use sonatina_ir::{
    ir_writer::{FuncWriteCtx, ValueWithTy, WriteWithFunc, WriteWithModule},
    module::FuncRef,
    BlockId, Function, InstId, Type, ValueId,
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
    InstArgWrongType(Type),
    InstResultWrongType(Type),
    CalleeArgWrongType(Type),
    CalleeResultWrongType(Type),
    CompoundTypeIsNullReference(Type),
}

impl ErrorKind {
    pub fn ir_source(&self) -> IrSource {
        use ErrorKind::*;

        match *self {
            PhiInEntryBlock(i) => IrSource::Inst(i),
            EmptyBlock(b) => IrSource::Block(b),
            TerminatorBeforeEnd(i)
            | NotEndedByTerminator(i)
            | InstructionMapMismatched(i)
            | BranchBrokenLink(i) => IrSource::Inst(i),
            ValueIsNullReference(v) => IrSource::Value(v),
            BlockIsNullReference(b) | BranchToEntryBlock(b) => IrSource::Block(b),
            FunctionIsNullReference(f) => IrSource::Callee(f),
            ValueLeak(v) => IrSource::Value(v),
            InstArgWrongType(ty)
            | InstResultWrongType(ty)
            | CalleeArgWrongType(ty)
            | CalleeResultWrongType(ty)
            | CompoundTypeIsNullReference(ty) => IrSource::Type(ty),
        }
    }
}

pub struct DisplayErrorKind<'a> {
    kind: ErrorKind,
    ctx: FuncWriteCtx<'a>,
}

impl<'a> DisplayErrorKind<'a> {
    pub fn new(kind: ErrorKind, func: &'a Function, func_ref: FuncRef) -> Self {
        let ctx = FuncWriteCtx::new(func, func_ref);
        Self { kind, ctx }
    }
}

impl fmt::Display for DisplayErrorKind<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ErrorKind::*;
        match self.kind {
            PhiInEntryBlock(inst) => {
                let inst = inst.dump_string(&self.ctx);
                write!(f, "phi instruction in entry block, {inst}")
            }
            EmptyBlock(block) => write!(f, "empty block, {block}"),
            TerminatorBeforeEnd(inst) => {
                let inst = inst.dump_string(&self.ctx);
                write!(f, "terminator instruction mid-block, {inst}")
            }
            NotEndedByTerminator(inst) => {
                let inst = inst.dump_string(&self.ctx);
                write!(f, "last instruction not terminator, {inst}")
            }
            InstructionMapMismatched(inst) => {
                let inst = inst.dump_string(&self.ctx);
                write!(f, "instruction not mapped to block, {inst}")
            }
            BranchBrokenLink(inst) => {
                let inst = inst.dump_string(&self.ctx);
                write!(f, "branch instruction not linked in cfg, {inst}")
            }
            ValueIsNullReference(value) => {
                let value = ValueWithTy(value).dump_string(&self.ctx);
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
                let cmpd_ty = cmpd_ty.dump_string(self.ctx.module_ctx());
                write!(f, "instruction references inexistent value, {cmpd_ty}")
            }
            BranchToEntryBlock(block) => write!(f, "branch to entry block, {block}"),
            ValueLeak(value) => {
                let value = ValueWithTy(value).dump_string(&self.ctx);
                write!(
                    f,
                    "value not assigned by instruction nor from function args, {value}"
                )
            }
            InstArgWrongType(ty) => {
                let ty = ty.dump_string(self.ctx.module_ctx());
                write!(f, "argument type inconsistent with instruction, {ty}")
            }
            InstResultWrongType(ty) => {
                let ty = ty.dump_string(self.ctx.module_ctx());
                write!(f, "argument type inconsistent with instruction, {ty}")
            }
            CalleeArgWrongType(ty) => {
                let ty = ty.dump_string(self.ctx.module_ctx());
                write!(f, "argument type inconsistent with callee signature, {ty}")
            }
            CalleeResultWrongType(ty) => {
                let ty = ty.dump_string(self.ctx.module_ctx());
                write!(f, "result type inconsistent with callee signature, {ty}")
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum IrSource {
    Callee(FuncRef),
    Block(BlockId),
    Inst(InstId),
    Value(ValueId),
    Type(Type),
}
