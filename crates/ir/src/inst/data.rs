use std::io;

use macros::Inst;
use smallvec::SmallVec;

use crate::{
    GlobalVariableRef, Type, ValueId,
    ir_writer::IrWrite,
    module::{FuncRef, ModuleCtx},
    visitor::{Visitable, VisitableMut},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolRef {
    Func(FuncRef),
    Global(GlobalVariableRef),
}

impl<Ctx> IrWrite<Ctx> for SymbolRef
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        match self {
            Self::Func(f) => f.write(w, ctx),
            Self::Global(gv) => ctx
                .as_ref()
                .with_gv_store(|s| write!(w, "${}", s.gv_data(*gv).symbol)),
        }
    }
}

impl Visitable for SymbolRef {
    fn accept(&self, visitor: &mut dyn crate::visitor::Visitor) {
        match self {
            Self::Func(f) => f.accept(visitor),
            Self::Global(gv) => gv.accept(visitor),
        }
    }
}

impl VisitableMut for SymbolRef {
    fn accept_mut(&mut self, visitor: &mut dyn crate::visitor::VisitorMut) {
        match self {
            Self::Func(f) => f.accept_mut(visitor),
            Self::Global(gv) => gv.accept_mut(visitor),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Read))]
pub struct Mload {
    addr: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
pub struct Mstore {
    addr: ValueId,
    value: ValueId,
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct Gep {
    values: SmallVec<[ValueId; 8]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct GetFunctionPtr {
    func: FuncRef,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect(super::SideEffect::Write))]
pub struct Alloca {
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct InsertValue {
    dest: ValueId,
    idx: ValueId,
    value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct ExtractValue {
    dest: ValueId,
    idx: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct SymAddr {
    sym: SymbolRef,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
pub struct SymSize {
    sym: SymbolRef,
}
