pub mod arith;
pub mod cast;
pub mod cmp;
pub mod control_flow;
pub mod data;
pub mod evm;
#[macro_use]
pub mod inst_set;
pub mod logic;

use std::{
    any::{Any, TypeId},
    io,
};

use dyn_clone::DynClone;
use macros::inst_prop;

use crate::{
    InstSetBase,
    ir_writer::{FuncWriteCtx, IrWrite},
    visitor::{Visitable, VisitableMut},
};

/// An opaque reference to dynamic [`Inst`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct InstId(pub u32);
cranelift_entity::entity_impl!(InstId);

pub trait Inst:
    inst_set::sealed::Registered + DynClone + Any + Send + Sync + Visitable + VisitableMut
{
    fn side_effect(&self) -> SideEffect;
    fn as_text(&self) -> &'static str;
    fn is_terminator(&self) -> bool;
}

pub trait InstExt: Inst {
    /// Checks if the this instruction type belongs to the given `InstSetBase`.
    ///
    /// # Returns
    ///
    /// * `Option<&dyn HasInst<Self>>` - If this instruction type belongs to the
    ///   set, returns `Some` with a reference to the corresponding `HasInst`.
    ///   Otherwise, returns `None`.
    fn belongs_to(isb: &dyn InstSetBase) -> Option<&dyn HasInst<Self>>;
}

impl IrWrite<FuncWriteCtx<'_>> for InstId {
    fn write<W>(&self, w: &mut W, ctx: &FuncWriteCtx) -> io::Result<()>
    where
        W: io::Write,
    {
        let inst = ctx.func.dfg.inst(*self);
        let write: &dyn InstWrite = InstDowncast::downcast(ctx.func.inst_set(), inst).unwrap();
        write.write(w, ctx)
    }
}

/// This trait works as a "proof" that a specific ISA contains `I`,
/// and then allows a construction and reflection of type `I` in that specific
/// ISA context.
pub trait HasInst<I: Inst> {
    fn is(&self, inst: &dyn Inst) -> bool {
        inst.type_id() == TypeId::of::<I>()
    }
}

pub trait InstDowncast<'a>: Sized {
    fn downcast(isb: &dyn InstSetBase, inst: &'a dyn Inst) -> Option<Self>;

    fn map<F, R>(isb: &dyn InstSetBase, inst: &'a dyn Inst, f: F) -> Option<R>
    where
        F: FnOnce(Self) -> R,
    {
        let data = Self::downcast(isb, inst)?;
        Some(f(data))
    }
}

impl<'a, T> InstDowncastMut<'a> for T
where
    T: InstDowncast<'a>,
{
    fn downcast_mut(isb: &dyn InstSetBase, inst: &'a mut dyn Inst) -> Option<Self> {
        InstDowncast::downcast(isb, inst)
    }
}

pub trait InstDowncastMut<'a>: Sized {
    fn downcast_mut(isb: &dyn InstSetBase, inst: &'a mut dyn Inst) -> Option<Self>;

    fn map_mut<F, R>(isb: &dyn InstSetBase, inst: &'a mut dyn Inst, f: F) -> Option<R>
    where
        F: FnOnce(Self) -> R,
    {
        let data = Self::downcast_mut(isb, inst)?;
        Some(f(data))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SideEffect {
    None,
    Read,
    Write,
}

impl SideEffect {
    pub fn has_effect(&self) -> bool {
        !matches!(self, Self::None)
    }
}

#[inst_prop]
trait InstWrite {
    fn write(&self, w: &mut dyn io::Write, ctx: &FuncWriteCtx) -> io::Result<()>;
    type Members = All;
}
