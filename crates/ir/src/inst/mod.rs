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
use rustc_hash::FxHashSet;
use smallvec::SmallVec;

use crate::{
    ir_writer::{FuncWriteCtx, IrWrite},
    InstSetBase, ValueId,
};

/// An opaque reference to dynamic [`Inst`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct InstId(pub u32);
cranelift_entity::entity_impl!(InstId);

pub trait Inst: inst_set::sealed::Registered + DynClone + Any + Send + Sync {
    fn visit_values(&self, f: &mut dyn FnMut(ValueId));
    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut ValueId));
    fn side_effect(&self) -> SideEffect;
    fn as_text(&self) -> &'static str;
    fn is_terminator(&self) -> bool;

    fn collect_values(&self) -> SmallVec<[ValueId; 2]> {
        let mut vs = SmallVec::new();

        self.visit_values(&mut |v| vs.push(v));
        vs
    }

    fn collect_value_set(&self) -> FxHashSet<ValueId> {
        let mut vs = FxHashSet::default();

        self.visit_values(&mut |v| {
            vs.insert(v);
        });
        vs
    }
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

pub(crate) trait ValueVisitable {
    fn visit_with(&self, f: &mut dyn FnMut(ValueId));
    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut ValueId));
}

impl ValueVisitable for ValueId {
    fn visit_with(&self, f: &mut dyn FnMut(ValueId)) {
        f(*self)
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut ValueId)) {
        f(self)
    }
}

impl<V> ValueVisitable for Option<V>
where
    V: ValueVisitable,
{
    fn visit_with(&self, f: &mut dyn FnMut(ValueId)) {
        if let Some(value) = self {
            value.visit_with(f)
        }
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut ValueId)) {
        if let Some(value) = self.as_mut() {
            value.visit_mut_with(f)
        }
    }
}

impl<V, T> ValueVisitable for (V, T)
where
    V: ValueVisitable,
{
    fn visit_with(&self, f: &mut dyn FnMut(ValueId)) {
        self.0.visit_with(f)
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut ValueId)) {
        self.0.visit_mut_with(f)
    }
}

impl<V> ValueVisitable for Vec<V>
where
    V: ValueVisitable,
{
    fn visit_with(&self, f: &mut dyn FnMut(ValueId)) {
        self.iter().for_each(|v| v.visit_with(f))
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut ValueId)) {
        self.iter_mut().for_each(|v| v.visit_mut_with(f))
    }
}

impl<V> ValueVisitable for [V]
where
    V: ValueVisitable,
{
    fn visit_with(&self, f: &mut dyn FnMut(ValueId)) {
        self.iter().for_each(|v| v.visit_with(f))
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut ValueId)) {
        self.iter_mut().for_each(|v| v.visit_mut_with(f))
    }
}

impl<V, const N: usize> ValueVisitable for SmallVec<[V; N]>
where
    V: ValueVisitable,
    [V; N]: smallvec::Array<Item = V>,
{
    fn visit_with(&self, f: &mut dyn FnMut(ValueId)) {
        self.iter().for_each(|v| v.visit_with(f))
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut ValueId)) {
        self.iter_mut().for_each(|v| v.visit_mut_with(f))
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
