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

use macros::inst_prop;
use rustc_hash::FxHashSet;
use smallvec::SmallVec;

use crate::{
    ir_writer::{FuncWriteCtx, WriteWithFunc},
    InstSetBase, ValueId,
};

/// An opaque reference to dynamic [`Inst`].
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Copy, Hash)]
pub struct InstId(pub u32);
cranelift_entity::entity_impl!(InstId);

pub trait Inst: inst_set::sealed::Registered + Any {
    fn visit_values(&self, f: &mut dyn FnMut(ValueId));
    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut ValueId));
    fn has_side_effect(&self) -> bool;
    fn as_text(&self) -> &'static str;
    fn is_terminator(&self) -> bool;

    fn collect_values(&self) -> Vec<ValueId> {
        let mut vs = Vec::new();

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

impl WriteWithFunc for InstId {
    fn write(&self, ctx: &FuncWriteCtx, w: &mut impl io::Write) -> io::Result<()> {
        let inst = ctx.func.dfg.inst(*self);
        let write: &dyn InstWrite = InstDowncast::downcast(ctx.func.inst_set(), inst).unwrap();
        write.write(ctx, w)
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

pub trait InstDowncast: Sized {
    fn downcast(isb: &dyn InstSetBase, inst: &dyn Inst) -> Option<Self>;

    fn map<F, R>(isb: &dyn InstSetBase, inst: &dyn Inst, f: F) -> Option<R>
    where
        F: FnOnce(Self) -> R,
    {
        let data = Self::downcast(isb, inst)?;
        Some(f(data))
    }
}

impl<T> InstDowncastMut for T
where
    T: InstDowncast,
{
    fn downcast_mut(isb: &dyn InstSetBase, inst: &mut dyn Inst) -> Option<Self> {
        InstDowncast::downcast(isb, inst)
    }
}

pub trait InstDowncastMut: Sized {
    fn downcast_mut(isb: &dyn InstSetBase, inst: &mut dyn Inst) -> Option<Self>;

    fn map_mut<F, R>(isb: &dyn InstSetBase, inst: &mut dyn Inst, f: F) -> Option<R>
    where
        F: FnOnce(Self) -> R,
    {
        let data = Self::downcast_mut(isb, inst)?;
        Some(f(data))
    }
}

#[inst_prop]
trait InstWrite {
    fn write(&self, ctx: &FuncWriteCtx, w: &mut dyn io::Write) -> io::Result<()>;
    type Members = All;
}

macro_rules! impl_inst_write {
    ($ty:ty) => {
        impl $crate::inst::InstWrite for $ty {
            fn write(
                &self,
                ctx: &crate::ir_writer::FuncWriteCtx,
                mut w: &mut dyn std::io::Write,
            ) -> std::io::Result<()> {
                w.write_fmt(format_args!("{} ", crate::Inst::as_text(self)))?;
                let values = crate::Inst::collect_values(self);
                let mut values = values.iter();

                if let Some(value) = values.next() {
                    $crate::ir_writer::WriteWithFunc::write(value, ctx, &mut w)?
                }
                for value in values {
                    write!(w, " ")?;
                    $crate::ir_writer::WriteWithFunc::write(value, ctx, &mut w)?
                }
                Ok(())
            }
        }
    };

    ($ty:ty, ($($field:ident: $kind:ident),+)) => {
        impl $crate::inst::InstWrite for $ty {
            fn write(
                &self,
                ctx: &crate::ir_writer::FuncWriteCtx,
                mut w: &mut dyn std::io::Write,
            ) -> std::io::Result<()> {
                w.write_fmt(format_args!("{} ", crate::Inst::as_text(self)))?;
                $crate::inst::__write_args!(self, ctx, &mut w, ($($field: $kind),+));
                Ok(())
            }
        }
    };
}

macro_rules! __write_args {
    ($self:expr, $ctx:expr, $w:expr, ($field:ident: $kind:ident $(,$fields:ident: $kinds:ident)+)) => {
        $crate::inst::__write_args!($self, $ctx, $w, ($field: $kind));
        write!(&mut $w, " ")?;
        $crate::inst::__write_args!($self, $ctx, $w, ($($fields: $kinds),+));
    };

    ($self:expr, $ctx:expr, $w:expr, ($field:ident: Type)) => {
        $crate::ir_writer::WriteWithModule::write($self.$field(), $ctx.func.ctx(), $w)?
    };

    ($self:expr, $ctx:expr, $w:expr, ($field:ident: ValueId)) => {
        $crate::ir_writer::WriteWithFunc::write($self.$field(), $ctx, $w)?
    };
}

use __write_args;
use impl_inst_write;
