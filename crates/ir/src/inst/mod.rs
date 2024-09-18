pub mod arith;
pub mod cast;
pub mod cmp;
pub mod control_flow;
pub mod data;
pub mod evm;
pub mod inst_set;
pub mod logic;

use std::any::{Any, TypeId};

use smallvec::SmallVec;

use crate::{value_::ValueId, InstSetBase};

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
}

/// This trait works as a "proof" that a specific ISA contains `I`,
/// and then allows a construction and reflection of type `I` in that specific ISA context.
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
