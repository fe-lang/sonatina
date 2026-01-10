//! This module contains the [`Visitor`]/ [`Visitable`] and
//! [`VisitorMut`]/[`VisitableMut`] traits and its implementations.
//!
//! TODO: This module is not fully completed, we need to add more IR-items to be
//! visited in order to cover the whole sonatina-IR.
use smallvec::{Array, SmallVec};

use crate::{BlockId, Type, ValueId, module::FuncRef};

pub trait Visitable {
    fn accept(&self, visitor: &mut dyn Visitor);

    /// Passes only values in the item to the `f`.
    /// This is useful when you want to iterate over all values in the item
    /// without implementing a `Visitor` trait.
    fn for_each_value(&self, f: &mut dyn FnMut(ValueId)) {
        struct ValueVisitor<'a> {
            f: &'a mut dyn FnMut(ValueId),
        }

        impl Visitor for ValueVisitor<'_> {
            fn visit_value_id(&mut self, item: ValueId) {
                (self.f)(item)
            }
        }

        let mut visitor = ValueVisitor { f };
        self.accept(&mut visitor);
    }
}

pub trait VisitableMut {
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut);

    /// Passes only mutable value references in the item to the `f`.
    /// This is useful when you want to iterate over all values in the item
    /// without implementing a `Visitor` trait.
    fn for_each_value_mut(&mut self, f: &mut dyn FnMut(&mut ValueId)) {
        struct ValueVisitorMut<'a> {
            f: &'a mut dyn FnMut(&mut ValueId),
        }

        impl VisitorMut for ValueVisitorMut<'_> {
            fn visit_value_id(&mut self, item: &mut ValueId) {
                (self.f)(item)
            }
        }

        let mut visitor = ValueVisitorMut { f };
        self.accept_mut(&mut visitor);
    }
}

#[allow(unused_variables)]
pub trait Visitor {
    fn visit_ty(&mut self, item: &Type) {}

    fn visit_value_id(&mut self, item: ValueId) {}

    fn visit_block_id(&mut self, item: BlockId) {}

    fn visit_func_ref(&mut self, item: FuncRef) {}
}

#[allow(unused_variables)]
pub trait VisitorMut {
    fn visit_ty(&mut self, item: &mut Type) {}

    fn visit_value_id(&mut self, item: &mut ValueId) {}

    fn visit_block_id(&mut self, item: &mut BlockId) {}

    fn visit_func_ref(&mut self, item: &mut FuncRef) {}
}

impl Visitable for Type {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_ty(self);
    }
}
impl VisitableMut for Type {
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut) {
        visitor.visit_ty(self);
    }
}

impl Visitable for ValueId {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_value_id(*self)
    }
}
impl VisitableMut for ValueId {
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut) {
        visitor.visit_value_id(self);
    }
}

impl Visitable for BlockId {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_block_id(*self);
    }
}
impl VisitableMut for BlockId {
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut) {
        visitor.visit_block_id(self);
    }
}

impl Visitable for FuncRef {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_func_ref(*self);
    }
}
impl VisitableMut for FuncRef {
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut) {
        visitor.visit_func_ref(self);
    }
}

impl<T> Visitable for Option<T>
where
    T: Visitable,
{
    fn accept(&self, visitor: &mut dyn Visitor) {
        if let Some(item) = self.as_ref() {
            item.accept(visitor);
        }
    }
}
impl<T> VisitableMut for Option<T>
where
    T: VisitableMut,
{
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut) {
        if let Some(item) = self.as_mut() {
            item.accept_mut(visitor);
        }
    }
}

impl<T> Visitable for Vec<T>
where
    T: Visitable,
{
    fn accept(&self, visitor: &mut dyn Visitor) {
        for item in self {
            item.accept(visitor);
        }
    }
}
impl<T> VisitableMut for Vec<T>
where
    T: VisitableMut,
{
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut) {
        for item in self {
            item.accept_mut(visitor);
        }
    }
}

impl<T, const N: usize> Visitable for SmallVec<[T; N]>
where
    T: Visitable,
    [T; N]: Array<Item = T>,
{
    fn accept(&self, visitor: &mut dyn Visitor) {
        for item in self {
            item.accept(visitor);
        }
    }
}
impl<T, const N: usize> VisitableMut for SmallVec<[T; N]>
where
    T: VisitableMut,
    [T; N]: Array<Item = T>,
{
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut) {
        for item in self {
            item.accept_mut(visitor);
        }
    }
}

impl<T, U> Visitable for (T, U)
where
    T: Visitable,
    U: Visitable,
{
    fn accept(&self, visitor: &mut dyn Visitor) {
        self.0.accept(visitor);
        self.1.accept(visitor);
    }
}

impl<T, U> VisitableMut for (T, U)
where
    T: VisitableMut,
    U: VisitableMut,
{
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut) {
        self.0.accept_mut(visitor);
        self.1.accept_mut(visitor);
    }
}
