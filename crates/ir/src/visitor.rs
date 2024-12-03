//! This module contains the [`Visitor`]/ [`Visitable`] and
//! [`VisitorMut`]/[`VisitableMut`] traits and its implementations.
//!
//! TODO: This module is not fully completed, we need to add more IR-items to be
//! visited in order to cover the whole sonatina-IR.
use smallvec::{Array, SmallVec};

use crate::{module::FuncRef, BlockId, Type, ValueId};

pub trait Visitable {
    fn accept(&self, visitor: &mut dyn Visitor);
}

#[allow(unused_variables)]
pub trait Visitor {
    fn visit_ty(&mut self, item: &Type) {}

    fn visit_value_id(&mut self, item: ValueId) {}

    fn visit_block_id(&mut self, item: BlockId) {}

    fn visit_func_ref(&mut self, item: FuncRef) {}
}

pub trait VisitableMut {
    fn accept_mut(&mut self, visitor: &mut dyn VisitorMut);
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
