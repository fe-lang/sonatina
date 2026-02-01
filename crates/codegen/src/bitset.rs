use bit_set::BitSet as Bs;
use cranelift_entity::EntityRef;
use std::{fmt, marker::PhantomData};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BitSet<T> {
    bs: Bs,
    marker: PhantomData<T>,
}

impl<T> BitSet<T> {
    pub fn new() -> Self {
        Self {
            bs: Bs::new(),
            marker: PhantomData,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.bs.is_empty()
    }

    pub fn len(&self) -> usize {
        self.bs.len()
    }

    pub fn union_with(&mut self, other: &Self) {
        self.bs.union_with(&other.bs)
    }

    pub fn intersect_with(&mut self, other: &Self) {
        self.bs.intersect_with(&other.bs)
    }

    pub fn difference_with(&mut self, other: &Self) {
        self.bs.difference_with(&other.bs)
    }

    pub fn symmetric_difference_with(&mut self, other: &Self) {
        self.bs.symmetric_difference_with(&other.bs)
    }

    pub fn is_subset(&self, other: &Self) -> bool {
        self.bs.is_subset(&other.bs)
    }

    pub fn is_superset(&self, other: &Self) -> bool {
        self.bs.is_superset(&other.bs)
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.bs.is_disjoint(&other.bs)
    }

    pub fn clear(&mut self) {
        self.bs.clear()
    }
}

impl<T> BitSet<T>
where
    T: EntityRef,
{
    pub fn difference(a: &Self, b: &Self) -> Self {
        let mut d = a.clone();
        d.difference_with(b);
        d
    }

    pub fn insert(&mut self, elem: T) -> bool {
        self.bs.insert(elem.index())
    }
    pub fn remove(&mut self, elem: T) -> bool {
        self.bs.remove(elem.index())
    }
    pub fn contains(&self, elem: T) -> bool {
        self.bs.contains(elem.index())
    }
    pub fn iter(&self) -> impl Iterator<Item = T> + '_ {
        self.bs.iter().map(|v| T::new(v))
    }
}

impl<T> Default for BitSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> fmt::Debug for BitSet<T>
where
    T: EntityRef + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.bs.iter()).finish()
    }
}

impl<T: EntityRef> From<&[T]> for BitSet<T> {
    fn from(elems: &[T]) -> Self {
        let mut bs = BitSet::new();
        for e in elems {
            bs.insert(*e);
        }
        bs
    }
}

impl<T: EntityRef, const N: usize> From<[T; N]> for BitSet<T> {
    fn from(elems: [T; N]) -> Self {
        let mut bs = BitSet::new();
        for e in elems {
            bs.insert(e);
        }
        bs
    }
}

impl<A: EntityRef> FromIterator<A> for BitSet<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A>,
    {
        let mut bs = BitSet::new();
        for e in iter {
            bs.insert(e);
        }
        bs
    }
}
