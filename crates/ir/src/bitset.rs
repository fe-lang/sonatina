use std::{fmt, marker::PhantomData};

use bit_set::BitSet as RawBitSet;
use cranelift_entity::EntityRef;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BitSet<T> {
    bs: RawBitSet,
    marker: PhantomData<T>,
}

impl<T> BitSet<T> {
    pub fn new() -> Self {
        Self {
            bs: RawBitSet::new(),
            marker: PhantomData,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.bs.is_empty()
    }

    pub fn len(&self) -> usize {
        self.bs.len()
    }

    pub fn clear(&mut self) {
        self.bs.clear()
    }

    pub fn union_with(&mut self, other: &Self) {
        self.bs.union_with(&other.bs)
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.bs.is_disjoint(&other.bs)
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
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T> BitSet<T>
where
    T: EntityRef,
{
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
        self.bs.iter().map(T::new)
    }
}

impl<T: EntityRef> FromIterator<T> for BitSet<T> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut bitset = Self::new();
        for elem in iter {
            bitset.insert(elem);
        }
        bitset
    }
}
