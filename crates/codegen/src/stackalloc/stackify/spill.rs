use crate::bitset::BitSet;
use sonatina_ir::ValueId;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct SpilledValueId {
    value: ValueId,
}

impl SpilledValueId {
    pub(super) fn value(self) -> ValueId {
        self.value
    }
}

/// The values a plan keeps off the stack between their uses, and those of them
/// it keeps in memory. A spilled value whose every use takes a copy still on
/// the stack is never reloaded, so it needs no memory and no store.
#[derive(Clone, Copy, Debug)]
pub(super) struct SpillSet<'a> {
    spill_set: &'a BitSet<ValueId>,
    stored: &'a BitSet<ValueId>,
}

impl<'a> SpillSet<'a> {
    pub(super) fn new(spill_set: &'a BitSet<ValueId>, stored: &'a BitSet<ValueId>) -> Self {
        Self { spill_set, stored }
    }

    pub(super) fn bitset(&self) -> &'a BitSet<ValueId> {
        self.spill_set
    }

    pub(super) fn contains(&self, v: ValueId) -> bool {
        self.spill_set.contains(v)
    }

    /// The spilled values kept in memory.
    pub(super) fn stored_bitset(&self) -> &'a BitSet<ValueId> {
        self.stored
    }

    pub(super) fn stored(&self, v: ValueId) -> Option<SpilledValueId> {
        self.stored
            .contains(v)
            .then_some(SpilledValueId { value: v })
    }
}

pub(super) struct SpillDiscovery<'a> {
    spill: SpillSet<'a>,
    spill_requests: &'a mut BitSet<ValueId>,
    reloaded: &'a mut BitSet<ValueId>,
}

impl<'a> SpillDiscovery<'a> {
    pub(super) fn new(
        spill: SpillSet<'a>,
        spill_requests: &'a mut BitSet<ValueId>,
        reloaded: &'a mut BitSet<ValueId>,
    ) -> Self {
        Self {
            spill,
            spill_requests,
            reloaded,
        }
    }

    pub(super) fn spill_set(&self) -> SpillSet<'a> {
        self.spill
    }

    /// Records a load of `v` from memory, spilling it if it is not spilled yet.
    pub(super) fn reload(&mut self, v: ValueId) {
        self.reloaded.insert(v);
        if !self.spill.contains(v) {
            self.spill_requests.insert(v);
        }
    }

    pub(super) fn requests(&self) -> (&BitSet<ValueId>, &BitSet<ValueId>) {
        (self.spill_requests, self.reloaded)
    }

    pub(super) fn restore_requests(
        &mut self,
        spill_requests: BitSet<ValueId>,
        reloaded: BitSet<ValueId>,
    ) {
        *self.spill_requests = spill_requests;
        *self.reloaded = reloaded;
    }
}
