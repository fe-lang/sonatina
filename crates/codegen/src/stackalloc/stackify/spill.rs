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

#[derive(Clone, Copy, Debug)]
pub(super) struct SpillSet<'a> {
    spill_set: &'a BitSet<ValueId>,
}

impl<'a> SpillSet<'a> {
    pub(super) fn new(spill_set: &'a BitSet<ValueId>) -> Self {
        Self { spill_set }
    }

    pub(super) fn bitset(&self) -> &'a BitSet<ValueId> {
        self.spill_set
    }

    pub(super) fn contains(&self, v: ValueId) -> bool {
        self.spill_set.contains(v)
    }

    pub(super) fn spilled(&self, v: ValueId) -> Option<SpilledValueId> {
        self.contains(v).then_some(SpilledValueId { value: v })
    }
}

pub(super) struct SpillDiscovery<'a> {
    spill: SpillSet<'a>,
    spill_requests: &'a mut BitSet<ValueId>,
}

impl<'a> SpillDiscovery<'a> {
    pub(super) fn new(spill: SpillSet<'a>, spill_requests: &'a mut BitSet<ValueId>) -> Self {
        Self {
            spill,
            spill_requests,
        }
    }

    pub(super) fn spill_set(&self) -> SpillSet<'a> {
        self.spill
    }

    pub(super) fn spilled(&self, v: ValueId) -> Option<SpilledValueId> {
        self.spill.spilled(v)
    }

    pub(super) fn request_spill(&mut self, v: ValueId) -> bool {
        self.spill_requests.insert(v)
    }

    pub(super) fn spill_requests(&self) -> &BitSet<ValueId> {
        &*self.spill_requests
    }
}
