use cranelift_entity::SecondaryMap;
use sonatina_ir::{BlockId, ValueId};
use std::collections::BTreeSet;

use crate::{bitset::BitSet, liveness::Liveness};

use super::spill::SpilledValueId;

#[derive(Default, Clone)]
pub(super) struct SlotState {
    slot_of: SecondaryMap<ValueId, Option<u32>>,
    next_slot: u32,
    slot_live_blocks: Vec<BitSet<BlockId>>,
}

impl SlotState {
    pub(super) fn frame_size_slots(&self) -> u32 {
        self.next_slot
    }

    pub(super) fn snapshot_slot_map(&self) -> &SecondaryMap<ValueId, Option<u32>> {
        &self.slot_of
    }

    pub(super) fn take_slot_map(&mut self) -> SecondaryMap<ValueId, Option<u32>> {
        std::mem::take(&mut self.slot_of)
    }

    /// Return the frame slot for `v`, allocating one if needed.
    ///
    /// Allocation is deterministic: we reuse the lowest-numbered currently-free slot, falling back
    /// to `next_slot` growth. In addition to within-block reuse, we also allow cross-block reuse
    /// when liveness indicates two values' live block sets are disjoint (see
    /// `Liveness::val_live_blocks`).
    pub(super) fn ensure_slot(
        &mut self,
        v: SpilledValueId,
        liveness: &Liveness,
        free_slots: &mut FreeSlots,
    ) -> u32 {
        let v = v.value();
        if let Some(slot) = self.slot_of[v] {
            return slot;
        }

        // Prefer reusing a slot that has been freed within this block (exact last-use tracking).
        let slot = if let Some(slot) = free_slots.take_released() {
            slot
        } else {
            let live_blocks = &liveness.val_live_blocks[v];
            let mut found: Option<u32> = None;
            for candidate in 0..self.next_slot {
                let idx = candidate as usize;
                debug_assert!(
                    idx < self.slot_live_blocks.len(),
                    "slot_live_blocks out of sync: candidate={candidate} len={}",
                    self.slot_live_blocks.len()
                );
                if self.slot_live_blocks[idx].is_disjoint(live_blocks) {
                    found = Some(candidate);
                    break;
                }
            }
            if let Some(slot) = found {
                slot
            } else {
                let slot = self.next_slot;
                self.next_slot = self
                    .next_slot
                    .checked_add(1)
                    .expect("frame slot index overflow");
                self.slot_live_blocks.push(BitSet::default());
                slot
            }
        };

        self.slot_of[v] = Some(slot);

        // Track the live-block union for this slot to support cross-block reuse checks.
        let idx = slot as usize;
        debug_assert!(
            idx < self.slot_live_blocks.len(),
            "slot_live_blocks missing slot"
        );
        self.slot_live_blocks[idx].union_with(&liveness.val_live_blocks[v]);
        slot
    }

    pub(super) fn slot_of_value(&self, v: ValueId) -> Option<u32> {
        self.snapshot_slot_map()[v]
    }

    pub(super) fn release_if_assigned(&self, v: ValueId, free_slots: &mut FreeSlots) {
        if let Some(slot) = self.slot_of_value(v) {
            free_slots.release(slot);
        }
    }
}

/// Per-block free list for frame slots.
///
/// A slot becomes available once the last use of the associated value occurs within the block and
/// the value is not live-out. New `spill_set` values do not allocate slots in discarded
/// fixed-point iterations; their slot is assigned at their definition once they become part of
/// `spill_set`.
#[derive(Default, Clone)]
pub(super) struct FreeSlots {
    slots: BTreeSet<u32>,
}

impl FreeSlots {
    pub(super) fn release(&mut self, slot: u32) {
        self.slots.insert(slot);
    }

    pub(super) fn take_released(&mut self) -> Option<u32> {
        if let Some(&slot) = self.slots.iter().next() {
            self.slots.remove(&slot);
            return Some(slot);
        }
        None
    }
}
