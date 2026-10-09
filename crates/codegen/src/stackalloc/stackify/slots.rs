use cranelift_entity::{SecondaryMap, entity_impl};
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, ValueId, cfg::ControlFlowGraph};
use std::collections::BTreeSet;

use crate::{
    bitset::BitSet,
    liveness::{Liveness, phi_args_for_edge},
};

use super::spill::SpilledValueId;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct PhiEdgePoint(u32);
entity_impl!(PhiEdgePoint);

#[derive(Default, Clone)]
struct SpillSlotLiveRange {
    blocks: BitSet<BlockId>,
    phi_edges: BitSet<PhiEdgePoint>,
}

impl SpillSlotLiveRange {
    fn union_with(&mut self, other: &Self) {
        self.blocks.union_with(&other.blocks);
        self.phi_edges.union_with(&other.phi_edges);
    }

    fn is_disjoint(&self, other: &Self) -> bool {
        self.blocks.is_disjoint(&other.blocks) && self.phi_edges.is_disjoint(&other.phi_edges)
    }
}

#[derive(Default, Clone)]
pub(super) struct SpillSlotInterference {
    ranges: SecondaryMap<ValueId, SpillSlotLiveRange>,
}

impl SpillSlotInterference {
    pub(super) fn compute(
        func: &Function,
        cfg: &ControlFlowGraph,
        liveness: &Liveness,
        phi_results: &SecondaryMap<BlockId, SmallVec<[ValueId; 4]>>,
        value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
    ) -> Self {
        let mut interference = Self::default();
        for value in func.dfg.value_ids() {
            let value = value_aliases[value].unwrap_or(value);
            interference.ranges[value]
                .blocks
                .union_with(&liveness.val_live_blocks[value]);
        }

        let mut edge_idx = 0u32;
        for pred in func.layout.iter_block() {
            for &succ in cfg.succs_of(pred) {
                if phi_results[succ].is_empty() {
                    continue;
                }

                let edge = PhiEdgePoint(edge_idx);
                edge_idx = edge_idx
                    .checked_add(1)
                    .expect("phi edge interference index overflow");

                for source in phi_args_for_edge(func, pred, succ) {
                    let source = value_aliases[source].unwrap_or(source);
                    if !func.dfg.value_is_imm(source) {
                        interference.ranges[source].phi_edges.insert(edge);
                    }
                }

                for &result in &phi_results[succ] {
                    let result = value_aliases[result].unwrap_or(result);
                    if !func.dfg.value_is_imm(result) {
                        interference.ranges[result].phi_edges.insert(edge);
                    }
                }
            }
        }

        interference
    }

    fn range(&self, value: ValueId) -> &SpillSlotLiveRange {
        &self.ranges[value]
    }
}

#[derive(Default, Clone)]
pub(super) struct SlotPool {
    slot_of: SecondaryMap<ValueId, Option<u32>>,
    next_slot: u32,
    slot_live_ranges: Vec<SpillSlotLiveRange>,
}

impl SlotPool {
    pub(super) fn take_slot_map(&mut self) -> SecondaryMap<ValueId, Option<u32>> {
        std::mem::take(&mut self.slot_of)
    }

    pub(super) fn slot_for(&self, v: ValueId) -> Option<u32> {
        self.slot_of[v]
    }

    pub(super) fn try_ensure_slot(
        &mut self,
        v: SpilledValueId,
        interference: &SpillSlotInterference,
        free_slots: &mut FreeSlots,
        max_slots: Option<u32>,
    ) -> Option<u32> {
        let v = v.value();
        if let Some(slot) = self.slot_of[v] {
            return Some(slot);
        }

        // Prefer reusing a slot freed earlier in this block, whose last value is dead from here on.
        // Only a value confined to this block may reuse it unchecked: a value that outlives the
        // block can meet the slot's other values elsewhere, or the dead value's next instance,
        // which this block's outgoing edges store to the slot when it is a successor's phi.
        let range = interference.range(v);
        let confined = range.blocks.len() <= 1 && range.phi_edges.is_empty();
        let slot = if confined && let Some(slot) = free_slots.take_released() {
            slot
        } else {
            let mut found: Option<u32> = None;
            for candidate in 0..self.next_slot {
                let idx = candidate as usize;
                debug_assert!(
                    idx < self.slot_live_ranges.len(),
                    "slot_live_ranges out of sync: candidate={candidate} len={}",
                    self.slot_live_ranges.len()
                );
                if self.slot_live_ranges[idx].is_disjoint(range) {
                    found = Some(candidate);
                    break;
                }
            }
            if let Some(slot) = found {
                slot
            } else {
                let can_grow = max_slots.is_none_or(|max| self.next_slot < max);
                if !can_grow {
                    return None;
                }

                let slot = self.next_slot;
                self.next_slot = self
                    .next_slot
                    .checked_add(1)
                    .expect("frame slot index overflow");
                self.slot_live_ranges.push(SpillSlotLiveRange::default());
                slot
            }
        };

        self.slot_of[v] = Some(slot);

        // Track the live range union for this slot to support cross-path reuse checks.
        let idx = slot as usize;
        debug_assert!(
            idx < self.slot_live_ranges.len(),
            "slot_live_ranges missing slot"
        );
        self.slot_live_ranges[idx].union_with(range);
        Some(slot)
    }

    pub(super) fn release_if_assigned(&self, v: ValueId, free_slots: &mut FreeSlots) {
        if let Some(slot) = self.slot_of[v] {
            free_slots.release(slot);
        }
    }
}

#[derive(Default, Clone)]
pub(super) struct FreeSlotPools {
    pub(super) scratch: FreeSlots,
}

#[derive(Default, Clone)]
pub(super) struct SpillSlotPools {
    pub(super) scratch: SlotPool,
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

#[cfg(test)]
mod tests {
    use super::{super::spill::SpillSet, *};
    use cranelift_entity::EntityRef;

    #[test]
    fn released_slot_is_reused_only_by_values_confined_to_the_block() {
        // `dead` is a loop header phi whose last use is in the latch. The latch's backedge stores
        // its next instance, so its slot is released in the latch but written again at the end.
        let (header, latch) = (BlockId::new(0), BlockId::new(1));
        let backedge = PhiEdgePoint(0);
        let [dead, live_out, phi_source, local] = [0, 1, 2, 3].map(ValueId::new);

        let mut interference = SpillSlotInterference::default();
        interference.ranges[dead].blocks = [header, latch].into_iter().collect();
        interference.ranges[dead].phi_edges.insert(backedge);
        interference.ranges[live_out].blocks = [latch, header].into_iter().collect();
        interference.ranges[phi_source].blocks.insert(latch);
        interference.ranges[phi_source].phi_edges.insert(backedge);
        interference.ranges[local].blocks.insert(latch);

        let spill_set: BitSet<ValueId> = [dead, live_out, phi_source, local].into_iter().collect();
        let spilled = |v| {
            SpillSet::new(&spill_set)
                .spilled(v)
                .expect("value is spilled")
        };
        let mut pool = SlotPool::default();
        let mut free_slots = FreeSlots::default();
        let mut slot_for = |v, free_slots: &mut FreeSlots| {
            pool.try_ensure_slot(spilled(v), &interference, free_slots, None)
        };

        assert_eq!(slot_for(dead, &mut free_slots), Some(0));
        free_slots.release(0);
        // Values that outlive the latch overlap `dead`, so they need fresh slots.
        assert_eq!(slot_for(live_out, &mut free_slots), Some(1));
        assert_eq!(slot_for(phi_source, &mut free_slots), Some(2));
        assert_eq!(slot_for(local, &mut free_slots), Some(0));
    }
}
