use cranelift_entity::EntityRef;
use rustc_hash::FxHashMap;
use std::hash::Hash;

use crate::bitset::BitSet;

use super::{LiveRegion, StackObjId};

#[derive(Clone, Debug)]
pub(crate) struct PackedObject {
    pub(crate) id: StackObjId,
    pub(crate) size_words: u32,
    pub(crate) region: LiveRegion,
    pub(crate) min_offset_words: u32,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ExactPackItem<Idx> {
    pub(crate) id: StackObjId,
    pub(crate) idx: Idx,
    pub(crate) size_words: u32,
    pub(crate) min_offset_words: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExactPackResult {
    pub(crate) offsets: FxHashMap<StackObjId, u32>,
    pub(crate) max_used: u32,
}

pub(crate) fn pack_objects_presorted(
    objects: &[PackedObject],
) -> (FxHashMap<StackObjId, u32>, u32) {
    let mut offsets = FxHashMap::with_capacity_and_hasher(objects.len(), Default::default());
    let mut placed: Vec<(u32, u32, &PackedObject)> = Vec::with_capacity(objects.len());
    let mut max_used = 0u32;

    for object in objects {
        if object.size_words == 0 {
            offsets.insert(object.id, 0);
            continue;
        }

        let off = first_fit_above(
            object.min_offset_words,
            object.size_words,
            occupied_ranges(
                placed
                    .iter()
                    .filter(|(_, _, placed_object)| placed_object.region.overlaps(&object.region))
                    .map(|(off, end, _)| (*off, *end)),
            ),
        );
        offsets.insert(object.id, off);
        max_used = max_used.max(
            off.checked_add(object.size_words)
                .expect("locals size overflow"),
        );
        placed.push((
            off,
            off.checked_add(object.size_words)
                .expect("locals size overflow"),
            object,
        ));
    }

    (offsets, max_used)
}

pub(crate) fn pack_exact_with_offsets<Idx>(
    items: &[ExactPackItem<Idx>],
    conflicts: &[BitSet<Idx>],
) -> ExactPackResult
where
    Idx: EntityRef + Copy + Eq + Hash,
{
    let mut offsets = FxHashMap::with_capacity_and_hasher(items.len(), Default::default());
    let mut placed: Vec<(u32, u32, Idx, u32)> = Vec::with_capacity(items.len());
    let mut max_used = 0u32;

    for item in items {
        if item.size_words == 0 {
            offsets.insert(item.id, 0);
            continue;
        }

        let off = first_fit_above(
            item.min_offset_words,
            item.size_words,
            occupied_ranges(placed.iter().filter_map(|(off, end, placed_idx, _)| {
                conflicts[item.idx.index()]
                    .contains(*placed_idx)
                    .then_some((*off, *end))
            })),
        );
        offsets.insert(item.id, off);
        max_used = max_used.max(
            off.checked_add(item.size_words)
                .expect("locals size overflow"),
        );
        placed.push((
            off,
            off.checked_add(item.size_words)
                .expect("locals size overflow"),
            item.idx,
            item.size_words,
        ));
    }

    ExactPackResult { offsets, max_used }
}

pub(crate) fn pack_exact_peak<Idx>(items: &[ExactPackItem<Idx>], conflicts: &[BitSet<Idx>]) -> u32
where
    Idx: EntityRef + Copy + Eq + Hash,
{
    pack_exact_with_offsets(items, conflicts).max_used
}

fn occupied_ranges(occupied: impl Iterator<Item = (u32, u32)>) -> Vec<(u32, u32)> {
    let mut occupied: Vec<_> = occupied.collect();
    occupied.sort_unstable();
    let mut merged = Vec::with_capacity(occupied.len());
    for (start, end) in occupied {
        if let Some((_, merged_end)) = merged.last_mut()
            && start <= *merged_end
        {
            *merged_end = (*merged_end).max(end);
        } else {
            merged.push((start, end));
        }
    }
    merged
}

fn first_fit_above(min_offset_words: u32, size_words: u32, occupied: Vec<(u32, u32)>) -> u32 {
    let mut cursor = min_offset_words;
    for (start, end) in occupied {
        if end <= cursor {
            continue;
        }
        if cursor
            .checked_add(size_words)
            .is_some_and(|candidate_end| candidate_end <= start)
        {
            return cursor;
        }
        cursor = cursor.max(end);
    }
    cursor
}
