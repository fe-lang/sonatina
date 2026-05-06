use rustc_hash::FxHashMap;

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

#[derive(Clone, Debug)]
pub(crate) struct ExactPackWorkspace<Idx> {
    placed: Vec<(u32, u32, Idx)>,
    occupied: Vec<(u32, u32)>,
}

impl<Idx> Default for ExactPackWorkspace<Idx> {
    fn default() -> Self {
        Self {
            placed: Vec::new(),
            occupied: Vec::new(),
        }
    }
}

impl<Idx> ExactPackWorkspace<Idx> {
    pub(crate) fn with_capacity(item_count: usize) -> Self {
        Self {
            placed: Vec::with_capacity(item_count),
            occupied: Vec::with_capacity(item_count),
        }
    }
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
            &occupied_ranges(
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

pub(crate) fn pack_exact_with_offsets_by<Idx>(
    items: &[ExactPackItem<Idx>],
    mut conflicts: impl FnMut(Idx, Idx) -> bool,
    workspace: &mut ExactPackWorkspace<Idx>,
) -> ExactPackResult
where
    Idx: Copy,
{
    workspace.placed.clear();
    let mut offsets = FxHashMap::with_capacity_and_hasher(items.len(), Default::default());
    let mut max_used = 0u32;

    for item in items {
        if item.size_words == 0 {
            offsets.insert(item.id, 0);
            continue;
        }

        let off = first_fit_above(
            item.min_offset_words,
            item.size_words,
            occupied_ranges_for_item(
                item.idx,
                &workspace.placed,
                &mut conflicts,
                &mut workspace.occupied,
            ),
        );
        offsets.insert(item.id, off);
        let end = off
            .checked_add(item.size_words)
            .expect("locals size overflow");
        max_used = max_used.max(end);
        workspace.placed.push((off, end, item.idx));
    }

    ExactPackResult { offsets, max_used }
}

pub(crate) fn pack_exact_peak_by<Idx>(
    items: &[ExactPackItem<Idx>],
    mut conflicts: impl FnMut(Idx, Idx) -> bool,
    workspace: &mut ExactPackWorkspace<Idx>,
) -> u32
where
    Idx: Copy,
{
    workspace.placed.clear();
    let mut max_used = 0u32;

    for item in items {
        if item.size_words == 0 {
            continue;
        }

        let off = first_fit_above(
            item.min_offset_words,
            item.size_words,
            occupied_ranges_for_item(
                item.idx,
                &workspace.placed,
                &mut conflicts,
                &mut workspace.occupied,
            ),
        );
        let end = off
            .checked_add(item.size_words)
            .expect("locals size overflow");
        max_used = max_used.max(end);
        workspace.placed.push((off, end, item.idx));
    }

    max_used
}

fn occupied_ranges_for_item<'a, Idx>(
    item_idx: Idx,
    placed: &[(u32, u32, Idx)],
    conflicts: &mut impl FnMut(Idx, Idx) -> bool,
    occupied: &'a mut Vec<(u32, u32)>,
) -> &'a [(u32, u32)]
where
    Idx: Copy,
{
    occupied.clear();
    occupied.extend(placed.iter().filter_map(|(off, end, placed_idx)| {
        conflicts(item_idx, *placed_idx).then_some((*off, *end))
    }));
    merge_occupied_ranges(occupied);
    occupied
}

fn occupied_ranges(occupied: impl Iterator<Item = (u32, u32)>) -> Vec<(u32, u32)> {
    let mut occupied: Vec<_> = occupied.collect();
    merge_occupied_ranges(&mut occupied);
    occupied
}

fn merge_occupied_ranges(occupied: &mut Vec<(u32, u32)>) {
    if occupied.is_empty() {
        return;
    }
    occupied.sort_unstable();
    let mut write_idx = 0usize;
    for read_idx in 1..occupied.len() {
        let (start, end) = occupied[read_idx];
        if start <= occupied[write_idx].1 {
            occupied[write_idx].1 = occupied[write_idx].1.max(end);
        } else {
            write_idx += 1;
            occupied[write_idx] = (start, end);
        }
    }
    occupied.truncate(write_idx + 1);
}

fn first_fit_above(min_offset_words: u32, size_words: u32, occupied: &[(u32, u32)]) -> u32 {
    let mut cursor = min_offset_words;
    for &(start, end) in occupied {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitset::BitSet;
    use cranelift_entity::EntityRef;

    #[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
    struct TestIdx(u32);
    cranelift_entity::entity_impl!(TestIdx);

    fn item(idx: u32, size_words: u32, min_offset_words: u32) -> ExactPackItem<TestIdx> {
        ExactPackItem {
            id: StackObjId::new(idx as usize + 1),
            idx: TestIdx::new(idx as usize),
            size_words,
            min_offset_words,
        }
    }

    #[test]
    fn exact_peak_by_matches_bitset_peak_without_offsets() {
        let items = vec![item(0, 3, 0), item(1, 2, 1), item(2, 1, 5)];
        let mut conflicts = vec![BitSet::default(); 3];
        let _ = conflicts[0].insert(TestIdx::new(1));
        let _ = conflicts[1].insert(TestIdx::new(0));

        let mut workspace = ExactPackWorkspace::default();
        let peak = pack_exact_peak_by(
            &items,
            |lhs, rhs| conflicts[lhs.index()].contains(rhs),
            &mut workspace,
        );

        let mut offset_workspace = ExactPackWorkspace::default();
        let packed = pack_exact_with_offsets_by(
            &items,
            |lhs, rhs| conflicts[lhs.index()].contains(rhs),
            &mut offset_workspace,
        );
        assert_eq!(peak, packed.max_used);
    }
}
