use std::{
    collections::BTreeMap,
    ops::Bound::{self, Excluded, Included, Unbounded},
};

use rustc_hash::FxHashMap;
use sonatina_ir::AddressSpaceId;

use crate::analysis::memory_access::{TrackedLocKey, absolute_byte_range};

type Partition = (AddressSpaceId, u32);
type OffsetMap<V> = BTreeMap<i64, FxHashMap<TrackedLocKey, V>>;

/// Absolute locations with checked i64 endpoints, partitioned by space and width.
/// Keep the full keys: equal byte ranges can have different forwarding types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct AbsoluteLocations<V> {
    partitions: FxHashMap<Partition, OffsetMap<V>>,
}

impl<V> Default for AbsoluteLocations<V> {
    fn default() -> Self {
        Self {
            partitions: FxHashMap::default(),
        }
    }
}

pub(super) fn absolute_interval(key: &TrackedLocKey) -> Option<(Partition, i64, i64)> {
    let TrackedLocKey::Linear(key) = key else {
        return None;
    };
    let (start, end) = absolute_byte_range(&key.base, key.offset, i64::from(key.bytes))?;
    Some(((key.space, key.bytes), start, end))
}

impl<V> AbsoluteLocations<V> {
    pub(super) fn get(&self, key: &TrackedLocKey) -> Option<&V> {
        let (partition, start, _) = absolute_interval(key)?;
        self.partitions.get(&partition)?.get(&start)?.get(key)
    }

    pub(super) fn insert(&mut self, key: TrackedLocKey, value: V) {
        let (partition, start, _) =
            absolute_interval(&key).expect("indexed locations must have checked absolute bounds");
        self.partitions
            .entry(partition)
            .or_default()
            .entry(start)
            .or_default()
            .insert(key, value);
    }

    pub(super) fn into_keys(self) -> impl Iterator<Item = TrackedLocKey> {
        self.partitions
            .into_values()
            .flat_map(|offsets| offsets.into_values())
            .flat_map(|bucket| bucket.into_keys())
    }

    pub(super) fn retain(&mut self, mut keep: impl FnMut(&TrackedLocKey, &mut V) -> bool) {
        self.partitions.retain(|_, offsets| {
            offsets.retain(|_, bucket| {
                bucket.retain(|key, value| keep(key, value));
                !bucket.is_empty()
            });
            !offsets.is_empty()
        });
    }

    pub(super) fn candidates(
        &self,
        space: Option<AddressSpaceId>,
        interval: Option<(i64, i64)>,
    ) -> impl Iterator<Item = (&TrackedLocKey, &V)> {
        self.partitions
            .iter()
            .filter(move |((other_space, _), _)| Some(*other_space) == space)
            .flat_map(move |((_, bytes), offsets)| {
                offsets
                    .range(overlap_bounds(interval, *bytes))
                    .flat_map(|(_, bucket)| bucket.iter())
            })
    }

    /// Only candidate locations reach the alias oracle; all other facts survive.
    /// An unrepresentable query interval visits every location in the space.
    pub(super) fn retain_candidates(
        &mut self,
        space: AddressSpaceId,
        interval: Option<(i64, i64)>,
        mut keep: impl FnMut(&TrackedLocKey, &mut V) -> bool,
    ) {
        self.partitions.retain(|(other_space, bytes), offsets| {
            if *other_space != space {
                return true;
            }
            if interval.is_none() {
                // Keep full-space fallback scans linear instead of looking up
                // and removing each tree entry separately.
                offsets.retain(|_, bucket| {
                    bucket.retain(|key, value| keep(key, value));
                    !bucket.is_empty()
                });
                return !offsets.is_empty();
            }
            let candidates: Vec<_> = offsets
                .range(overlap_bounds(interval, *bytes))
                .map(|(&start, _)| start)
                .collect();
            for start in candidates {
                let bucket = offsets.get_mut(&start).expect("candidate must exist");
                bucket.retain(|key, value| keep(key, value));
                if bucket.is_empty() {
                    offsets.remove(&start);
                }
            }
            !offsets.is_empty()
        });
    }
}

fn overlap_bounds(interval: Option<(i64, i64)>, bytes: u32) -> (Bound<i64>, Bound<i64>) {
    let Some((start, end)) = interval else {
        return (Unbounded, Unbounded);
    };
    // [other, other + bytes) overlaps [start, end) only when
    // start - bytes < other < end. Checked storage endpoints cannot wrap.
    let lower = start
        .checked_sub(i64::from(bytes))
        .map_or(Unbounded, Excluded);
    // Equal excluded bounds would panic in BTreeMap::range. Two zero-width
    // intervals cannot overlap, so use a valid empty range instead.
    if start == end && bytes == 0 {
        (Included(end), Excluded(end))
    } else {
        (lower, Excluded(end))
    }
}
