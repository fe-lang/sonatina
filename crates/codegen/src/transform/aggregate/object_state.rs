use std::{mem, ops::Range};

use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use sonatina_ir::{ValueId, inst::data, module::ModuleCtx};

use super::object_tracking::{ObjectSlice, enum_tag_object_slice, enum_variant_field_object_slice};

/// Exact demand in root-relative coordinates. Sorted, nonempty intervals never
/// overlap or touch, so equality is independent of insertion/predecessor order.
/// Endpoints come only from IR accesses and root extents: space and transfer work
/// depend on those boundaries, never on the number of leaves in a large array.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct LiveLeaves {
    ranges: SmallVec<[Range<usize>; 2]>,
}

impl LiveLeaves {
    pub(crate) fn ranges(&self) -> &[Range<usize>] {
        &self.ranges
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.ranges.is_empty()
    }

    fn insert(&mut self, mut range: Range<usize>) {
        if range.is_empty() {
            return;
        }
        let first = self.ranges.partition_point(|old| old.end < range.start);
        let end = self.ranges.partition_point(|old| old.start <= range.end);
        if first == end {
            self.ranges.insert(first, range);
        } else {
            range.start = range.start.min(self.ranges[first].start);
            range.end = range.end.max(self.ranges[end - 1].end);
            self.ranges[first] = range;
            self.ranges.drain(first + 1..end);
        }
    }

    pub(crate) fn remove(&mut self, range: Range<usize>) {
        if range.is_empty() {
            return;
        }
        let first = self.ranges.partition_point(|old| old.end <= range.start);
        let end = self.ranges.partition_point(|old| old.start < range.end);
        if first == end {
            return;
        }
        let start_leaf = self.ranges[first].start;
        let end_leaf = self.ranges[end - 1].end;
        self.ranges.drain(first..end);
        if end_leaf > range.end {
            self.ranges.insert(first, range.end..end_leaf);
        }
        if start_leaf < range.start {
            self.ranges.insert(first, start_leaf..range.start);
        }
    }

    fn overlaps(&self, range: Range<usize>) -> bool {
        !range.is_empty()
            && self
                .ranges
                .get(self.ranges.partition_point(|old| old.end <= range.start))
                .is_some_and(|old| old.start < range.end)
    }

    fn union_with(&mut self, other: &Self) {
        let previous = mem::take(&mut self.ranges);
        let mut left = previous.into_iter().peekable();
        let mut right = other.ranges.iter().cloned().peekable();
        while let Some(range) = match (left.peek(), right.peek()) {
            (Some(a), Some(b)) if a.start <= b.start => left.next(),
            (Some(_), Some(_)) | (None, Some(_)) => right.next(),
            (Some(_), None) => left.next(),
            (None, None) => None,
        } {
            if let Some(last) = self.ranges.last_mut()
                && range.start <= last.end
            {
                last.end = last.end.max(range.end);
            } else {
                self.ranges.push(range);
            }
        }
    }
}

pub(crate) type LiveLeafMap = FxHashMap<ValueId, LiveLeaves>;
pub(crate) type ObjectSliceList = SmallVec<[ObjectSlice; 4]>;
pub(crate) fn union_live_leaf_maps(states: impl Iterator<Item = LiveLeafMap>) -> LiveLeafMap {
    let mut out = LiveLeafMap::default();
    for state in states {
        for (root, leaves) in state {
            out.entry(root).or_default().union_with(&leaves);
        }
    }
    out
}

pub(crate) fn mark_root_live(live: &mut LiveLeafMap, root: ValueId, total_leaves: usize) {
    if total_leaves != 0 {
        live.entry(root).or_default().insert(0..total_leaves);
    }
}

pub(crate) fn mark_live_slice(live: &mut LiveLeafMap, slice: ObjectSlice) {
    if slice.leaf_count != 0 {
        live.entry(slice.root)
            .or_default()
            .insert(slice.first_leaf..slice.first_leaf + slice.leaf_count);
    }
}

pub(crate) fn slice_has_live_leaf(live: &LiveLeafMap, slice: ObjectSlice) -> bool {
    live.get(&slice.root)
        .is_some_and(|entry| entry.overlaps(slice.first_leaf..slice.first_leaf + slice.leaf_count))
}

pub(crate) fn enum_write_variant_slices(
    ctx: &ModuleCtx,
    base_slice: ObjectSlice,
    enum_write_variant: &data::EnumWriteVariant,
) -> ObjectSliceList {
    let mut slices = ObjectSliceList::new();
    if let Some(tag_slice) = enum_tag_object_slice(ctx, base_slice) {
        slices.push(tag_slice);
    }
    for field_idx in 0..enum_write_variant.values().len() {
        let Some(field_idx) = u32::try_from(field_idx).ok() else {
            continue;
        };
        if let Some(field_slice) = enum_variant_field_object_slice(
            ctx,
            base_slice,
            *enum_write_variant.variant(),
            field_idx,
        ) {
            slices.push(field_slice);
        }
    }
    slices
}

#[cfg(test)]
mod tests {
    use std::slice;

    use super::*;
    use crate::transform::aggregate::{
        object_access::ObjectAccessFacts,
        object_tracking::{collect_root_slices, objref_element_ty},
        provenance::collect_root_provenance,
        shape,
    };
    use sonatina_ir::{inst::downcast, module::FuncRef};
    use sonatina_parser::parse_module;

    fn parse_test_module(src: &str) -> sonatina_ir::Module {
        parse_module(src).expect("parse should succeed").module
    }

    fn lookup_func(module: &sonatina_ir::Module, name: &str) -> FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .expect("function should exist")
    }

    fn leaves_from_mask(mask: u8) -> LiveLeaves {
        let mut leaves = LiveLeaves::default();
        for leaf in (0..6).rev().filter(|leaf| mask & (1 << leaf) != 0) {
            leaves.insert(leaf..leaf + 1);
        }
        leaves
    }

    fn assert_live_mask(leaves: &LiveLeaves, expected: u8) {
        let actual = (0..6).fold(0, |mask, leaf| {
            mask | (u8::from(leaves.overlaps(leaf..leaf + 1)) << leaf)
        });
        assert_eq!(actual, expected, "{leaves:?}");
        assert!(leaves.ranges().iter().all(|range| !range.is_empty()));
        assert!(
            leaves
                .ranges()
                .windows(2)
                .all(|pair| pair[0].end < pair[1].start),
            "noncanonical demand: {leaves:?}"
        );
        assert_eq!(*leaves, leaves_from_mask(expected));
    }

    #[test]
    fn interval_liveness_matches_dense_set_operations() {
        // Exhaust every small set and range, including empty/touching ranges,
        // split subtraction, and overlapping or differently ordered unions.
        for mask in 0..64 {
            let leaves = leaves_from_mask(mask);
            for start in 0..=6 {
                for end in start..=6 {
                    let range_mask = (start..end).fold(0, |mask, leaf| mask | (1 << leaf));
                    assert_eq!(leaves.overlaps(start..end), mask & range_mask != 0);
                    let mut inserted = leaves.clone();
                    inserted.insert(start..end);
                    assert_live_mask(&inserted, mask | range_mask);
                    let mut removed = leaves.clone();
                    removed.remove(start..end);
                    assert_live_mask(&removed, mask & !range_mask);
                }
            }
            for other in 0..64 {
                let mut joined = leaves.clone();
                joined.union_with(&leaves_from_mask(other));
                assert_live_mask(&joined, mask | other);
            }
        }
    }

    #[test]
    fn whole_root_liveness_is_bounded_by_access_boundaries() {
        let root = ValueId::from_u32(0);
        let mut live = LiveLeafMap::default();
        mark_root_live(&mut live, root, usize::MAX);
        let leaves = live.get_mut(&root).unwrap();
        assert_eq!(leaves.ranges(), slice::from_ref(&(0..usize::MAX)));
        leaves.remove(1..usize::MAX - 1);
        assert_eq!(leaves.ranges(), &[0..1, usize::MAX - 1..usize::MAX]);
        leaves.insert(1..usize::MAX - 1);
        assert_eq!(leaves.ranges(), slice::from_ref(&(0..usize::MAX)));
        leaves.remove(0..usize::MAX);
        assert!(leaves.is_empty());
        let mut empty = LiveLeafMap::default();
        mark_root_live(&mut empty, root, 0);
        assert!(empty.is_empty());
    }

    #[test]
    fn pure_address_ops_do_not_observe_roots() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @Pair = { i256, i256 };

func private %f() {
block0:
    v0.objref<@Pair> = obj.alloc @Pair;
    v1.objref<i256> = obj.proj v0 0.i8;
    return;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        module.func_store.view(func_ref, |func| {
            let obj_proj = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find(|&inst| {
                    downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst)).is_some()
                })
                .expect("obj.proj should exist");

            let accesses = ObjectAccessFacts::new(func, None);
            let effects = accesses.effects(func, obj_proj, None);
            assert!(
                effects.reads.is_empty(),
                "pure projections must not observe memory"
            );
            assert!(effects.writes.is_empty());
        });
    }

    #[test]
    fn observed_roots_report_unknown_contributors() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

declare external %mystery() -> objref<[i256; 8]>;

type @Take = { objref<[i256; 8]> };

func private %f() {
block0:
    v0.objref<@Take> = obj.alloc @Take;
    v1.objref<objref<[i256; 8]>> = obj.proj v0 0.i8;
    v2.objref<[i256; 8]> = call %mystery;
    obj.store v1 v2;
    return;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        let object_effects = super::super::compute_object_effect_summaries(&module);
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices(func, None, &mut layout_cache);
            let provenance = collect_root_provenance(
                func,
                func.ctx(),
                &root_slices,
                &mut layout_cache,
                Some(&object_effects),
            );
            let store = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find(|&inst| {
                    downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)).is_some()
                })
                .expect("obj.store should exist");
            let store = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(store)).unwrap();
            let roots = provenance.may().may_roots(*store.value());
            assert!(roots.observed().is_empty());
            assert!(
                roots.has_unknown(),
                "unknown contributors must remain visible"
            );
        });
    }

    #[test]
    fn enum_write_variant_slices_cover_tag_and_payload() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f() {
block0:
    v0.objref<@OptionI256> = obj.alloc @OptionI256;
    enum.write_variant v0 #Some (7.i256);
    return;
}
"#,
        );

        let func_ref = lookup_func(&module, "f");
        module.func_store.view(func_ref, |func| {
            let mut layout_cache = shape::AggregateLayoutCache::default();
            let root_slices = collect_root_slices(func, None, &mut layout_cache);
            let enum_root = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst))
                        .and_then(|_| func.dfg.inst_result(inst))
                })
                .expect("enum alloc should exist");
            let enum_write_variant = func
                .layout
                .iter_block()
                .flat_map(|block| func.layout.iter_inst(block))
                .find_map(|inst| {
                    downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst))
                })
                .expect("enum.write_variant should exist");
            let pointee_ty = objref_element_ty(func.ctx(), func.dfg.value_ty(enum_root))
                .expect("alloc result should be an objref");
            let base_shape = root_slices
                .get(&enum_root)
                .copied()
                .expect("alloc root slice should exist");
            let base_slice = ObjectSlice {
                root: enum_root,
                ty: pointee_ty,
                first_leaf: 0,
                leaf_count: base_shape.leaf_count,
                total_leaves: base_shape.leaf_count,
            };

            let slices = enum_write_variant_slices(func.ctx(), base_slice, enum_write_variant);
            assert_eq!(
                slices.len(),
                2,
                "enum.write_variant should touch tag and payload"
            );
            assert_eq!(
                slices[0],
                enum_tag_object_slice(func.ctx(), base_slice).expect("tag slice should exist")
            );
            assert_eq!(
                slices[1],
                enum_variant_field_object_slice(
                    func.ctx(),
                    base_slice,
                    *enum_write_variant.variant(),
                    0
                )
                .expect("payload slice should exist")
            );
        });
    }
}
