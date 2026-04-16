use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, I256, Immediate, InstId, Type, Value, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{cast, control_flow, data, downcast},
    types::EnumVariantRef,
};

use super::{
    collect_root_provenance, object_locality,
    object_state::{
        LiveLeafMap, clear_live_slice, enum_write_variant_slices, is_pure_object_address_inst,
        mark_live_slice, mark_root_live, observed_roots, slice_has_live_leaf,
        tracked_root_total_leaves, union_live_leaf_maps,
    },
    object_tracking::{
        ObjectSlice, TrackedObject, collect_root_slices, collect_tracked_objects,
        enum_tag_object_slice, enum_variant_field_object_slice, objref_element_ty, slices_overlap,
        whole_root_slice,
    },
    provenance::{MayProvenance, MayRootSet, ProvenanceFacts, RootValue},
    reconstruct::AggregateValueReconstructor,
    shape,
};

#[derive(Default)]
pub struct AggregateCombine {
    changed: bool,
    layout_cache: shape::AggregateLayoutCache,
}

enum AggregateFieldLookup {
    Found(ValueId),
    BaseNeedsExtract(ValueId),
    Undef(Type),
    Unknown,
}

type EnumObjectFacts = FxHashMap<ExactEnumSlice, KnownEnumObjectState>;
type PendingEnumWrites = FxHashMap<ExactEnumSlice, PendingEnumWrite>;
type EnumLiveMap = LiveLeafMap;
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ExactObjectSlice(ObjectSlice);
impl ExactObjectSlice {
    fn new(slice: ObjectSlice) -> Self {
        Self(slice)
    }

    fn slice(self) -> ObjectSlice {
        self.0
    }

    fn root(self) -> RootValue {
        RootValue::new(self.0.root)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ExactEnumSlice(ExactObjectSlice);
impl ExactEnumSlice {
    fn new(func: &Function, slice: ExactObjectSlice) -> Option<Self> {
        is_enum_compound_ty(func.ctx(), slice.slice().ty).then_some(Self(slice))
    }

    fn slice(self) -> ObjectSlice {
        self.0.slice()
    }

    fn root(self) -> RootValue {
        self.0.root()
    }
}
#[derive(Clone, Copy)]
struct EnumAliasContext<'a> {
    tracked: &'a SecondaryMap<ValueId, Option<TrackedObject>>,
    may: MayProvenance<'a>,
}
impl<'a> EnumAliasContext<'a> {
    fn exact_object(self, value: ValueId) -> Option<ExactObjectSlice> {
        self.tracked[value]
            .as_ref()
            .copied()
            .and_then(TrackedObject::exact)
            .map(ExactObjectSlice::new)
    }

    fn exact_enum(self, func: &Function, value: ValueId) -> Option<ExactEnumSlice> {
        self.exact_object(value)
            .and_then(|slice| ExactEnumSlice::new(func, slice))
    }

    fn exact_local(
        self,
        func: &Function,
        local_roots: &FxHashSet<ValueId>,
        value: ValueId,
    ) -> Option<ExactEnumSlice> {
        let slice = self.exact_enum(func, value)?;
        local_roots.contains(&slice.root().value()).then_some(slice)
    }

    fn observed(self, value: ValueId) -> EnumAlias {
        if let Some(tracked_object) = self.tracked[value].as_ref().copied() {
            return match tracked_object {
                TrackedObject::Exact(slice) => EnumAlias::Exact(ExactObjectSlice::new(slice)),
                TrackedObject::RootUnknown { root, .. } => {
                    EnumAlias::Roots(smallvec![RootValue::new(root)])
                }
            };
        }

        let roots = self.may_root_set(value);
        if roots.has_unknown() {
            return EnumAlias::Unknown;
        }
        let Some(roots) = roots
            .exhaustive_known_roots()
            .filter(|roots| !roots.is_empty())
        else {
            return EnumAlias::None;
        };

        let mut observed = SmallVec::new();
        for root in roots.iter() {
            if !observed.contains(&root) {
                observed.push(root);
            }
        }
        EnumAlias::Roots(observed)
    }

    fn may_root_set(self, value: ValueId) -> MayRootSet<'a> {
        self.may.may_roots(value)
    }
}
enum EnumAlias {
    // Exact aliases stay object-typed because non-enum projections still need to conservatively
    // kill overlapping enum state by slice.
    Exact(ExactObjectSlice),
    Roots(SmallVec<[RootValue; 4]>),
    Unknown,
    None,
}
#[derive(Clone, Debug, PartialEq, Eq)]
struct KnownEnumObjectState {
    variant: EnumVariantRef,
    payloads: SmallVec<[Option<ValueId>; 2]>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PendingEnumWriteKind {
    SetTag,
    WriteVariant,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PendingEnumWrite {
    inst: InstId,
    kind: PendingEnumWriteKind,
    variant: EnumVariantRef,
}
fn collect_combine_enum_root_provenance(
    func: &Function,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> ProvenanceFacts {
    let mut root_slices = collect_root_slices(func, None, layout_cache);
    for &arg in &func.arg_values {
        let Some(root_ty) = objref_element_ty(func.ctx(), func.dfg.value_ty(arg)) else {
            continue;
        };
        root_slices.insert(arg, whole_root_slice(layout_cache, func.ctx(), root_ty));
    }
    collect_root_provenance(func, func.ctx(), &root_slices, layout_cache, None)
}
impl AggregateCombine {
    pub fn run(&mut self, func: &mut Function) -> bool {
        self.changed = false;
        self.layout_cache.clear();
        func.rebuild_users();

        loop {
            let mut iter_changed = false;
            let definitely_non_undef = compute_definitely_non_undef_aggregates(func);
            let enum_root_provenance =
                collect_combine_enum_root_provenance(func, &mut self.layout_cache);
            let tracked = collect_tracked_objects(
                func,
                enum_root_provenance.complete(),
                &mut self.layout_cache,
            );
            let enum_aliases = EnumAliasContext {
                tracked: &tracked,
                may: enum_root_provenance.may(),
            };
            let enum_entry_facts = compute_enum_object_entry_facts(func, enum_aliases);
            let blocks: Vec<_> = func.layout.iter_block().collect();
            for block in blocks {
                let mut enum_facts = enum_entry_facts[block].clone();
                let mut pending_enum_writes = PendingEnumWrites::default();
                let insts: Vec<_> = func.layout.iter_inst(block).collect();
                for inst in insts {
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    iter_changed |= self.try_rewrite_enum_object_inst(
                        func,
                        inst,
                        enum_aliases,
                        &mut enum_facts,
                        &mut pending_enum_writes,
                    );
                    if !func.layout.is_inst_inserted(inst) {
                        continue;
                    }
                    iter_changed |= self.try_rewrite_inst(func, inst, &definitely_non_undef);
                }
            }
            if iter_changed {
                func.rebuild_users();
            }
            iter_changed |= remove_dead_local_enum_writes(func, &mut self.layout_cache);
            if !iter_changed {
                break;
            }
            self.changed = true;
            func.rebuild_users();
        }

        self.changed
    }

    fn try_rewrite_enum_object_inst(
        &mut self,
        func: &mut Function,
        inst: InstId,
        enum_aliases: EnumAliasContext<'_>,
        enum_facts: &mut EnumObjectFacts,
        pending_enum_writes: &mut PendingEnumWrites,
    ) -> bool {
        if let Some(enum_get_tag) =
            downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            clear_pending_enum_writes_for_alias(
                pending_enum_writes,
                enum_aliases,
                *enum_get_tag.object(),
            );

            let Some(result) = func.dfg.inst_result(inst) else {
                return false;
            };
            let Some(object) = enum_aliases.exact_enum(func, *enum_get_tag.object()) else {
                return false;
            };
            let Some(state) = enum_facts.get(&object) else {
                return false;
            };
            let tag = func.dfg.make_imm_value(enum_variant_tag_imm(state.variant));
            func.dfg.change_to_alias(result, tag);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return true;
        }

        if let Some(enum_assert_ref) =
            downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            clear_pending_enum_writes_for_alias(
                pending_enum_writes,
                enum_aliases,
                *enum_assert_ref.object(),
            );
            let Some(object) = enum_aliases.exact_enum(func, *enum_assert_ref.object()) else {
                return false;
            };
            let redundant = enum_facts.get(&object).is_some_and(|state| {
                state.variant == *enum_assert_ref.variant()
                    && state.payloads.iter().all(Option::is_some)
            });
            update_enum_assert_fact(func, enum_facts, object, *enum_assert_ref.variant());

            if redundant {
                if let Some(result) = func.dfg.inst_result(inst) {
                    func.dfg.change_to_alias(result, *enum_assert_ref.object());
                }
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                return true;
            }
            return false;
        }

        if let Some(obj_load) =
            downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)).cloned()
            && let Some(enum_proj) = enum_proj_of_value(func, *obj_load.object())
        {
            clear_pending_enum_writes_for_alias(
                pending_enum_writes,
                enum_aliases,
                *enum_proj.object(),
            );
            let Some(object) = enum_aliases.exact_enum(func, *enum_proj.object()) else {
                return false;
            };

            let changed = if let Some(result) = func.dfg.inst_result(inst)
                && let Some(field_idx) = inst_const_index(func, *enum_proj.field())
                && let Some(replacement) =
                    enum_payload_value(enum_facts, object, *enum_proj.variant(), field_idx)
                && func.dfg.value_ty(replacement) == func.dfg.value_ty(result)
            {
                func.dfg.change_to_alias(result, replacement);
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                true
            } else {
                false
            };
            return changed;
        }

        if let Some(obj_store) =
            downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)).cloned()
            && let Some(enum_proj) = enum_proj_of_value(func, *obj_store.object())
        {
            if let Some(object) = enum_aliases.exact_enum(func, *enum_proj.object())
                && let Some(field_idx) = inst_const_index(func, *enum_proj.field())
            {
                kill_overlapping_enum_state_except(enum_facts, pending_enum_writes, object);
                update_enum_store_fact(
                    enum_facts,
                    object,
                    *enum_proj.variant(),
                    field_idx,
                    *obj_store.value(),
                );
            } else {
                kill_enum_state_for_alias(
                    enum_facts,
                    pending_enum_writes,
                    enum_aliases,
                    *enum_proj.object(),
                );
            }
            return false;
        }

        if let Some(enum_set_tag) =
            downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let Some(object) = enum_aliases.exact_enum(func, *enum_set_tag.object()) else {
                kill_enum_state_for_alias(
                    enum_facts,
                    pending_enum_writes,
                    enum_aliases,
                    *enum_set_tag.object(),
                );
                return false;
            };
            let changed = remove_dead_overwritten_enum_write(
                func,
                pending_enum_writes,
                object,
                PendingEnumWriteKind::SetTag,
                *enum_set_tag.variant(),
            );
            kill_overlapping_enum_state_except(enum_facts, pending_enum_writes, object);
            pending_enum_writes.insert(
                object,
                PendingEnumWrite {
                    inst,
                    kind: PendingEnumWriteKind::SetTag,
                    variant: *enum_set_tag.variant(),
                },
            );
            update_enum_set_tag_fact(func, enum_facts, object, *enum_set_tag.variant());
            return changed;
        }

        if let Some(enum_write_variant) =
            downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            let Some(object) = enum_aliases.exact_enum(func, *enum_write_variant.object()) else {
                kill_enum_state_for_alias(
                    enum_facts,
                    pending_enum_writes,
                    enum_aliases,
                    *enum_write_variant.object(),
                );
                return false;
            };
            let changed = remove_dead_overwritten_enum_write(
                func,
                pending_enum_writes,
                object,
                PendingEnumWriteKind::WriteVariant,
                *enum_write_variant.variant(),
            );
            kill_overlapping_enum_state_except(enum_facts, pending_enum_writes, object);
            pending_enum_writes.insert(
                object,
                PendingEnumWrite {
                    inst,
                    kind: PendingEnumWriteKind::WriteVariant,
                    variant: *enum_write_variant.variant(),
                },
            );
            update_enum_write_variant_fact(
                enum_facts,
                object,
                *enum_write_variant.variant(),
                enum_write_variant.values(),
            );
            return changed;
        }

        if let Some(enum_proj) =
            downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst)).cloned()
        {
            clear_pending_enum_writes_for_alias(
                pending_enum_writes,
                enum_aliases,
                *enum_proj.object(),
            );
            return false;
        }

        kill_touched_enum_object_facts(func, inst, enum_aliases, enum_facts, pending_enum_writes);
        false
    }

    fn try_rewrite_inst(
        &mut self,
        func: &mut Function,
        inst: InstId,
        definitely_non_undef: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        if downcast::<&data::EnumTag>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_enum_tag(func, inst)
        } else if downcast::<&data::EnumIsVariant>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_enum_is_variant(func, inst)
        } else if downcast::<&data::EnumExtract>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_enum_extract(func, inst)
        } else if downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_extract(func, inst)
        } else if downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_insert(func, inst, definitely_non_undef)
        } else if downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)).is_some() {
            self.try_rewrite_phi(func, inst, definitely_non_undef)
        } else {
            false
        }
    }

    fn try_rewrite_enum_tag(&mut self, func: &mut Function, inst: InstId) -> bool {
        let Some(enum_tag) = downcast::<&data::EnumTag>(func.inst_set(), func.dfg.inst(inst))
        else {
            return false;
        };
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let Some(enum_make) = enum_make_of_value(func, *enum_tag.value()) else {
            return false;
        };
        let tag = func.dfg.make_imm_value(Immediate::EnumTag {
            enum_ty: enum_make.variant().enum_ty(),
            value: I256::from(u64::from(enum_make.variant().index())),
        });
        func.dfg.change_to_alias(result, tag);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }

    fn try_rewrite_enum_is_variant(&mut self, func: &mut Function, inst: InstId) -> bool {
        let Some(enum_is_variant) =
            downcast::<&data::EnumIsVariant>(func.inst_set(), func.dfg.inst(inst))
        else {
            return false;
        };
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let Some(enum_make) = enum_make_of_value(func, *enum_is_variant.value()) else {
            return false;
        };
        let folded = func
            .dfg
            .make_imm_value(*enum_make.variant() == *enum_is_variant.variant());
        func.dfg.change_to_alias(result, folded);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }

    fn try_rewrite_enum_extract(&mut self, func: &mut Function, inst: InstId) -> bool {
        let Some(enum_extract) =
            downcast::<&data::EnumExtract>(func.inst_set(), func.dfg.inst(inst))
        else {
            return false;
        };
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let Some(enum_make) = enum_make_of_value(func, *enum_extract.value()) else {
            return false;
        };
        if *enum_make.variant() != *enum_extract.variant() {
            return false;
        }
        let Some(field_idx) = shape::const_u32(&func.dfg, *enum_extract.field()) else {
            return false;
        };
        let Some(&payload) = enum_make.values().get(field_idx as usize) else {
            return false;
        };
        if func.dfg.value_ty(payload) != func.dfg.value_ty(result) {
            return false;
        }
        func.dfg.change_to_alias(result, payload);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }

    fn try_rewrite_extract(&mut self, func: &mut Function, inst: InstId) -> bool {
        let Some(extract) = downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst))
        else {
            return false;
        };
        let extract = extract.clone();
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let Some(target_idx) = inst_const_index(func, *extract.idx()) else {
            return false;
        };

        match walk_insert_chain_for_field(func, *extract.dest(), target_idx) {
            AggregateFieldLookup::Found(found) => {
                if func.dfg.value_ty(found) != func.dfg.value_ty(result) {
                    return self.try_rewrite_extract_through_aggregate_bitcast(
                        func, inst, &extract, result, target_idx,
                    );
                }
                func.dfg.change_to_alias(result, found);
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                true
            }
            AggregateFieldLookup::BaseNeedsExtract(base) if base != *extract.dest() => {
                let new_extract =
                    data::ExtractValue::new_unchecked(func.inst_set(), base, *extract.idx());
                func.dfg.replace_inst(inst, Box::new(new_extract));
                true
            }
            AggregateFieldLookup::Undef(field_ty) => {
                if field_ty != func.dfg.value_ty(result) {
                    return false;
                }
                let undef = func.dfg.make_undef_value(field_ty);
                func.dfg.change_to_alias(result, undef);
                InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
                true
            }
            AggregateFieldLookup::BaseNeedsExtract(_) | AggregateFieldLookup::Unknown => self
                .try_rewrite_extract_through_aggregate_bitcast(
                    func, inst, &extract, result, target_idx,
                ),
        }
    }

    fn try_rewrite_extract_through_aggregate_bitcast(
        &mut self,
        func: &mut Function,
        inst: InstId,
        extract: &data::ExtractValue,
        result: ValueId,
        target_idx: u32,
    ) -> bool {
        let dest = *extract.dest();
        let Some(bitcast_inst) = func.dfg.value_inst(dest) else {
            return false;
        };
        let Some(bitcast) =
            downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(bitcast_inst)).cloned()
        else {
            return false;
        };

        let source = *bitcast.from();
        let source_ty = func.dfg.value_ty(source);
        let dest_ty = func.dfg.value_ty(dest);
        if !shape::is_supported_aggregate_ty(func.ctx(), dest_ty) {
            return false;
        }

        let Some(target_slice) = shape::aggregate_slice_for_index(func.ctx(), dest_ty, target_idx)
        else {
            return false;
        };
        let Some(source_slice) = (if shape::is_supported_aggregate_ty(func.ctx(), source_ty) {
            self.layout_cache.compatible_bitcast_source_slice(
                func.ctx(),
                source_ty,
                dest_ty,
                target_slice,
            )
        } else if self
            .layout_cache
            .single_runtime_word_leaf(func.ctx(), dest_ty)
            .is_some()
        {
            Some(shape::AggregateSlice {
                ty: source_ty,
                first_leaf: 0,
                leaf_count: 1,
            })
        } else {
            None
        }) else {
            return false;
        };
        let Some(replacement) = AggregateValueReconstructor::new(&mut self.layout_cache)
            .rebuild_slice(
                func,
                inst,
                source,
                source_ty,
                source_slice,
                func.dfg.value_ty(result),
            )
        else {
            return false;
        };
        if func.dfg.value_ty(replacement) != func.dfg.value_ty(result) {
            return false;
        }
        func.dfg.change_to_alias(result, replacement);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }

    fn try_rewrite_insert(
        &mut self,
        func: &mut Function,
        inst: InstId,
        definitely_non_undef: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        let Some(insert) = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst))
        else {
            return false;
        };
        let insert = insert.clone();
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };

        // AC5: insert identical field back into aggregate.
        if is_identical_field_reinsert(func, &insert, definitely_non_undef) {
            if func.dfg.value_ty(*insert.dest()) != func.dfg.value_ty(result) {
                return false;
            }
            func.dfg.change_to_alias(result, *insert.dest());
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return true;
        }

        // AC3: overwrite collapse.
        if let Some(prev_inst) = func.dfg.value_inst(*insert.dest())
            && let Some(prev) =
                downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(prev_inst))
            && equivalent_indices(func, *insert.idx(), *prev.idx())
        {
            let rewritten = data::InsertValue::new_unchecked(
                func.inst_set(),
                *prev.dest(),
                *insert.idx(),
                *insert.value(),
            );
            func.dfg.replace_inst(inst, Box::new(rewritten));
            return true;
        }

        // AC6: full reconstruction reuse.
        if let Some(source) = try_reconstruct_original_aggregate(func, result) {
            if func.dfg.value_ty(source) != func.dfg.value_ty(result) {
                return false;
            }
            func.dfg.change_to_alias(result, source);
            InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
            return true;
        }

        false
    }

    fn try_rewrite_phi(
        &mut self,
        func: &mut Function,
        inst: InstId,
        definitely_non_undef: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        self.try_rewrite_phi_of_extracts(func, inst)
            || self.try_rewrite_phi_of_inserts(func, inst, definitely_non_undef)
    }

    fn try_rewrite_phi_of_extracts(&mut self, func: &mut Function, inst: InstId) -> bool {
        let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)) else {
            return false;
        };
        let phi = phi.clone();
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let Some((first_val, first_pred)) = phi.args().first().copied() else {
            return false;
        };
        let Some(first_extract_inst) = func.dfg.value_inst(first_val) else {
            return false;
        };
        let Some(first_extract) =
            downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(first_extract_inst))
        else {
            return false;
        };
        let Some(idx) = inst_const_index(func, *first_extract.idx()) else {
            return false;
        };
        let idx_value = *first_extract.idx();
        let agg_ty = func.dfg.value_ty(*first_extract.dest());
        let res_ty = func.dfg.value_ty(result);

        let mut agg_args = vec![(*first_extract.dest(), first_pred)];
        for &(incoming, pred) in phi.args().iter().skip(1) {
            let Some(extract_inst) = func.dfg.value_inst(incoming) else {
                return false;
            };
            let Some(extract) =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(extract_inst))
            else {
                return false;
            };
            if inst_const_index(func, *extract.idx()) != Some(idx) {
                return false;
            }
            if func.dfg.value_ty(*extract.dest()) != agg_ty {
                return false;
            }
            if func.dfg.value_ty(incoming) != res_ty {
                return false;
            }
            agg_args.push((*extract.dest(), pred));
        }

        let block = func.layout.inst_block(inst);
        let agg_phi_value = append_phi_at_block_top(func, block, agg_ty, agg_args);
        let new_extract = append_non_phi_after_phi_region(
            func,
            block,
            data::ExtractValue::new_unchecked(func.inst_set(), agg_phi_value, idx_value),
            res_ty,
        );

        func.dfg.change_to_alias(result, new_extract);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }

    fn try_rewrite_phi_of_inserts(
        &mut self,
        func: &mut Function,
        inst: InstId,
        definitely_non_undef: &SecondaryMap<ValueId, bool>,
    ) -> bool {
        let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)) else {
            return false;
        };
        let phi = phi.clone();
        let Some(result) = func.dfg.inst_result(inst) else {
            return false;
        };
        let Some((first_val, first_pred)) = phi.args().first().copied() else {
            return false;
        };
        let Some(first_insert_inst) = func.dfg.value_inst(first_val) else {
            return false;
        };
        let Some(first_insert) =
            downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(first_insert_inst))
        else {
            return false;
        };
        if is_identical_field_reinsert(func, first_insert, definitely_non_undef) {
            return false;
        }
        let Some(idx) = inst_const_index(func, *first_insert.idx()) else {
            return false;
        };
        let idx_value = *first_insert.idx();
        let base_ty = func.dfg.value_ty(*first_insert.dest());
        let payload_ty = func.dfg.value_ty(*first_insert.value());
        let result_ty = func.dfg.value_ty(result);

        let mut base_args = vec![(*first_insert.dest(), first_pred)];
        let mut payload_args = vec![(*first_insert.value(), first_pred)];

        for &(incoming, pred) in phi.args().iter().skip(1) {
            let Some(insert_inst) = func.dfg.value_inst(incoming) else {
                return false;
            };
            let Some(insert) =
                downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(insert_inst))
            else {
                return false;
            };
            if is_identical_field_reinsert(func, insert, definitely_non_undef) {
                return false;
            }
            if inst_const_index(func, *insert.idx()) != Some(idx) {
                return false;
            }
            if func.dfg.value_ty(incoming) != result_ty
                || func.dfg.value_ty(*insert.dest()) != base_ty
                || func.dfg.value_ty(*insert.value()) != payload_ty
            {
                return false;
            }
            base_args.push((*insert.dest(), pred));
            payload_args.push((*insert.value(), pred));
        }

        let block = func.layout.inst_block(inst);
        let base_phi = append_phi_at_block_top(func, block, base_ty, base_args);
        let payload_phi = append_phi_at_block_top(func, block, payload_ty, payload_args);
        let new_insert = append_non_phi_after_phi_region(
            func,
            block,
            data::InsertValue::new_unchecked(func.inst_set(), base_phi, idx_value, payload_phi),
            result_ty,
        );

        func.dfg.change_to_alias(result, new_insert);
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        true
    }
}
fn compute_enum_object_entry_facts(
    func: &Function,
    enum_aliases: EnumAliasContext<'_>,
) -> SecondaryMap<BlockId, EnumObjectFacts> {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    let reachable = cfg.reachable_blocks();
    let mut order: Vec<_> = cfg.post_order().collect();
    order.reverse();

    let mut in_states = SecondaryMap::<BlockId, EnumObjectFacts>::default();
    let mut out_states = SecondaryMap::<BlockId, EnumObjectFacts>::default();

    loop {
        let mut changed = false;
        for &block in &order {
            if !reachable[block] {
                continue;
            }

            let next_in = meet_enum_object_facts(
                cfg.preds_of(block)
                    .copied()
                    .filter(|pred| reachable[*pred])
                    .map(|pred| {
                        edge_enum_object_facts(func, pred, block, &out_states[pred], enum_aliases)
                    }),
            );
            if next_in != in_states[block] {
                in_states[block] = next_in.clone();
                changed = true;
            }

            let mut state = next_in;
            let mut pending_writes = PendingEnumWrites::default();
            for inst in func.layout.iter_inst(block) {
                if func.layout.is_inst_inserted(inst) {
                    transfer_enum_object_facts(
                        func,
                        inst,
                        enum_aliases,
                        &mut state,
                        &mut pending_writes,
                    );
                }
            }

            if state != out_states[block] {
                out_states[block] = state;
                changed = true;
            }
        }

        if !changed {
            return in_states;
        }
    }
}
fn remove_dead_local_enum_writes(
    func: &mut Function,
    layout_cache: &mut shape::AggregateLayoutCache,
) -> bool {
    let local_roots = collect_local_object_roots(func);
    if local_roots.is_empty() {
        return false;
    }

    let root_provenance = collect_combine_enum_root_provenance(func, layout_cache);
    let tracked = collect_tracked_objects(func, root_provenance.complete(), layout_cache);
    let enum_aliases = EnumAliasContext {
        tracked: &tracked,
        may: root_provenance.may(),
    };
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    let reachable = cfg.reachable_blocks();
    let order: Vec<_> = cfg.post_order().collect();
    let mut in_states = SecondaryMap::<BlockId, EnumLiveMap>::new();
    let mut out_states = SecondaryMap::<BlockId, EnumLiveMap>::new();

    loop {
        let mut changed = false;
        for &block in &order {
            if !reachable[block] {
                continue;
            }

            let out = union_live_leaf_maps(
                cfg.succs_of(block)
                    .copied()
                    .filter(|succ| reachable[*succ])
                    .map(|succ| in_states[succ].clone()),
            );
            if out != out_states[block] {
                out_states[block] = out.clone();
                changed = true;
            }

            let mut live = out;
            for inst in func
                .layout
                .iter_inst(block)
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
            {
                if func.layout.is_inst_inserted(inst) {
                    transfer_backward_enum_live(func, inst, &local_roots, enum_aliases, &mut live);
                }
            }

            if live != in_states[block] {
                in_states[block] = live;
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    let mut changed = false;
    for &block in &order {
        if !reachable[block] {
            continue;
        }

        let mut live = out_states[block].clone();
        for inst in func
            .layout
            .iter_inst(block)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
        {
            if !func.layout.is_inst_inserted(inst) {
                continue;
            }
            let removed =
                try_remove_dead_local_enum_write(func, inst, &local_roots, enum_aliases, &live);
            changed |= removed;
            if !removed {
                transfer_backward_enum_live(func, inst, &local_roots, enum_aliases, &mut live);
            }
        }
    }

    changed
}
fn collect_local_object_roots(func: &Function) -> FxHashSet<ValueId> {
    let mut local_roots = FxHashSet::default();

    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            let Some(_) = downcast::<&data::ObjAlloc>(func.inst_set(), func.dfg.inst(inst)) else {
                continue;
            };
            let Some(result) = func.dfg.inst_result(inst) else {
                continue;
            };
            if objref_element_ty(func.ctx(), func.dfg.value_ty(result)).is_none() {
                continue;
            }
            if object_root_stays_local(func, result) {
                local_roots.insert(result);
            }
        }
    }

    local_roots
}
fn object_root_stays_local(func: &Function, root: ValueId) -> bool {
    let local_object_args = FxHashMap::default();
    object_locality::object_root_stays_local(
        func,
        root,
        func.dfg.value_ty(root),
        &local_object_args,
        false,
    )
}
fn kill_pending_enum_writes_for_root(pending_enum_writes: &mut PendingEnumWrites, root: RootValue) {
    pending_enum_writes.retain(|slice, _| slice.root() != root);
}
fn kill_overlapping_pending_enum_writes(
    pending_enum_writes: &mut PendingEnumWrites,
    slice: ExactObjectSlice,
) {
    pending_enum_writes.retain(|other, _| !slices_overlap(other.slice(), slice.slice()));
}
fn clear_pending_enum_writes_for_alias(
    pending_enum_writes: &mut PendingEnumWrites,
    enum_aliases: EnumAliasContext<'_>,
    value: ValueId,
) {
    match enum_aliases.observed(value) {
        EnumAlias::Exact(slice) => kill_overlapping_pending_enum_writes(pending_enum_writes, slice),
        EnumAlias::Roots(roots) => {
            for root in roots {
                kill_pending_enum_writes_for_root(pending_enum_writes, root);
            }
        }
        EnumAlias::Unknown => pending_enum_writes.clear(),
        EnumAlias::None => {}
    }
}
fn kill_root_enum_state(
    enum_facts: &mut EnumObjectFacts,
    pending_enum_writes: &mut PendingEnumWrites,
    root: RootValue,
) {
    enum_facts.retain(|slice, _| slice.root() != root);
    pending_enum_writes.retain(|slice, _| slice.root() != root);
}
fn kill_overlapping_enum_state(
    enum_facts: &mut EnumObjectFacts,
    pending_enum_writes: &mut PendingEnumWrites,
    slice: ExactObjectSlice,
) {
    enum_facts.retain(|other, _| !slices_overlap(other.slice(), slice.slice()));
    pending_enum_writes.retain(|other, _| !slices_overlap(other.slice(), slice.slice()));
}
fn kill_overlapping_enum_state_except(
    enum_facts: &mut EnumObjectFacts,
    pending_enum_writes: &mut PendingEnumWrites,
    slice: ExactEnumSlice,
) {
    enum_facts.retain(|other, _| *other == slice || !slices_overlap(other.slice(), slice.slice()));
    pending_enum_writes
        .retain(|other, _| *other == slice || !slices_overlap(other.slice(), slice.slice()));
}
fn kill_enum_state_for_alias(
    enum_facts: &mut EnumObjectFacts,
    pending_enum_writes: &mut PendingEnumWrites,
    enum_aliases: EnumAliasContext<'_>,
    value: ValueId,
) {
    match enum_aliases.observed(value) {
        EnumAlias::Exact(slice) => {
            kill_overlapping_enum_state(enum_facts, pending_enum_writes, slice)
        }
        EnumAlias::Roots(roots) => {
            for root in roots {
                kill_root_enum_state(enum_facts, pending_enum_writes, root);
            }
        }
        EnumAlias::Unknown => {
            enum_facts.clear();
            pending_enum_writes.clear();
        }
        EnumAlias::None => {}
    }
}
fn is_enum_state_passthrough_inst(func: &Function, inst: InstId) -> bool {
    is_pure_object_address_inst(func, inst)
        || downcast::<&control_flow::Jump>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&control_flow::Br>(func.inst_set(), func.dfg.inst(inst)).is_some()
        || downcast::<&control_flow::BrTable>(func.inst_set(), func.dfg.inst(inst)).is_some()
}
fn observed_object_roots(
    func: &Function,
    inst: InstId,
    enum_aliases: EnumAliasContext<'_>,
    skip: &[ValueId],
) -> (Vec<RootValue>, bool) {
    if is_enum_state_passthrough_inst(func, inst) {
        return (Vec::new(), false);
    }

    let (roots, observed_unknown) = observed_roots(func, inst, enum_aliases.may, skip);
    (
        roots.into_iter().map(RootValue::new).collect(),
        observed_unknown,
    )
}
fn transfer_backward_enum_live(
    func: &Function,
    inst: InstId,
    local_roots: &FxHashSet<ValueId>,
    enum_aliases: EnumAliasContext<'_>,
    live: &mut EnumLiveMap,
) {
    if is_enum_state_passthrough_inst(func, inst) {
        return;
    }

    if let Some(obj_load) = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst)) {
        if let Some((object, variant, field)) = enum_field_of_value(func, *obj_load.object())
            && let Some(base_slice) = enum_aliases.exact_local(func, local_roots, object)
            && let Some(field_slice) =
                enum_variant_field_object_slice(func.ctx(), base_slice.slice(), variant, field)
        {
            mark_live_slice(live, field_slice);
        } else {
            mark_live_may_roots(
                local_roots,
                enum_aliases,
                live,
                enum_aliases.may_root_set(*obj_load.object()),
            );
        }
        mark_observed_local_roots_live(
            func,
            inst,
            local_roots,
            enum_aliases,
            live,
            &[*obj_load.object()],
        );
        return;
    }

    if let Some(obj_store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst)) {
        mark_observed_local_roots_live(
            func,
            inst,
            local_roots,
            enum_aliases,
            live,
            &[*obj_store.object()],
        );
        if let Some((object, variant, field)) = enum_field_of_value(func, *obj_store.object())
            && let Some(base_slice) = enum_aliases.exact_local(func, local_roots, object)
            && let Some(field_slice) =
                enum_variant_field_object_slice(func.ctx(), base_slice.slice(), variant, field)
        {
            clear_live_slice(live, field_slice);
        } else {
            mark_live_may_roots(
                local_roots,
                enum_aliases,
                live,
                enum_aliases.may_root_set(*obj_store.object()),
            );
        }
        return;
    }

    if let Some(enum_get_tag) = downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst))
    {
        if let Some(tag_slice) = enum_aliases
            .exact_local(func, local_roots, *enum_get_tag.object())
            .and_then(|slice| enum_tag_object_slice(func.ctx(), slice.slice()))
        {
            mark_live_slice(live, tag_slice);
        } else {
            mark_live_may_roots(
                local_roots,
                enum_aliases,
                live,
                enum_aliases.may_root_set(*enum_get_tag.object()),
            );
        }
        return;
    }

    if let Some(enum_assert_ref) =
        downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst))
    {
        if let Some(tag_slice) = enum_aliases
            .exact_local(func, local_roots, *enum_assert_ref.object())
            .and_then(|slice| enum_tag_object_slice(func.ctx(), slice.slice()))
        {
            mark_live_slice(live, tag_slice);
        } else {
            mark_live_may_roots(
                local_roots,
                enum_aliases,
                live,
                enum_aliases.may_root_set(*enum_assert_ref.object()),
            );
        }
        return;
    }

    if let Some(enum_set_tag) = downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst))
    {
        if let Some(tag_slice) = enum_aliases
            .exact_local(func, local_roots, *enum_set_tag.object())
            .and_then(|slice| enum_tag_object_slice(func.ctx(), slice.slice()))
        {
            clear_live_slice(live, tag_slice);
        } else {
            mark_live_may_roots(
                local_roots,
                enum_aliases,
                live,
                enum_aliases.may_root_set(*enum_set_tag.object()),
            );
        }
        return;
    }

    if let Some(enum_write_variant) =
        downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst))
    {
        if let Some(base_slice) =
            enum_aliases.exact_local(func, local_roots, *enum_write_variant.object())
        {
            for slice in
                enum_write_variant_slices(func.ctx(), base_slice.slice(), enum_write_variant)
            {
                clear_live_slice(live, slice);
            }
        } else {
            mark_live_may_roots(
                local_roots,
                enum_aliases,
                live,
                enum_aliases.may_root_set(*enum_write_variant.object()),
            );
        }
        mark_observed_local_roots_live(
            func,
            inst,
            local_roots,
            enum_aliases,
            live,
            &[*enum_write_variant.object()],
        );
        return;
    }

    mark_observed_local_roots_live(func, inst, local_roots, enum_aliases, live, &[]);
}
fn try_remove_dead_local_enum_write(
    func: &mut Function,
    inst: InstId,
    local_roots: &FxHashSet<ValueId>,
    enum_aliases: EnumAliasContext<'_>,
    live: &EnumLiveMap,
) -> bool {
    if let Some(obj_store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst))
        && let Some((object, variant, field)) = enum_field_of_value(func, *obj_store.object())
        && let Some(base_slice) = enum_aliases.exact_local(func, local_roots, object)
        && let Some(field_slice) =
            enum_variant_field_object_slice(func.ctx(), base_slice.slice(), variant, field)
        && !slice_has_live_leaf(live, field_slice)
    {
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        return true;
    }

    if let Some(enum_set_tag) = downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst))
        && let Some(tag_slice) = enum_aliases
            .exact_local(func, local_roots, *enum_set_tag.object())
            .and_then(|slice| enum_tag_object_slice(func.ctx(), slice.slice()))
        && !slice_has_live_leaf(live, tag_slice)
    {
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        return true;
    }

    if let Some(enum_write_variant) =
        downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst))
        && let Some(base_slice) =
            enum_aliases.exact_local(func, local_roots, *enum_write_variant.object())
        && !enum_write_variant_slices(func.ctx(), base_slice.slice(), enum_write_variant)
            .into_iter()
            .any(|slice| slice_has_live_leaf(live, slice))
    {
        InstInserter::at_location(CursorLocation::At(inst)).remove_inst(func);
        return true;
    }

    false
}
fn enum_field_of_value(func: &Function, value: ValueId) -> Option<(ValueId, EnumVariantRef, u32)> {
    let enum_proj = enum_proj_of_value(func, value)?;
    Some((
        *enum_proj.object(),
        *enum_proj.variant(),
        inst_const_index(func, *enum_proj.field())?,
    ))
}
fn mark_observed_local_roots_live(
    func: &Function,
    inst: InstId,
    local_roots: &FxHashSet<ValueId>,
    enum_aliases: EnumAliasContext<'_>,
    live: &mut EnumLiveMap,
    skip: &[ValueId],
) {
    let (roots, observed_unknown) = observed_object_roots(func, inst, enum_aliases, skip);
    if observed_unknown {
        mark_all_local_roots_live(local_roots, enum_aliases, live);
        return;
    }
    for root in roots {
        if local_roots.contains(&root.value()) {
            mark_root_live(
                live,
                root.value(),
                tracked_root_total_leaves(enum_aliases.tracked, root.value()),
            );
        }
    }
}
fn mark_live_may_roots(
    local_roots: &FxHashSet<ValueId>,
    enum_aliases: EnumAliasContext<'_>,
    live: &mut EnumLiveMap,
    roots: MayRootSet<'_>,
) {
    if roots.has_unknown() {
        mark_all_local_roots_live(local_roots, enum_aliases, live);
        return;
    }
    for root in roots.observed().iter() {
        if local_roots.contains(&root.value()) {
            mark_root_live(
                live,
                root.value(),
                tracked_root_total_leaves(enum_aliases.tracked, root.value()),
            );
        }
    }
}
fn mark_all_local_roots_live(
    local_roots: &FxHashSet<ValueId>,
    enum_aliases: EnumAliasContext<'_>,
    live: &mut EnumLiveMap,
) {
    for &root in local_roots {
        mark_root_live(
            live,
            root,
            tracked_root_total_leaves(enum_aliases.tracked, root),
        );
    }
}

fn meet_enum_object_facts(states: impl Iterator<Item = EnumObjectFacts>) -> EnumObjectFacts {
    let mut states = states;
    let Some(mut out) = states.next() else {
        return EnumObjectFacts::default();
    };

    for state in states {
        out.retain(|object, fact| {
            let Some(other) = state.get(object) else {
                return false;
            };
            let Some(merged) = meet_known_enum_object_state(fact, other) else {
                return false;
            };
            *fact = merged;
            true
        });
    }

    out
}

fn meet_known_enum_object_state(
    lhs: &KnownEnumObjectState,
    rhs: &KnownEnumObjectState,
) -> Option<KnownEnumObjectState> {
    if lhs.variant != rhs.variant || lhs.payloads.len() != rhs.payloads.len() {
        return None;
    }

    let payloads = lhs
        .payloads
        .iter()
        .zip(rhs.payloads.iter())
        .map(|(lhs, rhs)| (*lhs == *rhs).then_some(*lhs).flatten())
        .collect();
    Some(KnownEnumObjectState {
        variant: lhs.variant,
        payloads,
    })
}

fn edge_enum_object_facts(
    func: &Function,
    pred: BlockId,
    succ: BlockId,
    out_state: &EnumObjectFacts,
    enum_aliases: EnumAliasContext<'_>,
) -> EnumObjectFacts {
    let mut edge_state = out_state.clone();
    let Some(term) = func.layout.last_inst_of(pred) else {
        return edge_state;
    };

    if let Some(br_table) = downcast::<&control_flow::BrTable>(func.inst_set(), func.dfg.inst(term))
        && let Some((object, variant)) = br_table_edge_variant(func, br_table, succ, enum_aliases)
    {
        update_enum_assert_fact(func, &mut edge_state, object, variant);
        return edge_state;
    }

    edge_state
}

fn br_table_edge_variant(
    func: &Function,
    br_table: &control_flow::BrTable,
    succ: BlockId,
    enum_aliases: EnumAliasContext<'_>,
) -> Option<(ExactEnumSlice, EnumVariantRef)> {
    let enum_get_tag = enum_get_tag_of_value(func, *br_table.scrutinee())?;
    let object = enum_aliases.exact_enum(func, *enum_get_tag.object())?;
    let Type::EnumTag(enum_ty) = func.dfg.value_ty(*br_table.scrutinee()) else {
        return None;
    };

    let mut matched = SmallVec::<[EnumVariantRef; 2]>::new();
    for &(case_value, dest) in br_table.table() {
        if dest != succ {
            continue;
        }
        let variant = enum_variant_for_tag_value(func, enum_ty, case_value)?;
        if !matched.contains(&variant) {
            matched.push(variant);
        }
    }
    if matched.len() == 1 {
        return Some((object, matched[0]));
    }
    if !matched.is_empty() {
        return None;
    }

    if *br_table.default() != Some(succ) {
        return None;
    }

    let remaining = remaining_br_table_variants(func, enum_ty, br_table)?;
    if remaining.len() == 1 {
        Some((object, remaining[0]))
    } else {
        None
    }
}

fn remaining_br_table_variants(
    func: &Function,
    enum_ty: sonatina_ir::types::CompoundTypeRef,
    br_table: &control_flow::BrTable,
) -> Option<SmallVec<[EnumVariantRef; 2]>> {
    let variant_count = enum_variant_count(func.ctx(), enum_ty)?;
    let mut covered = FxHashMap::<EnumVariantRef, ()>::default();
    for &(case_value, _) in br_table.table() {
        covered.insert(enum_variant_for_tag_value(func, enum_ty, case_value)?, ());
    }

    let mut remaining = SmallVec::new();
    for idx in 0..variant_count {
        let variant = EnumVariantRef::new(
            enum_ty,
            u32::try_from(idx).expect("enum variant index overflow"),
        );
        if !covered.contains_key(&variant) {
            remaining.push(variant);
        }
    }
    Some(remaining)
}

fn enum_variant_for_tag_value(
    func: &Function,
    enum_ty: sonatina_ir::types::CompoundTypeRef,
    value: ValueId,
) -> Option<EnumVariantRef> {
    let imm = func.dfg.value_imm(value)?;
    let idx = imm.to_nonnegative_usize()?;
    let variant_count = enum_variant_count(func.ctx(), enum_ty)?;
    (idx < variant_count).then_some(EnumVariantRef::new(
        enum_ty,
        u32::try_from(idx).expect("enum variant index overflow"),
    ))
}

fn transfer_enum_object_facts(
    func: &Function,
    inst: InstId,
    enum_aliases: EnumAliasContext<'_>,
    enum_facts: &mut EnumObjectFacts,
    pending_enum_writes: &mut PendingEnumWrites,
) {
    if let Some(enum_get_tag) = downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst))
    {
        clear_pending_enum_writes_for_alias(
            pending_enum_writes,
            enum_aliases,
            *enum_get_tag.object(),
        );
        return;
    }

    if let Some(enum_assert_ref) =
        downcast::<&data::EnumAssertVariantRef>(func.inst_set(), func.dfg.inst(inst))
    {
        clear_pending_enum_writes_for_alias(
            pending_enum_writes,
            enum_aliases,
            *enum_assert_ref.object(),
        );
        if let Some(object) = enum_aliases.exact_enum(func, *enum_assert_ref.object()) {
            update_enum_assert_fact(func, enum_facts, object, *enum_assert_ref.variant());
        }
        return;
    }

    if let Some(enum_proj) = downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst)) {
        clear_pending_enum_writes_for_alias(pending_enum_writes, enum_aliases, *enum_proj.object());
        return;
    }

    if let Some(enum_set_tag) = downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst))
    {
        if let Some(object) = enum_aliases.exact_enum(func, *enum_set_tag.object()) {
            kill_overlapping_enum_state_except(enum_facts, pending_enum_writes, object);
            pending_enum_writes.insert(
                object,
                PendingEnumWrite {
                    inst,
                    kind: PendingEnumWriteKind::SetTag,
                    variant: *enum_set_tag.variant(),
                },
            );
            update_enum_set_tag_fact(func, enum_facts, object, *enum_set_tag.variant());
        } else {
            kill_enum_state_for_alias(
                enum_facts,
                pending_enum_writes,
                enum_aliases,
                *enum_set_tag.object(),
            );
        }
        return;
    }

    if let Some(enum_write_variant) =
        downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst))
    {
        if let Some(object) = enum_aliases.exact_enum(func, *enum_write_variant.object()) {
            kill_overlapping_enum_state_except(enum_facts, pending_enum_writes, object);
            pending_enum_writes.insert(
                object,
                PendingEnumWrite {
                    inst,
                    kind: PendingEnumWriteKind::WriteVariant,
                    variant: *enum_write_variant.variant(),
                },
            );
            update_enum_write_variant_fact(
                enum_facts,
                object,
                *enum_write_variant.variant(),
                enum_write_variant.values(),
            );
        } else {
            kill_enum_state_for_alias(
                enum_facts,
                pending_enum_writes,
                enum_aliases,
                *enum_write_variant.object(),
            );
        }
        return;
    }

    if let Some(obj_load) = downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst))
        && let Some(enum_proj) = enum_proj_of_value(func, *obj_load.object())
    {
        clear_pending_enum_writes_for_alias(pending_enum_writes, enum_aliases, *enum_proj.object());
        return;
    }

    if let Some(obj_store) = downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst))
        && let Some(enum_proj) = enum_proj_of_value(func, *obj_store.object())
    {
        if let Some(object) = enum_aliases.exact_enum(func, *enum_proj.object())
            && let Some(field_idx) = inst_const_index(func, *enum_proj.field())
        {
            kill_overlapping_enum_state_except(enum_facts, pending_enum_writes, object);
            update_enum_store_fact(
                enum_facts,
                object,
                *enum_proj.variant(),
                field_idx,
                *obj_store.value(),
            );
        } else {
            kill_enum_state_for_alias(
                enum_facts,
                pending_enum_writes,
                enum_aliases,
                *enum_proj.object(),
            );
        }
        return;
    }

    kill_touched_enum_object_facts(func, inst, enum_aliases, enum_facts, pending_enum_writes);
}

fn update_enum_assert_fact(
    func: &Function,
    enum_facts: &mut EnumObjectFacts,
    object: ExactEnumSlice,
    variant: EnumVariantRef,
) {
    let payloads = enum_facts
        .get(&object)
        .filter(|state| state.variant == variant)
        .map(|state| state.payloads.clone())
        .unwrap_or_else(|| unknown_variant_payloads(func, variant));
    enum_facts.insert(object, KnownEnumObjectState { variant, payloads });
}

fn update_enum_set_tag_fact(
    func: &Function,
    enum_facts: &mut EnumObjectFacts,
    object: ExactEnumSlice,
    variant: EnumVariantRef,
) {
    let payloads = enum_facts
        .get(&object)
        .filter(|state| state.variant == variant)
        .map(|state| state.payloads.clone())
        .unwrap_or_else(|| unknown_variant_payloads(func, variant));
    enum_facts.insert(object, KnownEnumObjectState { variant, payloads });
}

fn update_enum_write_variant_fact(
    enum_facts: &mut EnumObjectFacts,
    object: ExactEnumSlice,
    variant: EnumVariantRef,
    values: &[ValueId],
) {
    enum_facts.insert(
        object,
        KnownEnumObjectState {
            variant,
            payloads: values.iter().copied().map(Some).collect(),
        },
    );
}

fn update_enum_store_fact(
    enum_facts: &mut EnumObjectFacts,
    object: ExactEnumSlice,
    variant: EnumVariantRef,
    field_idx: u32,
    value: ValueId,
) {
    let Some(state) = enum_facts.get_mut(&object) else {
        return;
    };
    if state.variant != variant {
        return;
    }
    let Some(field) = usize::try_from(field_idx).ok() else {
        return;
    };
    if let Some(slot) = state.payloads.get_mut(field) {
        *slot = Some(value);
    }
}

fn enum_payload_value(
    enum_facts: &EnumObjectFacts,
    object: ExactEnumSlice,
    variant: EnumVariantRef,
    field_idx: u32,
) -> Option<ValueId> {
    let field = usize::try_from(field_idx).ok()?;
    enum_facts
        .get(&object)
        .filter(|state| state.variant == variant)?
        .payloads
        .get(field)
        .copied()
        .flatten()
}

fn unknown_variant_payloads(
    func: &Function,
    variant: EnumVariantRef,
) -> SmallVec<[Option<ValueId>; 2]> {
    let field_count = func
        .ctx()
        .with_ty_store(|store| {
            store
                .enum_variant_data(variant)
                .map(|data| data.fields.len())
        })
        .unwrap_or(0);
    let mut payloads = SmallVec::new();
    payloads.resize(field_count, None);
    payloads
}

fn remove_dead_overwritten_enum_write(
    func: &mut Function,
    pending_enum_writes: &mut PendingEnumWrites,
    object: ExactEnumSlice,
    next_kind: PendingEnumWriteKind,
    next_variant: EnumVariantRef,
) -> bool {
    let Some(prev) = pending_enum_writes.remove(&object) else {
        return false;
    };
    if !func.layout.is_inst_inserted(prev.inst) {
        return false;
    }

    let removable = prev.kind == PendingEnumWriteKind::SetTag
        || (prev.kind == PendingEnumWriteKind::WriteVariant
            && next_kind == PendingEnumWriteKind::WriteVariant
            && prev.variant == next_variant);
    if !removable {
        pending_enum_writes.insert(object, prev);
        return false;
    }

    InstInserter::at_location(CursorLocation::At(prev.inst)).remove_inst(func);
    true
}

fn kill_touched_enum_object_facts(
    func: &Function,
    inst: InstId,
    enum_aliases: EnumAliasContext<'_>,
    enum_facts: &mut EnumObjectFacts,
    pending_enum_writes: &mut PendingEnumWrites,
) {
    if is_enum_state_passthrough_inst(func, inst) {
        return;
    }

    let mut touched_slices = SmallVec::<[ExactObjectSlice; 4]>::new();
    let mut touched_roots = SmallVec::<[RootValue; 4]>::new();
    let mut saw_unknown = false;
    for value in func.dfg.inst(inst).collect_values() {
        append_touched_enum_object(
            value,
            enum_aliases,
            &mut touched_slices,
            &mut touched_roots,
            &mut saw_unknown,
        );
    }

    if saw_unknown {
        enum_facts.clear();
        pending_enum_writes.clear();
        return;
    }

    for slice in touched_slices {
        kill_overlapping_enum_state(enum_facts, pending_enum_writes, slice);
    }
    for root in touched_roots {
        kill_root_enum_state(enum_facts, pending_enum_writes, root);
    }
}

fn append_touched_enum_object(
    value: ValueId,
    enum_aliases: EnumAliasContext<'_>,
    touched_slices: &mut SmallVec<[ExactObjectSlice; 4]>,
    touched_roots: &mut SmallVec<[RootValue; 4]>,
    saw_unknown: &mut bool,
) {
    match enum_aliases.observed(value) {
        EnumAlias::Exact(slice) => {
            if !touched_slices.contains(&slice) {
                touched_slices.push(slice);
            }
        }
        EnumAlias::Roots(roots) => {
            for root in roots {
                if !touched_roots.contains(&root) {
                    touched_roots.push(root);
                }
            }
        }
        EnumAlias::Unknown => *saw_unknown = true,
        EnumAlias::None => {}
    }
}

fn is_enum_compound_ty(ctx: &sonatina_ir::module::ModuleCtx, ty: Type) -> bool {
    let Type::Compound(ty) = ty else {
        return false;
    };
    ctx.with_ty_store(|store| {
        matches!(
            store.resolve_compound(ty),
            sonatina_ir::types::CompoundType::Enum(_)
        )
    })
}

fn enum_variant_count(
    ctx: &sonatina_ir::module::ModuleCtx,
    enum_ty: sonatina_ir::types::CompoundTypeRef,
) -> Option<usize> {
    ctx.with_ty_store(|store| store.enum_data(enum_ty).map(|data| data.variants.len()))
}

fn enum_variant_tag_imm(variant: EnumVariantRef) -> Immediate {
    Immediate::EnumTag {
        enum_ty: variant.enum_ty(),
        value: I256::from(u64::from(variant.index())),
    }
}

fn enum_get_tag_of_value(func: &Function, value: ValueId) -> Option<data::EnumGetTag> {
    let inst = func.dfg.value_inst(value)?;
    downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst)).cloned()
}

fn enum_proj_of_value(func: &Function, value: ValueId) -> Option<data::EnumProj> {
    let inst = func.dfg.value_inst(value)?;
    downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst)).cloned()
}

fn append_phi_at_block_top(
    func: &mut Function,
    block: BlockId,
    ty: Type,
    args: Vec<(ValueId, BlockId)>,
) -> ValueId {
    let phi = control_flow::Phi::new_unchecked(func.inst_set(), args);
    let mut cursor = InstInserter::at_location(CursorLocation::BlockTop(block));
    let inst = cursor.prepend_inst_data(func, phi);
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty,
    });
    cursor.attach_result(func, inst, value);
    value
}

fn append_non_phi_after_phi_region<I: sonatina_ir::Inst>(
    func: &mut Function,
    block: BlockId,
    inst_data: I,
    ty: Type,
) -> ValueId {
    let mut last_phi = None;
    for inst in func.layout.iter_inst(block) {
        if func.dfg.is_phi(inst) {
            last_phi = Some(inst);
            continue;
        }
        break;
    }

    let mut cursor = if let Some(last_phi) = last_phi {
        InstInserter::at_location(CursorLocation::At(last_phi))
    } else {
        InstInserter::at_location(CursorLocation::BlockTop(block))
    };
    let inst = cursor.insert_inst_data(func, inst_data);
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty,
    });
    cursor.attach_result(func, inst, value);
    value
}

fn enum_make_of_value(func: &Function, value: ValueId) -> Option<data::EnumMake> {
    let inst = func.dfg.value_inst(value)?;
    downcast::<&data::EnumMake>(func.inst_set(), func.dfg.inst(inst)).cloned()
}

fn inst_const_index(func: &Function, v: ValueId) -> Option<u32> {
    shape::const_u32(&func.dfg, v)
}

fn equivalent_indices(func: &Function, lhs: ValueId, rhs: ValueId) -> bool {
    lhs == rhs
        || matches!(
            (inst_const_index(func, lhs), inst_const_index(func, rhs)),
            (Some(lhs), Some(rhs)) if lhs == rhs
        )
}

fn is_explicit_undef(func: &Function, v: ValueId) -> bool {
    matches!(func.dfg.value(v), Value::Undef { .. })
}

fn compute_definitely_non_undef_aggregates(func: &Function) -> SecondaryMap<ValueId, bool> {
    let mut definitely_non_undef = SecondaryMap::default();
    for value in func.dfg.value_ids() {
        let ty = func.dfg.value_ty(value);
        if shape::is_supported_aggregate_ty(func.ctx(), ty) {
            definitely_non_undef[value] = !is_explicit_undef(func, value);
        }
    }

    loop {
        let mut changed = false;
        for value in func.dfg.value_ids() {
            let ty = func.dfg.value_ty(value);
            if !shape::is_supported_aggregate_ty(func.ctx(), ty) {
                continue;
            }

            let next = aggregate_is_definitely_non_undef(func, value, &definitely_non_undef);
            if definitely_non_undef[value] != next {
                definitely_non_undef[value] = next;
                changed = true;
            }
        }
        if !changed {
            return definitely_non_undef;
        }
    }
}

fn aggregate_is_definitely_non_undef(
    func: &Function,
    value: ValueId,
    definitely_non_undef: &SecondaryMap<ValueId, bool>,
) -> bool {
    if is_explicit_undef(func, value) {
        return false;
    }

    let ty = func.dfg.value_ty(value);
    let Some(inst) = func.dfg.value_inst(value) else {
        return true;
    };

    if let Some(insert) = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst)) {
        if value_is_definitely_non_undef(func, *insert.dest(), definitely_non_undef) {
            return true;
        }

        let Some(field_count) = shape::aggregate_child_count(func.ctx(), ty) else {
            return false;
        };
        let Some(assignments) = collect_insert_assignments(func, value) else {
            return false;
        };
        return assignments.len() == field_count
            && (0..field_count).all(|idx| {
                let Some(idx_u32) = u32::try_from(idx).ok() else {
                    return false;
                };
                let Some(field) = assignments.get(&idx_u32).copied() else {
                    return false;
                };
                let Some(field_ty) = shape::aggregate_child_ty(func.ctx(), ty, idx_u32) else {
                    return false;
                };
                func.dfg.value_ty(field) == field_ty
                    && value_is_definitely_non_undef(func, field, definitely_non_undef)
            });
    }

    if let Some(phi) = downcast::<&control_flow::Phi>(func.inst_set(), func.dfg.inst(inst)) {
        return phi.args().iter().any(|&(arg, _)| arg != value)
            && phi.args().iter().all(|&(arg, _)| {
                func.dfg.value_ty(arg) == ty
                    && value_is_definitely_non_undef(func, arg, definitely_non_undef)
            });
    }

    if let Some(extract) = downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst)) {
        return value_is_definitely_non_undef(func, *extract.dest(), definitely_non_undef);
    }

    if let Some(bitcast) = downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(inst)) {
        return value_is_definitely_non_undef(func, *bitcast.from(), definitely_non_undef);
    }

    false
}

fn value_is_definitely_non_undef(
    func: &Function,
    value: ValueId,
    definitely_non_undef: &SecondaryMap<ValueId, bool>,
) -> bool {
    let ty = func.dfg.value_ty(value);
    if shape::is_supported_aggregate_ty(func.ctx(), ty) {
        definitely_non_undef[value]
    } else {
        !is_explicit_undef(func, value)
    }
}

fn is_identical_field_reinsert(
    func: &Function,
    insert: &data::InsertValue,
    definitely_non_undef: &SecondaryMap<ValueId, bool>,
) -> bool {
    if !definitely_non_undef[*insert.dest()] {
        return false;
    }

    let Some(idx) = inst_const_index(func, *insert.idx()) else {
        return false;
    };

    matches!(
        walk_insert_chain_for_field(func, *insert.dest(), idx),
        AggregateFieldLookup::Found(found) if found == *insert.value()
    ) || func
        .dfg
        .value_inst(*insert.value())
        .is_some_and(|src_inst| {
            downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(src_inst)).is_some_and(
                |extract| {
                    *extract.dest() == *insert.dest()
                        && inst_const_index(func, *extract.idx()) == Some(idx)
                },
            )
        })
}

fn walk_insert_chain_for_field(
    func: &Function,
    aggregate: ValueId,
    target_idx: u32,
) -> AggregateFieldLookup {
    if is_explicit_undef(func, aggregate) {
        let agg_ty = func.dfg.value_ty(aggregate);
        if let Some(field_ty) = shape::aggregate_child_ty(func.ctx(), agg_ty, target_idx) {
            return AggregateFieldLookup::Undef(field_ty);
        }
        return AggregateFieldLookup::Unknown;
    }

    let Some(def_inst) = func.dfg.value_inst(aggregate) else {
        return AggregateFieldLookup::BaseNeedsExtract(aggregate);
    };
    let Some(insert) = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(def_inst))
    else {
        return AggregateFieldLookup::BaseNeedsExtract(aggregate);
    };
    let Some(insert_idx) = inst_const_index(func, *insert.idx()) else {
        return AggregateFieldLookup::Unknown;
    };
    if insert_idx == target_idx {
        return AggregateFieldLookup::Found(*insert.value());
    }
    walk_insert_chain_for_field(func, *insert.dest(), target_idx)
}

fn try_reconstruct_original_aggregate(func: &Function, value: ValueId) -> Option<ValueId> {
    let agg_ty = func.dfg.value_ty(value);
    let field_count = shape::aggregate_child_count(func.ctx(), agg_ty)?;
    if field_count == 0 {
        return None;
    }

    let assignments = collect_insert_assignments(func, value)?;
    if assignments.len() != field_count {
        return None;
    }

    let mut source: Option<ValueId> = None;
    for idx in 0..field_count {
        let idx_u32 = u32::try_from(idx).ok()?;
        let field_val = *assignments.get(&idx_u32)?;
        let mut path = vec![idx_u32];
        let field_source = source_for_path_value(func, field_val, &mut path)?;
        if source.is_none() {
            source = Some(field_source);
        } else if source != Some(field_source) {
            return None;
        }
    }

    let source = source?;
    (!is_explicit_undef(func, source) && func.dfg.value_ty(source) == agg_ty).then_some(source)
}

fn collect_insert_assignments(func: &Function, value: ValueId) -> Option<FxHashMap<u32, ValueId>> {
    let mut assignments: FxHashMap<u32, ValueId> = FxHashMap::default();
    let mut current = value;
    while let Some(inst) = func.dfg.value_inst(current) {
        let Some(insert) = downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst))
        else {
            break;
        };
        let idx = inst_const_index(func, *insert.idx())?;
        assignments.entry(idx).or_insert(*insert.value());
        current = *insert.dest();
    }
    Some(assignments)
}

fn source_for_path_value(func: &Function, value: ValueId, path: &mut Vec<u32>) -> Option<ValueId> {
    if let Some(source) = extract_chain_source(func, value, path) {
        return Some(source);
    }

    let value_ty = func.dfg.value_ty(value);
    let child_count = shape::aggregate_child_count(func.ctx(), value_ty)?;
    if child_count == 0 {
        return None;
    }

    let assignments = collect_insert_assignments(func, value)?;
    if assignments.len() != child_count {
        return None;
    }

    let mut source: Option<ValueId> = None;
    for idx in 0..child_count {
        let idx_u32 = u32::try_from(idx).ok()?;
        let field_val = *assignments.get(&idx_u32)?;
        path.push(idx_u32);
        let field_source = source_for_path_value(func, field_val, path)?;
        path.pop();
        if source.is_none() {
            source = Some(field_source);
        } else if source != Some(field_source) {
            return None;
        }
    }

    source
}

fn extract_chain_source(func: &Function, mut value: ValueId, path: &[u32]) -> Option<ValueId> {
    for &idx in path.iter().rev() {
        let inst = func.dfg.value_inst(value)?;
        let extract = downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst))?;
        if inst_const_index(func, *extract.idx()) != Some(idx) {
            return None;
        }
        value = *extract.dest();
    }
    Some(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{Module, ir_writer::FuncWriter, module::FuncRef};
    use sonatina_parser::parse_module;

    fn parse_test_module(src: &str) -> Module {
        parse_module(src).expect("parse should succeed").module
    }

    fn lookup_func(module: &Module, name: &str) -> FuncRef {
        module
            .funcs()
            .into_iter()
            .find(|&func_ref| module.ctx.func_sig(func_ref, |sig| sig.name() == name))
            .expect("function should exist")
    }

    fn dump_func(module: &Module, func_ref: FuncRef) -> String {
        module.func_store.view(func_ref, |func| {
            FuncWriter::new(func_ref, func).dump_string()
        })
    }

    #[test]
    fn combine_rewrites_extracts_through_compatible_aggregate_bitcasts() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @inner = { i256 };
type @pair = { i256, i256 };
type @nested = { @inner, i256 };

func private %f(v0.@pair) -> i256 {
block0:
    v1.@nested = bitcast v0 @nested;
    v2.@inner = extract_value v1 0.i8;
    v3.i256 = extract_value v2 0.i8;
    return v3;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateCombine::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            let mut extract_count = 0;
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    let Some(extract) =
                        downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst))
                    else {
                        continue;
                    };
                    extract_count += 1;

                    if let Some(dest_inst) = func.dfg.value_inst(*extract.dest())
                        && let Some(bitcast) =
                            downcast::<&cast::Bitcast>(func.inst_set(), func.dfg.inst(dest_inst))
                    {
                        let from_ty = func.dfg.value_ty(*bitcast.from());
                        let to_ty = func.dfg.value_ty(*extract.dest());
                        assert!(
                            !shape::is_supported_aggregate_ty(func.ctx(), from_ty)
                                || !shape::is_supported_aggregate_ty(func.ctx(), to_ty),
                            "compatible aggregate bitcast should not remain directly under extract"
                        );
                    }
                }
            }
            assert_eq!(
                extract_count, 1,
                "bitcasted nested extract chain should collapse"
            );
        });
    }

    #[test]
    fn combine_folds_enum_value_queries_from_enum_make() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.i256) -> i256 {
block0:
    v1.@OptionI256 = enum.make @OptionI256 #Some (v0);
    v2.enumtag(@OptionI256) = enum.tag v1;
    v3.i1 = enum.is_variant v1 #Some;
    v4.i256 = enum.extract v1 #Some 0.i8;
    br v3 block1 block2;

block1:
    return v4;

block2:
    return 0.i256;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateCombine::default().run(func);
        });

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    assert!(
                        downcast::<&data::EnumTag>(func.inst_set(), func.dfg.inst(inst)).is_none()
                            && downcast::<&data::EnumIsVariant>(
                                func.inst_set(),
                                func.dfg.inst(inst),
                            )
                            .is_none()
                            && downcast::<&data::EnumExtract>(
                                func.inst_set(),
                                func.dfg.inst(inst),
                            )
                            .is_none(),
                        "enum value query should fold away",
                    );
                }
            }
        });
    }

    #[test]
    fn combine_folds_enum_get_tag_after_write_variant() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.i256) -> enumtag(@OptionI256) {
block0:
    v1.objref<@OptionI256> = obj.alloc @OptionI256;
    enum.write_variant v1 #Some (v0);
    v2.enumtag(@OptionI256) = enum.get_tag v1;
    return v2;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(AggregateCombine::default().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("enum.get_tag"),
            "known enum tag reads should fold away:\n{dumped}"
        );
        assert!(
            dumped.contains("return 1.enumtag(@OptionI256);"),
            "tag read should fold to the written variant:\n{dumped}"
        );
    }

    #[test]
    fn combine_folds_enum_proj_load_after_write_variant() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.i256) -> i256 {
block0:
    v1.objref<@OptionI256> = obj.alloc @OptionI256;
    enum.write_variant v1 #Some (v0);
    v2.objref<@OptionI256> = enum.assert_variant_ref v1 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    v4.i256 = obj.load v3;
    return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(AggregateCombine::default().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("enum.assert_variant_ref"),
            "redundant enum.assert_variant_ref should be removed:\n{dumped}"
        );
        assert!(
            !dumped.contains("obj.load"),
            "known enum payload load should fold away:\n{dumped}"
        );
        assert!(
            dumped.contains("return v0;"),
            "payload load should fold to the written scalar:\n{dumped}"
        );
    }

    #[test]
    fn combine_removes_overwritten_enum_set_tag() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.objref<@OptionI256>) -> enumtag(@OptionI256) {
block0:
    enum.set_tag v0 #Some;
    enum.set_tag v0 #None;
    v1.enumtag(@OptionI256) = enum.get_tag v0;
    return v1;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(AggregateCombine::default().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert_eq!(
            dumped.matches("enum.set_tag").count(),
            1,
            "overwritten tag writes should collapse:\n{dumped}"
        );
        assert!(
            dumped.contains("enum.set_tag v0 #None;"),
            "the surviving tag write should be the final one:\n{dumped}"
        );
        assert!(
            !dumped.contains("enum.get_tag"),
            "known enum tag reads should fold after tag overwrite cleanup:\n{dumped}"
        );
    }

    #[test]
    fn combine_keeps_enum_set_tag_before_same_root_phi_alias_assert() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.objref<@OptionI256>) {
block0:
    br 1.i1 block1 block2;

block1:
    jump block3;

block2:
    jump block3;

block3:
    v1.objref<@OptionI256> = phi (v0 block1) (v0 block2);
    enum.set_tag v0 #Some;
    v2.objref<@OptionI256> = enum.assert_variant_ref v1 #Some;
    enum.set_tag v0 #None;
    return;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateCombine::default().run(func);
        });

        let dumped = dump_func(&module, func_ref);
        assert_eq!(
            dumped.matches("enum.set_tag").count(),
            2,
            "aliasing reads through same-root phi values must clear pending enum writes:\n{dumped}"
        );
        assert!(
            dumped.contains("enum.assert_variant_ref v1 #Some;"),
            "the intervening alias read should remain visible:\n{dumped}"
        );
    }

    #[test]
    fn combine_folds_root_load_after_same_root_phi_alias_write_variant() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.objref<@OptionI256>) -> i256 {
block0:
    br 1.i1 block1 block2;

block1:
    jump block3;

block2:
    jump block3;

block3:
    v1.objref<@OptionI256> = phi (v0 block1) (v0 block2);
    enum.write_variant v1 #Some (7.i256);
    v2.objref<i256> = enum.proj v0 #Some 0.i8;
    v3.i256 = obj.load v2;
    return v3;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(AggregateCombine::default().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("obj.load"),
            "same-root phi aliases should preserve enum payload facts:\n{dumped}"
        );
        assert!(
            dumped.contains("return 7.i256;"),
            "writes through a phi alias should fold loads through the root:\n{dumped}"
        );
    }

    #[test]
    fn combine_folds_root_load_after_nested_assert_phi_alias_write_variant() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.objref<@OptionI256>) -> i256 {
block0:
    v1.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    br 1.i1 block1 block2;

block1:
    jump block3;

block2:
    v2.objref<@OptionI256> = enum.assert_variant_ref v1 #Some;
    jump block3;

block3:
    v3.objref<@OptionI256> = phi (v1 block1) (v2 block2);
    enum.write_variant v3 #Some (7.i256);
    v4.objref<i256> = enum.proj v0 #Some 0.i8;
    v5.i256 = obj.load v4;
    return v5;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(AggregateCombine::default().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("obj.load"),
            "mixed nested-assert phi aliases should preserve enum payload facts:\n{dumped}"
        );
        assert!(
            dumped.contains("return 7.i256;"),
            "mixed nested-assert phi aliases should canonicalize to the root:\n{dumped}"
        );
    }

    #[test]
    fn combine_does_not_fold_write_variant_through_known_plus_unknown_phi() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %mystery() -> objref<@OptionI256> {
block0:
    v10.objref<@OptionI256> = obj.alloc @OptionI256;
    return v10;
}

func private %f(v0.i1) -> i256 {
block0:
    v1.objref<@OptionI256> = obj.alloc @OptionI256;
    enum.write_variant v1 #Some (9.i256);
    br v0 block1 block2;

block1:
    jump block3;

block2:
    v2.objref<@OptionI256> = call %mystery;
    jump block3;

block3:
    v3.objref<@OptionI256> = phi (v1 block1) (v2 block2);
    enum.write_variant v3 #Some (7.i256);
    v4.objref<i256> = enum.proj v1 #Some 0.i8;
    v5.i256 = obj.load v4;
    return v5;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateCombine::default().run(func);
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            dumped.contains("obj.load"),
            "writes through known+unknown phi aliases must not fold loads through the known root:\n{dumped}"
        );
        assert!(
            !dumped.contains("return 7.i256;"),
            "known+unknown phi aliases must not be treated as exact roots:\n{dumped}"
        );
    }

    #[test]
    fn combine_folds_nested_enum_field_write_variant() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

type @Wrapper = { @OptionI256 };

func private %f() -> i256 {
block0:
    v0.objref<@Wrapper> = obj.alloc @Wrapper;
    v1.objref<@OptionI256> = obj.proj v0 0.i8;
    enum.write_variant v1 #Some (7.i256);
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.i256 = obj.load v2;
    return v3;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateCombine::default().run(func);
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("obj.load"),
            "nested enum-field writes should fold payload loads through exact slices:\n{dumped}"
        );
        assert!(
            dumped.contains("return 7.i256;"),
            "nested enum-field writes should fold to the written payload:\n{dumped}"
        );
    }

    #[test]
    fn combine_keeps_sibling_nested_enum_fields_isolated() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

type @Wrapper = { @OptionI256, @OptionI256 };

func private %f() -> i256 {
block0:
    v0.objref<@Wrapper> = obj.alloc @Wrapper;
    v1.objref<@OptionI256> = obj.proj v0 0.i8;
    v2.objref<@OptionI256> = obj.proj v0 1.i8;
    enum.write_variant v1 #Some (7.i256);
    enum.write_variant v2 #Some (9.i256);
    v3.objref<i256> = enum.proj v1 #Some 0.i8;
    v4.i256 = obj.load v3;
    return v4;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateCombine::default().run(func);
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("obj.load"),
            "writes to sibling nested enum fields must not kill exact facts for the target field:\n{dumped}"
        );
        assert!(
            dumped.contains("return 7.i256;"),
            "sibling nested enum fields must not cross-talk through the wrapper root:\n{dumped}"
        );
    }

    #[test]
    fn combine_folds_nested_enum_field_under_wrapper_argument() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

type @Wrapper = { @OptionI256 };

func private %f(v0.objref<@Wrapper>) -> i256 {
block0:
    v1.objref<@OptionI256> = obj.proj v0 0.i8;
    enum.write_variant v1 #Some (7.i256);
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    v3.i256 = obj.load v2;
    return v3;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateCombine::default().run(func);
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("obj.load"),
            "wrapper arguments should seed provenance for nested enum-field exact slices:\n{dumped}"
        );
        assert!(
            dumped.contains("return 7.i256;"),
            "nested enum-field writes through wrapper arguments should fold:\n{dumped}"
        );
    }

    #[test]
    fn combine_keeps_nested_enum_facts_through_pure_projection_phi() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

type @Wrapper = { @OptionI256 };

func private %f() -> i256 {
block0:
    v0.objref<@Wrapper> = obj.alloc @Wrapper;
    br 1.i1 block1 block2;

block1:
    v1.objref<@OptionI256> = obj.proj v0 0.i8;
    jump block3;

block2:
    v2.objref<@OptionI256> = obj.proj v0 0.i8;
    jump block3;

block3:
    v3.objref<@OptionI256> = phi (v1 block1) (v2 block2);
    enum.write_variant v3 #Some (7.i256);
    v4.objref<@OptionI256> = obj.proj v0 0.i8;
    v5.objref<i256> = enum.proj v4 #Some 0.i8;
    v6.i256 = obj.load v5;
    return v6;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateCombine::default().run(func);
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("obj.load"),
            "pure projection and phi instructions must not invalidate nested enum facts:\n{dumped}"
        );
        assert!(
            dumped.contains("return 7.i256;"),
            "pure address-building aliases should preserve exact nested enum slices:\n{dumped}"
        );
    }

    #[test]
    fn combine_removes_dead_write_to_sibling_nested_enum_field() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

type @Wrapper = { @OptionI256, @OptionI256 };

func private %f(v0.i256) -> i256 {
block0:
    v1.objref<@Wrapper> = obj.alloc @Wrapper;
    v2.objref<@OptionI256> = obj.proj v1 0.i8;
    v3.objref<@OptionI256> = obj.proj v1 1.i8;
    enum.write_variant v2 #Some (7.i256);
    enum.write_variant v3 #Some (v0);
    v4.objref<i256> = enum.proj v2 #Some 0.i8;
    v5.i256 = obj.load v4;
    return v5;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            AggregateCombine::default().run(func);
        });

        let dumped = dump_func(&module, func_ref);
        assert_eq!(
            dumped.matches("enum.write_variant").count(),
            0,
            "dead writes to sibling nested enum fields should disappear after load folding and dead-write cleanup:\n{dumped}"
        );
        assert!(
            dumped.contains("return 7.i256;"),
            "the live nested enum field must still compute the correct payload while dead sibling writes are removed:\n{dumped}"
        );
    }

    #[test]
    fn combine_tracks_branch_sensitive_enum_proj_store_load() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.objref<@OptionI256>) -> i256 {
block0:
    v1.enumtag(@OptionI256) = enum.get_tag v0;
    br_table v1 block2 (1.enumtag(@OptionI256) block1) (0.enumtag(@OptionI256) block2);

block1:
    v2.objref<@OptionI256> = enum.assert_variant_ref v0 #Some;
    v3.objref<i256> = enum.proj v2 #Some 0.i8;
    obj.store v3 7.i256;
    v4.i256 = obj.load v3;
    return v4;

block2:
    return 0.i256;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(AggregateCombine::default().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("obj.load"),
            "branch-proven enum payload store/load should fold away:\n{dumped}"
        );
        assert!(
            dumped.contains("return 7.i256;"),
            "branch-local enum payload facts should feed load folding:\n{dumped}"
        );
    }

    #[test]
    fn combine_tracks_branch_sensitive_nested_wrapper_enum_proj_store_load() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

type @Wrapper = { @OptionI256 };

func private %f(v0.objref<@Wrapper>) -> i256 {
block0:
    v1.objref<@OptionI256> = obj.proj v0 0.i8;
    v2.enumtag(@OptionI256) = enum.get_tag v1;
    br_table v2 block2 (1.enumtag(@OptionI256) block1) (0.enumtag(@OptionI256) block2);

block1:
    v3.objref<@OptionI256> = enum.assert_variant_ref v1 #Some;
    v4.objref<i256> = enum.proj v3 #Some 0.i8;
    obj.store v4 7.i256;
    v5.i256 = obj.load v4;
    return v5;

block2:
    return 0.i256;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(AggregateCombine::default().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("obj.load"),
            "branch-proven nested enum payload store/load should fold away:\n{dumped}"
        );
        assert!(
            dumped.contains("return 7.i256;"),
            "branch-local nested enum payload facts should feed load folding:\n{dumped}"
        );
    }

    #[test]
    fn combine_removes_dead_inactive_variant_payload_store() {
        let module = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

type @OptionI256 = enum {
    #None,
    #Some(i256),
};

func private %f(v0.i256) -> i256 {
block0:
    v1.objref<@OptionI256> = obj.alloc @OptionI256;
    enum.set_tag v1 #None;
    v2.objref<i256> = enum.proj v1 #Some 0.i8;
    obj.store v2 v0;
    return 0.i256;
}
"#,
        );
        let func_ref = lookup_func(&module, "f");
        module.func_store.modify(func_ref, |func| {
            assert!(AggregateCombine::default().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(
            !dumped.contains("obj.store"),
            "dead inactive-variant payload stores should be removed:\n{dumped}"
        );
        assert!(
            !dumped.contains("enum.set_tag"),
            "dead tag writes on local enums should be removed:\n{dumped}"
        );
    }
}
