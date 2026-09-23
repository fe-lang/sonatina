use std::hash::Hash;

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId,
    cfg::ControlFlowGraph,
    inst::{control_flow, data, downcast},
    module::ModuleCtx,
    types::EnumVariantRef,
};

use super::{
    object_alias::ObjectAliasFacts,
    provenance::{Projection, RootValue, exact_capture_destination},
    shape,
};

pub(crate) type RootCaptureMap<C> = FxHashMap<RootValue, Vec<C>>;

pub(crate) trait RootCapturePayload: Copy + Eq + Hash {
    fn dst_slice(self) -> shape::AggregateSlice;
}

pub(crate) enum CaptureRelevantInst<'a> {
    ObjStore(&'a data::ObjStore),
    ObjInitConst(&'a data::ObjInitConst),
    EnumSetTag(&'a data::EnumSetTag),
    EnumWriteVariant(&'a data::EnumWriteVariant),
    Call,
}

pub(crate) fn capture_relevant_inst<'a>(
    function: &'a Function,
    inst: InstId,
) -> Option<CaptureRelevantInst<'a>> {
    let inst_data = function.dfg.inst(inst);
    if let Some(obj_store) = downcast::<&data::ObjStore>(function.inst_set(), inst_data) {
        return Some(CaptureRelevantInst::ObjStore(obj_store));
    }
    if let Some(init) = downcast::<&data::ObjInitConst>(function.inst_set(), inst_data) {
        return Some(CaptureRelevantInst::ObjInitConst(init));
    }
    if let Some(enum_set_tag) = downcast::<&data::EnumSetTag>(function.inst_set(), inst_data) {
        return Some(CaptureRelevantInst::EnumSetTag(enum_set_tag));
    }
    if let Some(enum_write_variant) =
        downcast::<&data::EnumWriteVariant>(function.inst_set(), inst_data)
    {
        return Some(CaptureRelevantInst::EnumWriteVariant(enum_write_variant));
    }
    downcast::<&control_flow::Call>(function.inst_set(), inst_data)
        .map(|_| CaptureRelevantInst::Call)
}

pub(crate) fn compute_capture_states_for_blocks<C: RootCapturePayload>(
    function: &Function,
    cfg: &ControlFlowGraph,
    reachable: &SecondaryMap<BlockId, bool>,
    initial_captures: &RootCaptureMap<C>,
    mut transfer_inst: impl FnMut(InstId, &mut RootCaptureMap<C>),
) -> (SecondaryMap<BlockId, RootCaptureMap<C>>, RootCaptureMap<C>) {
    let mut block_entry_captures = SecondaryMap::default();
    let mut block_exit_captures = SecondaryMap::default();

    loop {
        let mut changed = false;

        for block in function.layout.iter_block() {
            if !reachable[block] {
                continue;
            }

            let mut entry_captures = if Some(block) == cfg.entry() {
                initial_captures.clone()
            } else {
                RootCaptureMap::default()
            };
            for &pred in cfg.preds_of(block) {
                if reachable[pred] {
                    merge_root_capture_maps(&mut entry_captures, &block_exit_captures[pred]);
                }
            }
            dedup_root_capture_map(&mut entry_captures);

            if block_entry_captures[block] != entry_captures {
                block_entry_captures[block] = entry_captures.clone();
                changed = true;
            }

            let mut exit_captures = entry_captures;
            for inst in function.layout.iter_inst(block) {
                transfer_inst(inst, &mut exit_captures);
            }
            dedup_root_capture_map(&mut exit_captures);

            if block_exit_captures[block] != exit_captures {
                block_exit_captures[block] = exit_captures;
                changed = true;
            }
        }

        if !changed {
            break;
        }
    }

    let mut exit_root_captures = RootCaptureMap::default();
    for &block in &cfg.exits {
        if reachable[block] {
            merge_root_capture_maps(&mut exit_root_captures, &block_exit_captures[block]);
        }
    }
    dedup_root_capture_map(&mut exit_root_captures);

    (block_entry_captures, exit_root_captures)
}

pub(crate) fn merge_root_capture_maps<C: RootCapturePayload>(
    dst: &mut RootCaptureMap<C>,
    src: &RootCaptureMap<C>,
) -> bool {
    let mut changed = false;
    for (&root, captures) in src {
        let entry = dst.entry(root).or_default();
        for &capture in captures {
            if entry.contains(&capture) {
                continue;
            }
            entry.push(capture);
            changed = true;
        }
    }
    changed
}

pub(crate) fn dedup_root_capture_map<C: RootCapturePayload>(root_captures: &mut RootCaptureMap<C>) {
    for captures in root_captures.values_mut() {
        let mut seen = FxHashSet::default();
        captures.retain(|capture| seen.insert(*capture));
    }
}

pub(crate) fn kill_capture_access<C: RootCapturePayload>(
    root_captures: &mut RootCaptureMap<C>,
    aliases: &ObjectAliasFacts,
    projection: Option<Projection>,
    relative_slice: Option<shape::AggregateSlice>,
) {
    let Some((root, slice)) = exact_capture_destination(projection, relative_slice) else {
        return;
    };
    let write = Projection {
        root_value: root,
        slice,
    };
    if let Some(captures) = root_captures.get_mut(&root) {
        captures.retain(|capture| {
            !aliases.exact_write_covers(
                write,
                Projection {
                    root_value: root,
                    slice: capture.dst_slice(),
                },
            )
        });
        if captures.is_empty() {
            root_captures.remove(&root);
        }
    }
}

pub(crate) fn kill_enum_variant_captures<C: RootCapturePayload>(
    root_captures: &mut RootCaptureMap<C>,
    aliases: &ObjectAliasFacts,
    ctx: &ModuleCtx,
    projection: Option<Projection>,
    variant: EnumVariantRef,
    fields: usize,
) {
    let Some(projection) = projection else {
        return;
    };
    // Selecting a variant does not erase the inactive reference slots (I11).
    if let Some(tag) = shape::enum_tag_slice(ctx, projection.slice.ty) {
        kill_capture_access(root_captures, aliases, Some(projection), Some(tag));
    }
    for field in (0..fields).filter_map(|field| u32::try_from(field).ok()) {
        if let Some(slice) =
            shape::enum_variant_field_slice(ctx, projection.slice.ty, variant, field)
        {
            kill_capture_access(root_captures, aliases, Some(projection), Some(slice));
        }
    }
}

pub(crate) fn slices_overlap_relative(
    lhs: shape::AggregateSlice,
    rhs: shape::AggregateSlice,
) -> bool {
    lhs.first_leaf < rhs.first_leaf + rhs.leaf_count
        && rhs.first_leaf < lhs.first_leaf + lhs.leaf_count
}
