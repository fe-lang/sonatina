//! StaticArena stack-object layout (allocas + spills).
//!
//! Memory model:
//! - `MemScheme::StaticArena` uses a shared base (`STATIC_BASE`) across functions.
//! - A call to a StaticArena callee `g` may clobber the prefix `[0..need_words(g))`.
//! - Any caller object live across that call must be placed at offset `>= need_words(g)`.
//!
//! Packing:
//! - Variable-sized exact packing over CFG live regions.
//! - Each object has a lower bound (`min_offset_words`) derived from call clobber constraints.

use cranelift_entity::{EntityRef, SecondaryMap, entity_impl};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};
use std::hash::Hash;

use crate::bitset::BitSet;

use super::{
    memory_plan::{FuncAnalysis, WORD_BYTES},
    provenance::{Provenance, compute_provenance},
    ptr_escape::PtrEscapeSummary,
};

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct StackObjId(u32);
entity_impl!(StackObjId);

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(crate) struct LocalObjIdx(u32);
entity_impl!(LocalObjIdx);

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub(crate) struct StableItemIdx(u32);
entity_impl!(StableItemIdx);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum StackObjKind {
    Alloca(InstId),
    Spill(ValueId),
    Shadow(InstId),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct BlockLiveSegment {
    pub(crate) block: BlockId,
    pub(crate) start_boundary: u32,
    pub(crate) end_boundary: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LiveRegion {
    pub(crate) segments: SmallVec<[BlockLiveSegment; 4]>,
    pub(crate) first_rank: u32,
    pub(crate) last_rank: u32,
}

impl LiveRegion {
    pub(crate) fn empty() -> Self {
        Self {
            segments: SmallVec::new(),
            first_rank: 0,
            last_rank: 0,
        }
    }

    pub(crate) fn sort_only(rank: u32) -> Self {
        Self {
            segments: SmallVec::new(),
            first_rank: rank,
            last_rank: rank,
        }
    }

    pub(crate) fn sort_key(&self, id: StackObjId) -> (u32, u32, u32) {
        (self.first_rank, self.last_rank, id.as_u32())
    }

    pub(crate) fn overlaps(&self, other: &Self) -> bool {
        let mut lhs = 0usize;
        let mut rhs = 0usize;
        while lhs < self.segments.len() && rhs < other.segments.len() {
            let a = self.segments[lhs];
            let b = other.segments[rhs];
            let block_cmp = a.block.as_u32().cmp(&b.block.as_u32());
            if block_cmp.is_lt() {
                lhs += 1;
                continue;
            }
            if block_cmp.is_gt() {
                rhs += 1;
                continue;
            }
            if a.end_boundary <= b.start_boundary {
                lhs += 1;
            } else if b.end_boundary <= a.start_boundary {
                rhs += 1;
            } else {
                return true;
            }
        }
        false
    }
}

#[derive(Clone, Debug)]
pub(crate) struct StackObj {
    pub(crate) id: StackObjId,
    pub(crate) kind: StackObjKind,
    pub(crate) size_words: u32,
    pub(crate) region: LiveRegion,
    pub(crate) access_weight: u64,
    pub(crate) load_count: u32,
    pub(crate) store_count: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StableReason {
    None,
    VisibleToCallee,
    RecursiveVisibility,
    UnknownLocalPointerClosure,
    #[allow(dead_code)]
    ExplicitAddressEscapeBarrier,
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub(crate) struct ObjFacts {
    pub(crate) id: StackObjId,
    pub(crate) size_words: u32,
    pub(crate) region: LiveRegion,
    pub(crate) is_alloca: bool,
    pub(crate) is_spill: bool,
    pub(crate) address_taken: bool,
    pub(crate) access_weight: u64,
    pub(crate) load_count: u32,
    pub(crate) store_count: u32,
    pub(crate) live_across_calls: SmallVec<[InstId; 4]>,
    pub(crate) visible_to_callee_at: SmallVec<[InstId; 4]>,
    pub(crate) live_across_recursive_call: bool,
    pub(crate) must_stable: bool,
    pub(crate) stable_reason: StableReason,
}

pub(crate) struct CallSiteObjects {
    pub(crate) inst: InstId,
    pub(crate) call_rank: u32,
    pub(crate) callee: FuncRef,
    pub(crate) result_count: u8,
    #[allow(dead_code)]
    pub(crate) arg_count: u8,
    pub(crate) live_across_objs: Vec<StackObjId>,
    pub(crate) callee_visible_objs: Vec<StackObjId>,
}

pub(crate) struct FuncStackObjects {
    pub(crate) objects: Vec<StackObj>,
    pub(crate) obj_facts: FxHashMap<StackObjId, ObjFacts>,
    pub(crate) obj_size_words: FxHashMap<StackObjId, u32>,
    pub(crate) alloca_ids: FxHashMap<InstId, StackObjId>,
    pub(crate) spill_obj: SecondaryMap<ValueId, Option<StackObjId>>,
    pub(crate) call_sites: Vec<CallSiteObjects>,
    pub(crate) next_obj_id: u32,
}

pub(crate) struct StaticArenaAllocCtx<'a> {
    module: &'a ModuleCtx,
    isa: &'a Evm,
    ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
}

impl<'a> StaticArenaAllocCtx<'a> {
    pub(crate) fn new(
        module: &'a ModuleCtx,
        isa: &'a Evm,
        ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
    ) -> Self {
        Self {
            module,
            isa,
            ptr_escape,
        }
    }

    pub(crate) fn compute_func_stack_objects(
        &self,
        func_ref: FuncRef,
        function: &Function,
        analysis: &FuncAnalysis,
    ) -> FuncStackObjects {
        compute_func_stack_objects(func_ref, function, self, analysis)
    }
}

#[derive(Clone, Copy, Debug)]
struct UnknownLocalPtr;

fn closure_allocas(
    roots: impl IntoIterator<Item = InstId>,
    edges: &FxHashMap<InstId, FxHashSet<InstId>>,
    unknown: &FxHashSet<InstId>,
) -> Result<FxHashSet<InstId>, UnknownLocalPtr> {
    let mut out: FxHashSet<InstId> = FxHashSet::default();
    let mut work: Vec<InstId> = Vec::new();
    for root in roots {
        if out.insert(root) {
            work.push(root);
        }
    }

    while let Some(base) = work.pop() {
        if unknown.contains(&base) {
            return Err(UnknownLocalPtr);
        }

        let Some(next) = edges.get(&base) else {
            continue;
        };
        for &child in next {
            if out.insert(child) {
                work.push(child);
            }
        }
    }

    Ok(out)
}

fn conservative_closure_allocas(
    roots: impl IntoIterator<Item = InstId>,
    edges: &FxHashMap<InstId, FxHashSet<InstId>>,
    unknown: &FxHashSet<InstId>,
    all_allocas: &FxHashSet<InstId>,
) -> (FxHashSet<InstId>, bool) {
    match closure_allocas(roots, edges, unknown) {
        Ok(allocas) => (allocas, false),
        Err(UnknownLocalPtr) => (all_allocas.clone(), true),
    }
}

pub(crate) fn compute_inst_order(
    function: &Function,
    block_order: &[BlockId],
) -> (Vec<InstId>, FxHashMap<InstId, u32>) {
    let mut blocks: Vec<BlockId> = Vec::new();
    let mut seen: FxHashSet<BlockId> = FxHashSet::default();

    for &b in block_order {
        if seen.insert(b) {
            blocks.push(b);
        }
    }

    for b in function.layout.iter_block() {
        if seen.insert(b) {
            blocks.push(b);
        }
    }

    let mut order: Vec<InstId> = Vec::new();
    let mut pos: FxHashMap<InstId, u32> = FxHashMap::default();
    let mut next: u32 = 0;
    for b in blocks {
        for inst in function.layout.iter_inst(b) {
            pos.insert(inst, next);
            order.push(inst);
            next = next.checked_add(1).expect("instruction position overflow");
        }
    }

    (order, pos)
}

fn compute_block_order(function: &Function, block_order: &[BlockId]) -> Vec<BlockId> {
    let mut blocks = Vec::new();
    let mut seen: FxHashSet<BlockId> = FxHashSet::default();
    for &block in block_order {
        if seen.insert(block) {
            blocks.push(block);
        }
    }
    for block in function.layout.iter_block() {
        if seen.insert(block) {
            blocks.push(block);
        }
    }
    blocks
}

#[derive(Default)]
struct ExpandedAllocaRoots {
    allocas: FxHashSet<InstId>,
    hit_unknown: bool,
}

struct AllocaClosureCtx<'a> {
    edges: &'a FxHashMap<InstId, FxHashSet<InstId>>,
    unknown: &'a FxHashSet<InstId>,
    all_allocas: &'a FxHashSet<InstId>,
}

impl AllocaClosureCtx<'_> {
    fn expand_roots(&self, roots: impl IntoIterator<Item = InstId>) -> ExpandedAllocaRoots {
        let (allocas, hit_unknown) =
            conservative_closure_allocas(roots, self.edges, self.unknown, self.all_allocas);
        ExpandedAllocaRoots {
            allocas,
            hit_unknown,
        }
    }
}

#[derive(Default)]
struct ObjectEventIndex {
    phi_defs: SecondaryMap<BlockId, BitSet<LocalObjIdx>>,
    edge_phi_uses: FxHashMap<(BlockId, BlockId), BitSet<LocalObjIdx>>,
    local_uses: SecondaryMap<InstId, BitSet<LocalObjIdx>>,
    local_defs: SecondaryMap<InstId, BitSet<LocalObjIdx>>,
    block_inst_count: SecondaryMap<BlockId, u32>,
    block_rank_base: SecondaryMap<BlockId, u32>,
    inst_block: FxHashMap<InstId, BlockId>,
    inst_index_in_block: FxHashMap<InstId, u32>,
}

struct ObjectEventBuildCtx<'a, 'b> {
    analysis: &'a FuncAnalysis,
    isa: &'a Evm,
    prov: &'a SecondaryMap<ValueId, Provenance>,
    spill_local_by_value: &'a SecondaryMap<ValueId, Option<LocalObjIdx>>,
    alloca_local_by_inst: &'a FxHashMap<InstId, LocalObjIdx>,
    closure: &'a AllocaClosureCtx<'b>,
    unknown_barrier_objs: &'a mut FxHashSet<StackObjId>,
    obj_id_by_local: &'a [StackObjId],
}

impl ObjectEventIndex {
    fn ensure_block(&mut self, block: BlockId) {
        let _ = &mut self.phi_defs[block];
        let _ = &mut self.block_inst_count[block];
        let _ = &mut self.block_rank_base[block];
    }

    fn ensure_inst(&mut self, inst: InstId) {
        let _ = &mut self.local_uses[inst];
        let _ = &mut self.local_defs[inst];
    }

    fn boundary_rank(&self, block: BlockId, boundary_idx: u32) -> u32 {
        self.block_rank_base[block]
            .checked_add(boundary_idx)
            .expect("boundary rank overflow")
    }
}

#[derive(Default)]
struct ObjectBlockLiveness {
    live_in: SecondaryMap<BlockId, BitSet<LocalObjIdx>>,
    live_out: SecondaryMap<BlockId, BitSet<LocalObjIdx>>,
}

fn seed_object_event_metadata(function: &Function, block_order: &[BlockId]) -> ObjectEventIndex {
    let mut events = ObjectEventIndex::default();
    let mut next_rank = 0u32;
    for &block in block_order {
        events.ensure_block(block);
        events.block_rank_base[block] = next_rank;

        let mut inst_count = 0u32;
        for (inst_index, inst) in function.layout.iter_inst(block).enumerate() {
            let inst_index = inst_index as u32;
            events.ensure_inst(inst);
            events.inst_block.insert(inst, block);
            events.inst_index_in_block.insert(inst, inst_index);
            inst_count = inst_index
                .checked_add(1)
                .expect("block instruction count overflow");
        }
        events.block_inst_count[block] = inst_count;
        next_rank = next_rank
            .checked_add(inst_count.checked_add(1).expect("block boundary overflow"))
            .expect("block rank overflow");
    }
    events
}

fn add_value_alloca_uses(
    uses: &mut BitSet<LocalObjIdx>,
    value: ValueId,
    prov: &SecondaryMap<ValueId, Provenance>,
    closure: &AllocaClosureCtx<'_>,
    alloca_local_by_inst: &FxHashMap<InstId, LocalObjIdx>,
    unknown_barrier_objs: &mut FxHashSet<StackObjId>,
    obj_id_by_local: &[StackObjId],
) {
    let roots: Vec<_> = prov[value].alloca_insts().collect();
    if roots.is_empty() {
        return;
    }
    let expanded = closure.expand_roots(roots);
    for alloca in expanded.allocas {
        if let Some(&local_idx) = alloca_local_by_inst.get(&alloca) {
            uses.insert(local_idx);
            if expanded.hit_unknown {
                unknown_barrier_objs.insert(obj_id_by_local[local_idx.as_u32() as usize]);
            }
        }
    }
}

fn build_object_event_index(
    function: &Function,
    block_order: &[BlockId],
    ctx: &mut ObjectEventBuildCtx<'_, '_>,
) -> ObjectEventIndex {
    let mut events = seed_object_event_metadata(function, block_order);

    for &block in block_order {
        for inst in function.layout.iter_inst(block) {
            let resolved = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));
            if let EvmInstKind::Phi(phi) = resolved {
                for &result in function.dfg.inst_results(inst) {
                    let value = ctx.analysis.canonicalize_value(result);
                    if let Some(local_idx) = ctx.spill_local_by_value[value] {
                        events.phi_defs[block].insert(local_idx);
                    }
                }
                for (value, pred) in phi.args().iter() {
                    let raw_value = *value;
                    let value = ctx.analysis.canonicalize_value(raw_value);
                    if let Some(local_idx) = ctx.spill_local_by_value[value] {
                        events
                            .edge_phi_uses
                            .entry((*pred, block))
                            .or_default()
                            .insert(local_idx);
                    }

                    let edge_uses = events.edge_phi_uses.entry((*pred, block)).or_default();
                    add_value_alloca_uses(
                        edge_uses,
                        raw_value,
                        ctx.prov,
                        ctx.closure,
                        ctx.alloca_local_by_inst,
                        ctx.unknown_barrier_objs,
                        ctx.obj_id_by_local,
                    );
                }
                continue;
            }

            for &result in function.dfg.inst_results(inst) {
                let value = ctx.analysis.canonicalize_value(result);
                if let Some(local_idx) = ctx.spill_local_by_value[value] {
                    events.local_defs[inst].insert(local_idx);
                }
            }

            if matches!(resolved, EvmInstKind::Alloca(_))
                && let Some(&local_idx) = ctx.alloca_local_by_inst.get(&inst)
            {
                events.local_defs[inst].insert(local_idx);
            }

            function.dfg.inst(inst).for_each_value(&mut |value| {
                let value = ctx.analysis.canonicalize_value(value);
                if let Some(local_idx) = ctx.spill_local_by_value[value] {
                    events.local_uses[inst].insert(local_idx);
                }
                add_value_alloca_uses(
                    &mut events.local_uses[inst],
                    value,
                    ctx.prov,
                    ctx.closure,
                    ctx.alloca_local_by_inst,
                    ctx.unknown_barrier_objs,
                    ctx.obj_id_by_local,
                );
            });
        }
    }

    events
}

fn reverse_scan_block_non_phi(
    function: &Function,
    block: BlockId,
    live_out: &BitSet<LocalObjIdx>,
    events: &ObjectEventIndex,
) -> BitSet<LocalObjIdx> {
    let mut live = live_out.clone();
    let insts: Vec<_> = function.layout.iter_inst(block).collect();
    for inst in insts.into_iter().rev() {
        if function.dfg.is_phi(inst) {
            continue;
        }
        live.difference_with(&events.local_defs[inst]);
        live.union_with(&events.local_uses[inst]);
    }
    live
}

fn solve_object_block_liveness(
    function: &Function,
    cfg: &ControlFlowGraph,
    block_order: &[BlockId],
    events: &ObjectEventIndex,
) -> ObjectBlockLiveness {
    let mut out = ObjectBlockLiveness::default();
    for &block in block_order {
        let _ = &mut out.live_in[block];
        let _ = &mut out.live_out[block];
    }

    let mut changed = true;
    while changed {
        changed = false;
        for &block in block_order.iter().rev() {
            let mut live_out = BitSet::default();
            for &succ in cfg.succs_as_slice(block) {
                let mut edge_live = out.live_in[succ].clone();
                edge_live.difference_with(&events.phi_defs[succ]);
                if let Some(phi_uses) = events.edge_phi_uses.get(&(block, succ)) {
                    edge_live.union_with(phi_uses);
                }
                live_out.union_with(&edge_live);
            }

            let live_in = reverse_scan_block_non_phi(function, block, &live_out, events);
            if live_out != out.live_out[block] || live_in != out.live_in[block] {
                out.live_out[block] = live_out;
                out.live_in[block] = live_in;
                changed = true;
            }
        }
    }

    out
}

fn build_block_boundary_live_sets(
    function: &Function,
    block: BlockId,
    block_live: &ObjectBlockLiveness,
    events: &ObjectEventIndex,
) -> Vec<BitSet<LocalObjIdx>> {
    let insts: Vec<_> = function.layout.iter_inst(block).collect();
    let mut boundary_live = vec![BitSet::default(); insts.len().saturating_add(1)];
    boundary_live[insts.len()] = block_live.live_out[block].clone();

    let mut live = block_live.live_out[block].clone();
    for inst in insts.into_iter().rev() {
        if function.dfg.is_phi(inst) {
            continue;
        }
        let boundary_idx = events.inst_index_in_block[&inst] as usize;
        live.difference_with(&events.local_defs[inst]);
        live.union_with(&events.local_uses[inst]);
        boundary_live[boundary_idx] = live.clone();
    }

    boundary_live
}

fn push_region_segment(
    regions: &mut [LiveRegion],
    events: &ObjectEventIndex,
    local_idx: LocalObjIdx,
    block: BlockId,
    start_boundary: u32,
    end_boundary: u32,
) {
    if start_boundary == end_boundary {
        return;
    }

    let region = &mut regions[local_idx.as_u32() as usize];
    region.segments.push(BlockLiveSegment {
        block,
        start_boundary,
        end_boundary,
    });
    let start_rank = events.boundary_rank(block, start_boundary);
    let end_rank = events.boundary_rank(block, end_boundary);
    if region.segments.len() == 1 {
        region.first_rank = start_rank;
        region.last_rank = end_rank;
    } else {
        region.first_rank = region.first_rank.min(start_rank);
        region.last_rank = region.last_rank.max(end_rank);
    }
}

fn coalesce_region_segments(region: &mut LiveRegion) {
    if region.segments.is_empty() {
        return;
    }
    region
        .segments
        .sort_unstable_by_key(|seg| (seg.block.as_u32(), seg.start_boundary, seg.end_boundary));
    let mut coalesced = SmallVec::<[BlockLiveSegment; 4]>::new();
    for segment in region.segments.drain(..) {
        if let Some(last) = coalesced.last_mut()
            && last.block == segment.block
            && last.end_boundary == segment.start_boundary
        {
            last.end_boundary = segment.end_boundary;
        } else {
            coalesced.push(segment);
        }
    }
    region.segments = coalesced;
}

fn emit_regions(
    function: &Function,
    block_order: &[BlockId],
    events: &ObjectEventIndex,
    block_live: &ObjectBlockLiveness,
    object_count: usize,
) -> Vec<LiveRegion> {
    let mut regions = vec![LiveRegion::empty(); object_count];
    let mut open = vec![None; object_count];

    for &block in block_order {
        open.fill(None);
        let boundary_live = build_block_boundary_live_sets(function, block, block_live, events);
        let mut active = BitSet::default();
        let block_inst_count = events.block_inst_count[block];

        for boundary_idx in 0..block_inst_count {
            let current = &boundary_live[boundary_idx as usize];
            for local_idx in BitSet::difference(&active, current).iter() {
                if let Some(start_boundary) = open[local_idx.as_u32() as usize].take() {
                    push_region_segment(
                        &mut regions,
                        events,
                        local_idx,
                        block,
                        start_boundary,
                        boundary_idx,
                    );
                }
            }
            for local_idx in BitSet::difference(current, &active).iter() {
                open[local_idx.as_u32() as usize] = Some(boundary_idx);
            }
            active = current.clone();
        }

        for local_idx in active.iter() {
            if let Some(start_boundary) = open[local_idx.as_u32() as usize].take() {
                push_region_segment(
                    &mut regions,
                    events,
                    local_idx,
                    block,
                    start_boundary,
                    block_inst_count,
                );
            }
        }
    }

    for region in &mut regions {
        coalesce_region_segments(region);
    }
    regions
}

pub(crate) fn compute_func_stack_objects(
    func_ref: FuncRef,
    function: &Function,
    ctx: &StaticArenaAllocCtx<'_>,
    analysis: &FuncAnalysis,
) -> FuncStackObjects {
    let block_order = compute_block_order(function, &analysis.block_order);
    let (inst_order, _inst_pos) = compute_inst_order(function, &analysis.block_order);
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    let prov_info = compute_provenance(function, ctx.module, ctx.isa, |callee| {
        ctx.ptr_escape
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| conservative_unknown_ptr_summary(ctx.module, callee))
    });
    let prov = &prov_info.value;

    let mut local_edges: FxHashMap<InstId, FxHashSet<InstId>> = FxHashMap::default();
    let mut local_unknown: FxHashSet<InstId> = FxHashSet::default();
    for (&base, stored) in &prov_info.local_mem {
        if stored.is_unknown_ptr() {
            local_unknown.insert(base);
            continue;
        }
        for child in stored.alloca_insts() {
            local_edges.entry(base).or_default().insert(child);
        }
    }

    let escaping_sites =
        compute_escaping_allocas(function, ctx.module, ctx.isa, ctx.ptr_escape, prov);
    if !escaping_sites.is_empty() {
        panic!(
            "{}",
            render_alloca_escapes(ctx.module, func_ref, escaping_sites)
        );
    }

    let mut spill_obj: SecondaryMap<ValueId, Option<StackObjId>> = SecondaryMap::new();
    for v in function.dfg.value_ids() {
        let _ = &mut spill_obj[v];
    }

    let mut spilled_values: BitSet<ValueId> = BitSet::default();
    for (v, obj) in analysis.alloc.spill_obj.iter() {
        if analysis.alloc.scratch_slot_of_value[v].is_some() {
            continue;
        }
        if obj.is_some() {
            spilled_values.insert(v);
            spill_obj[v] = *obj;
        }
    }

    let mut objects: Vec<StackObj> = Vec::new();
    for v in spilled_values.iter() {
        let id = spill_obj[v].expect("spilled value missing stack object id");
        objects.push(StackObj {
            id,
            kind: StackObjKind::Spill(v),
            size_words: 1,
            region: LiveRegion::empty(),
            access_weight: 0,
            load_count: 0,
            store_count: 0,
        });
    }

    let mut next_id: u32 = analysis
        .alloc
        .spill_obj
        .values()
        .filter_map(|o| *o)
        .map(|id| id.as_u32())
        .max()
        .map_or(0, |n| n.checked_add(1).expect("stack object id overflow"));

    let mut alloca_ids: FxHashMap<InstId, StackObjId> = FxHashMap::default();
    for &inst in &inst_order {
        let EvmInstKind::Alloca(alloca) = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst))
        else {
            continue;
        };

        let size_bytes: u32 = ctx
            .isa
            .type_layout()
            .size_of(*alloca.ty(), ctx.module)
            .expect("alloca has invalid type") as u32;
        let size_words = size_bytes.div_ceil(WORD_BYTES);

        let id = StackObjId::new(next_id as usize);
        next_id = next_id.checked_add(1).expect("stack object id overflow");
        alloca_ids.insert(inst, id);

        objects.push(StackObj {
            id,
            kind: StackObjKind::Alloca(inst),
            size_words,
            region: LiveRegion::empty(),
            access_weight: 0,
            load_count: 0,
            store_count: 0,
        });
    }
    let all_allocas: FxHashSet<InstId> = alloca_ids.keys().copied().collect();

    let mut obj_index: FxHashMap<StackObjId, usize> = FxHashMap::default();
    for (idx, obj) in objects.iter().enumerate() {
        obj_index.insert(obj.id, idx);
    }

    let mut spill_local_by_value: SecondaryMap<ValueId, Option<LocalObjIdx>> = SecondaryMap::new();
    for value in function.dfg.value_ids() {
        let _ = &mut spill_local_by_value[value];
    }
    for value in spilled_values.iter() {
        let obj = spill_obj[value].expect("spilled value missing stack object id");
        spill_local_by_value[value] = Some(LocalObjIdx::new(obj_index[&obj]));
    }
    let mut alloca_local_by_inst: FxHashMap<InstId, LocalObjIdx> = FxHashMap::default();
    for (&inst, &id) in &alloca_ids {
        alloca_local_by_inst.insert(inst, LocalObjIdx::new(obj_index[&id]));
    }
    let obj_id_by_local: Vec<StackObjId> = objects.iter().map(|obj| obj.id).collect();

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));
            match data {
                EvmInstKind::Mload(mload) => {
                    for base in prov[*mload.addr()].alloca_insts() {
                        if let Some(&id) = alloca_ids.get(&base)
                            && let Some(obj) =
                                obj_index.get(&id).and_then(|idx| objects.get_mut(*idx))
                        {
                            obj.load_count = obj.load_count.saturating_add(1);
                        }
                    }
                }
                EvmInstKind::Mstore(mstore) => {
                    for base in prov[*mstore.addr()].alloca_insts() {
                        if let Some(&id) = alloca_ids.get(&base)
                            && let Some(obj) =
                                obj_index.get(&id).and_then(|idx| objects.get_mut(*idx))
                        {
                            obj.store_count = obj.store_count.saturating_add(1);
                        }
                    }
                }
                _ => {}
            }

            function.dfg.inst(inst).for_each_value(&mut |v| {
                let v = analysis.canonicalize_value(v);
                if let Some(id) = spill_obj[v]
                    && let Some(obj) = obj_index.get(&id).and_then(|idx| objects.get_mut(*idx))
                {
                    obj.access_weight = obj.access_weight.saturating_add(1);
                }
                for base in prov[v].alloca_insts() {
                    if let Some(&id) = alloca_ids.get(&base)
                        && let Some(obj) = obj_index.get(&id).and_then(|idx| objects.get_mut(*idx))
                    {
                        obj.access_weight = obj.access_weight.saturating_add(1);
                    }
                }
            });
        }
    }

    for obj in &mut objects {
        obj.access_weight = obj
            .access_weight
            .saturating_add(u64::from(obj.load_count).saturating_mul(2))
            .saturating_add(u64::from(obj.store_count).saturating_mul(2));
    }

    let mut address_taken_allocas: FxHashSet<InstId> = FxHashSet::default();
    for (&base, stored) in &prov_info.local_mem {
        address_taken_allocas.insert(base);
        for child in stored.alloca_insts() {
            address_taken_allocas.insert(child);
        }
    }
    for edges in local_edges.values() {
        for &child in edges {
            address_taken_allocas.insert(child);
        }
    }
    for &base in &local_unknown {
        address_taken_allocas.insert(base);
    }

    let mut unknown_barrier_objs: FxHashSet<StackObjId> = FxHashSet::default();
    let closure = AllocaClosureCtx {
        edges: &local_edges,
        unknown: &local_unknown,
        all_allocas: &all_allocas,
    };
    let mut event_ctx = ObjectEventBuildCtx {
        analysis,
        isa: ctx.isa,
        prov,
        spill_local_by_value: &spill_local_by_value,
        alloca_local_by_inst: &alloca_local_by_inst,
        closure: &closure,
        unknown_barrier_objs: &mut unknown_barrier_objs,
        obj_id_by_local: &obj_id_by_local,
    };
    let events = build_object_event_index(function, &block_order, &mut event_ctx);
    let block_live = solve_object_block_liveness(function, &cfg, &block_order, &events);
    let regions = emit_regions(function, &block_order, &events, &block_live, objects.len());
    for (idx, region) in regions.into_iter().enumerate() {
        objects[idx].region = region;
    }

    let mut call_sites: Vec<CallSiteObjects> = Vec::new();
    for &block in &block_order {
        let boundary_live = build_block_boundary_live_sets(function, block, &block_live, &events);
        for inst in function.layout.iter_inst(block) {
            let Some(call) = function.dfg.cast_call(inst) else {
                continue;
            };

            let mut live_across =
                boundary_live[events.inst_index_in_block[&inst] as usize + 1].clone();
            live_across.difference_with(&events.local_defs[inst]);
            let mut live_across_objs: Vec<StackObjId> = live_across
                .iter()
                .map(|local_idx| obj_id_by_local[local_idx.as_u32() as usize])
                .collect();
            live_across_objs.sort_unstable_by_key(|id| id.as_u32());

            let mut visible_objs: FxHashSet<StackObjId> = FxHashSet::default();
            let mut roots: FxHashSet<InstId> = FxHashSet::default();
            for &arg in call.args() {
                for base in prov[arg].alloca_insts() {
                    roots.insert(base);
                }
            }
            let expanded = closure.expand_roots(roots.iter().copied());
            for alloca in expanded.allocas {
                if let Some(&id) = alloca_ids.get(&alloca) {
                    visible_objs.insert(id);
                    if expanded.hit_unknown {
                        unknown_barrier_objs.insert(id);
                    }
                }
            }
            let mut callee_visible_objs: Vec<StackObjId> = visible_objs.into_iter().collect();
            callee_visible_objs.sort_unstable_by_key(|id| id.as_u32());
            call_sites.push(CallSiteObjects {
                inst,
                call_rank: events.boundary_rank(block, events.inst_index_in_block[&inst]),
                callee: *call.callee(),
                result_count: u8::try_from(function.dfg.inst_results(inst).len())
                    .expect("call result count too large"),
                arg_count: u8::try_from(call.args().len()).expect("call arg count too large"),
                live_across_objs,
                callee_visible_objs,
            });
        }
    }

    let mut obj_size_words: FxHashMap<StackObjId, u32> = FxHashMap::default();
    for obj in &objects {
        obj_size_words.insert(obj.id, obj.size_words);
    }

    let mut obj_facts: FxHashMap<StackObjId, ObjFacts> = FxHashMap::default();
    for obj in &objects {
        let address_taken =
            matches!(obj.kind, StackObjKind::Alloca(inst) if address_taken_allocas.contains(&inst));
        obj_facts.insert(
            obj.id,
            ObjFacts {
                id: obj.id,
                size_words: obj.size_words,
                region: obj.region.clone(),
                is_alloca: matches!(obj.kind, StackObjKind::Alloca(_)),
                is_spill: matches!(obj.kind, StackObjKind::Spill(_)),
                address_taken,
                access_weight: obj.access_weight,
                load_count: obj.load_count,
                store_count: obj.store_count,
                live_across_calls: SmallVec::new(),
                visible_to_callee_at: SmallVec::new(),
                live_across_recursive_call: false,
                must_stable: false,
                stable_reason: StableReason::None,
            },
        );
    }
    for call in &call_sites {
        for &obj in &call.live_across_objs {
            let facts = obj_facts
                .get_mut(&obj)
                .unwrap_or_else(|| panic!("missing object facts for obj {}", obj.as_u32()));
            if !facts.live_across_calls.contains(&call.inst) {
                facts.live_across_calls.push(call.inst);
            }
        }
        for &obj in &call.callee_visible_objs {
            let facts = obj_facts
                .get_mut(&obj)
                .unwrap_or_else(|| panic!("missing object facts for obj {}", obj.as_u32()));
            if !facts.visible_to_callee_at.contains(&call.inst) {
                facts.visible_to_callee_at.push(call.inst);
            }
            facts.must_stable = true;
            facts.stable_reason = StableReason::VisibleToCallee;
        }
    }
    for obj in unknown_barrier_objs {
        let facts = obj_facts
            .get_mut(&obj)
            .unwrap_or_else(|| panic!("missing object facts for obj {}", obj.as_u32()));
        facts.must_stable = true;
        if matches!(facts.stable_reason, StableReason::None) {
            facts.stable_reason = StableReason::UnknownLocalPointerClosure;
        }
    }

    FuncStackObjects {
        objects,
        obj_facts,
        obj_size_words,
        alloca_ids,
        spill_obj,
        call_sites,
        next_obj_id: next_id,
    }
}

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

fn conservative_unknown_ptr_summary(module: &ModuleCtx, func_ref: FuncRef) -> PtrEscapeSummary {
    PtrEscapeSummary::conservative_unknown_ctx(module, func_ref)
}

fn compute_escaping_allocas(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> FxHashMap<InstId, Vec<AllocaEscapeSite>> {
    let mut escaping: FxHashMap<InstId, Vec<AllocaEscapeSite>> = FxHashMap::default();

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            match data {
                EvmInstKind::Return(_) => {
                    let Some(ret_args) = function.dfg.return_args(inst) else {
                        continue;
                    };
                    for &ret_val in ret_args {
                        for base in prov[ret_val].alloca_insts() {
                            escaping
                                .entry(base)
                                .or_default()
                                .push(AllocaEscapeSite::Return {
                                    inst,
                                    value: ret_val,
                                });
                        }
                    }
                }
                EvmInstKind::Mstore(mstore) => {
                    let addr = *mstore.addr();
                    if prov[addr].is_local_addr() {
                        continue;
                    }

                    let val = *mstore.value();
                    for base in prov[val].alloca_insts() {
                        escaping
                            .entry(base)
                            .or_default()
                            .push(AllocaEscapeSite::NonLocalStore {
                                inst,
                                addr,
                                value: val,
                            });
                    }
                }
                EvmInstKind::Call(call) => {
                    let callee = *call.callee();
                    let callee_sum = ptr_escape
                        .get(&callee)
                        .cloned()
                        .unwrap_or_else(|| conservative_unknown_ptr_summary(module, callee));
                    for (idx, &arg) in call.args().iter().enumerate() {
                        if idx < callee_sum.arg_may_escape.len() && callee_sum.arg_may_escape[idx] {
                            for base in prov[arg].alloca_insts() {
                                escaping
                                    .entry(base)
                                    .or_default()
                                    .push(AllocaEscapeSite::CallArg {
                                        inst,
                                        callee,
                                        arg_index: idx,
                                        value: arg,
                                    });
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    escaping
}

#[derive(Clone, Debug)]
enum AllocaEscapeSite {
    Return {
        inst: InstId,
        value: ValueId,
    },
    NonLocalStore {
        inst: InstId,
        addr: ValueId,
        value: ValueId,
    },
    CallArg {
        inst: InstId,
        callee: FuncRef,
        arg_index: usize,
        value: ValueId,
    },
}

impl AllocaEscapeSite {
    fn escape_inst(&self) -> InstId {
        match self {
            AllocaEscapeSite::Return { inst, .. }
            | AllocaEscapeSite::NonLocalStore { inst, .. }
            | AllocaEscapeSite::CallArg { inst, .. } => *inst,
        }
    }

    fn derived_value(&self) -> ValueId {
        match self {
            AllocaEscapeSite::Return { value, .. }
            | AllocaEscapeSite::NonLocalStore { value, .. }
            | AllocaEscapeSite::CallArg { value, .. } => *value,
        }
    }

    fn render(&self, module: &ModuleCtx) -> String {
        match self {
            AllocaEscapeSite::Return { inst, value } => {
                format!("return of v{} at inst {}", value.as_u32(), inst.as_u32())
            }
            AllocaEscapeSite::NonLocalStore { inst, addr, value } => format!(
                "non-local store of v{} to addr v{} at inst {}",
                value.as_u32(),
                addr.as_u32(),
                inst.as_u32()
            ),
            AllocaEscapeSite::CallArg {
                inst,
                callee,
                arg_index,
                value,
            } => {
                let callee_name = module.func_sig(*callee, |sig| sig.name().to_string());
                format!(
                    "call arg {arg_index} v{} to %{callee_name} at inst {}",
                    value.as_u32(),
                    inst.as_u32()
                )
            }
        }
    }
}

fn render_alloca_escapes(
    module: &ModuleCtx,
    func_ref: FuncRef,
    escaping_sites: FxHashMap<InstId, Vec<AllocaEscapeSite>>,
) -> String {
    let name = module.func_sig(func_ref, |sig| sig.name().to_string());
    let mut allocas: Vec<(InstId, Vec<AllocaEscapeSite>)> = escaping_sites.into_iter().collect();
    allocas.sort_unstable_by_key(|(inst, _)| inst.as_u32());

    let mut msg = String::new();
    msg.push_str(&format!("alloca escapes in {name}:\n"));
    for (alloca_inst, mut sites) in allocas {
        sites.sort_unstable_by_key(|s| (s.escape_inst().as_u32(), s.derived_value().as_u32()));
        msg.push_str(&format!("  alloca inst {}:\n", alloca_inst.as_u32()));
        for site in sites {
            msg.push_str("    - ");
            msg.push_str(&site.render(module));
            msg.push('\n');
        }
    }
    msg
}

#[cfg(any())]
mod old_tests {
    use super::*;
    use crate::{
        critical_edge::CriticalEdgeSplitter,
        domtree::DomTree,
        isa::evm::{EvmBackend, canonicalize_alias_value},
        liveness::{InstLiveness, Liveness},
        stackalloc::StackifyBuilder,
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    fn test_isa() -> Evm {
        Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        })
    }

    #[test]
    fn aliased_spill_is_marked_live_out_at_internal_call() {
        let parsed = parse_module(include_str!(
            "../../../tests/fixtures/fe_lazy_merkle_proof_element_1_pass6.sntn"
        ))
        .expect("module parses");
        let funcs = parsed.module.funcs();
        let isa = test_isa();
        let backend = EvmBackend::new(test_isa());
        let ptr_escape =
            super::super::ptr_escape::compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func| {
                parsed.module.ctx.func_sig(func, |sig| {
                    sig.name() == "lazyimtdata_hb575fd00dcf9c59f_merkle_proof_elements"
                })
            })
            .expect("merkle_proof_elements exists");

        let mut analysis = None;
        parsed.module.func_store.modify(func_ref, |function| {
            let mut cfg = sonatina_ir::cfg::ControlFlowGraph::new();
            cfg.compute(function);
            CriticalEdgeSplitter::new().run(function, &mut cfg);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut inst_liveness = InstLiveness::new();
            inst_liveness.compute(function, &cfg, &liveness);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let value_aliases =
                backend.compute_stackify_value_aliases(function, &parsed.module.ctx);

            let mut stack_liveness = Liveness::new();
            stack_liveness.compute_with_value_normalizer(function, &cfg, |value| {
                canonicalize_alias_value(&value_aliases, value)
            });

            let alloc = StackifyBuilder::new(function, &cfg, &dom, &stack_liveness, 16)
                .with_value_aliases(&value_aliases)
                .compute();

            analysis = Some(FuncAnalysis {
                alloc,
                inst_liveness,
                block_order: dom.rpo().to_vec(),
                value_aliases,
            });
        });
        let analysis = analysis.expect("analysis computed");

        let spill_value = analysis.canonicalize_value(
            parsed
                .debug
                .value(func_ref, "v5")
                .expect("aliased pointer value exists"),
        );
        let spill_obj = analysis.alloc.spill_obj[spill_value].expect("spill object exists");

        let alloc_ctx = StaticArenaAllocCtx::new(&parsed.module.ctx, &isa, &ptr_escape);
        let stack = parsed.module.func_store.view(func_ref, |function| {
            alloc_ctx.compute_func_stack_objects(func_ref, function, &analysis)
        });

        let call = stack
            .call_sites
            .iter()
            .find(|call| {
                parsed.module.ctx.func_sig(call.callee, |sig| {
                    sig.name() == "lazyimtdata_hb575fd00dcf9c59f_levels_for_root"
                })
            })
            .expect("levels_for_root call exists");

        assert!(
            call.live_out_objs.contains(&spill_obj),
            "canonical spill object for aliased pointer should be live across the internal call"
        );
    }

    #[test]
    fn presorted_packer_matches_sorted_packer() {
        let mut unsorted = vec![
            PackedObject {
                id: StackObjId::new(3),
                size_words: 2,
                interval: LiveInterval { start: 4, end: 9 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(1),
                size_words: 1,
                interval: LiveInterval { start: 0, end: 2 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(2),
                size_words: 3,
                interval: LiveInterval { start: 1, end: 6 },
                min_offset_words: 1,
            },
            PackedObject {
                id: StackObjId::new(4),
                size_words: 1,
                interval: LiveInterval { start: 6, end: 6 },
                min_offset_words: 0,
            },
        ];
        let (sorted_offsets, sorted_words) = pack_objects(&mut unsorted);

        let mut presorted = unsorted.clone();
        presorted
            .sort_unstable_by_key(|obj| (obj.interval.start, obj.interval.end, obj.id.as_u32()));
        let (presorted_offsets, presorted_words) = pack_objects_presorted(&presorted);
        let peak_words = pack_objects_peak_presorted(&presorted);

        assert_eq!(presorted_offsets, sorted_offsets);
        assert_eq!(presorted_words, sorted_words);
        assert_eq!(peak_words, sorted_words);
    }

    #[test]
    fn zero_min_peak_packer_matches_generic_peak() {
        let mut objects = vec![
            PackedObject {
                id: StackObjId::new(5),
                size_words: 4,
                interval: LiveInterval { start: 5, end: 9 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(2),
                size_words: 2,
                interval: LiveInterval { start: 0, end: 4 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(7),
                size_words: 3,
                interval: LiveInterval { start: 2, end: 6 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(8),
                size_words: 1,
                interval: LiveInterval { start: 6, end: 6 },
                min_offset_words: 0,
            },
        ];
        objects.sort_unstable_by_key(|obj| (obj.interval.start, obj.interval.end, obj.id.as_u32()));

        let generic_peak = pack_objects_peak_presorted(&objects);
        let mut workspace = PeakPackWorkspace::default();
        let schedule = zero_min_release_schedule(&objects);
        let specialized_peak = pack_zero_min_offset_peak_ranked(
            &mut workspace,
            &schedule,
            zero_min_ranked_items(&objects),
            objects.len(),
        );

        assert_eq!(specialized_peak, generic_peak);
    }

    #[test]
    fn zero_min_peak_packer_matches_generic_peak_with_tied_bounds() {
        let objects = [
            PackedObject {
                id: StackObjId::new(1),
                size_words: 3,
                interval: LiveInterval { start: 0, end: 4 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(2),
                size_words: 2,
                interval: LiveInterval { start: 0, end: 1 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(3),
                size_words: 4,
                interval: LiveInterval { start: 1, end: 4 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(4),
                size_words: 1,
                interval: LiveInterval { start: 4, end: 4 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(5),
                size_words: 2,
                interval: LiveInterval { start: 4, end: 6 },
                min_offset_words: 0,
            },
        ];

        let generic_peak = pack_objects_peak_presorted(&objects);
        let mut workspace = PeakPackWorkspace::default();
        let schedule = zero_min_release_schedule(&objects);
        let specialized_peak = pack_zero_min_offset_peak_ranked(
            &mut workspace,
            &schedule,
            zero_min_ranked_items(&objects),
            objects.len(),
        );

        assert_eq!(specialized_peak, generic_peak);
    }

    #[test]
    fn zero_min_peak_packer_matches_generic_peak_randomized() {
        let mut seed = 0x4d59_5df4_d0f3_3173u64;
        for case_idx in 0..256 {
            let count = (next_test_u32(&mut seed) % 12 + 1) as usize;
            let mut objects = Vec::with_capacity(count);
            for obj_idx in 0..count {
                let start = next_test_u32(&mut seed) % 16;
                let end = start + next_test_u32(&mut seed) % 8;
                objects.push(PackedObject {
                    id: StackObjId::new(obj_idx + 1),
                    size_words: next_test_u32(&mut seed) % 6 + 1,
                    interval: LiveInterval { start, end },
                    min_offset_words: 0,
                });
            }
            objects.sort_unstable_by_key(|obj| {
                (obj.interval.start, obj.interval.end, obj.id.as_u32())
            });

            let generic_peak = pack_objects_peak_presorted(&objects);
            let mut workspace = PeakPackWorkspace::default();
            let schedule = zero_min_release_schedule(&objects);
            let specialized_peak = pack_zero_min_offset_peak_ranked(
                &mut workspace,
                &schedule,
                zero_min_ranked_items(&objects),
                objects.len(),
            );

            assert_eq!(
                specialized_peak, generic_peak,
                "randomized zero-min peak mismatch on case {case_idx}"
            );
        }
    }

    #[test]
    fn zero_min_peak_packer_matches_generic_peak_with_dense_ties() {
        let mut seed = 0x7c52_91d2_4aa1_44cdu64;
        for case_idx in 0..256 {
            let count = (next_test_u32(&mut seed) % 16 + 1) as usize;
            let mut objects = Vec::with_capacity(count);
            for obj_idx in 0..count {
                let start = next_test_u32(&mut seed) % 4;
                let end = start + next_test_u32(&mut seed) % 3;
                objects.push(PackedObject {
                    id: StackObjId::new(obj_idx + 1),
                    size_words: next_test_u32(&mut seed) % 7,
                    interval: LiveInterval { start, end },
                    min_offset_words: 0,
                });
            }
            objects.sort_unstable_by_key(|obj| {
                (obj.interval.start, obj.interval.end, obj.id.as_u32())
            });

            let generic_peak = pack_objects_peak_presorted(&objects);
            let mut workspace = PeakPackWorkspace::default();
            let schedule = zero_min_release_schedule(&objects);
            let specialized_peak = pack_zero_min_offset_peak_ranked(
                &mut workspace,
                &schedule,
                zero_min_ranked_items(&objects),
                objects.len(),
            );

            assert_eq!(
                specialized_peak, generic_peak,
                "dense-tie zero-min peak mismatch on case {case_idx}"
            );
        }
    }

    #[test]
    fn packer_extends_frontier_segment_into_tail() {
        let presorted = [
            PackedObject {
                id: StackObjId::new(1),
                size_words: 4,
                interval: LiveInterval { start: 0, end: 5 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(2),
                size_words: 3,
                interval: LiveInterval { start: 1, end: 1 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(3),
                size_words: 5,
                interval: LiveInterval { start: 2, end: 4 },
                min_offset_words: 0,
            },
        ];

        let (offsets, max_used) = pack_objects_presorted(&presorted);
        let mut workspace = PeakPackWorkspace::default();
        let schedule = zero_min_release_schedule(&presorted);
        let specialized_peak = pack_zero_min_offset_peak_ranked(
            &mut workspace,
            &schedule,
            zero_min_ranked_items(&presorted),
            presorted.len(),
        );

        assert_eq!(offsets[&StackObjId::new(1)], 0);
        assert_eq!(offsets[&StackObjId::new(2)], 4);
        assert_eq!(offsets[&StackObjId::new(3)], 4);
        assert_eq!(max_used, 9);
        assert_eq!(pack_objects_peak_presorted(&presorted), 9);
        assert_eq!(specialized_peak, 9);
    }

    #[test]
    fn zero_min_peak_packer_reuses_remaining_interior_suffix() {
        let presorted = [
            PackedObject {
                id: StackObjId::new(1),
                size_words: 4,
                interval: LiveInterval { start: 0, end: 7 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(2),
                size_words: 6,
                interval: LiveInterval { start: 0, end: 2 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(3),
                size_words: 3,
                interval: LiveInterval { start: 1, end: 7 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(4),
                size_words: 2,
                interval: LiveInterval { start: 3, end: 6 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(5),
                size_words: 4,
                interval: LiveInterval { start: 4, end: 5 },
                min_offset_words: 0,
            },
        ];

        let (offsets, generic_peak) = pack_objects_presorted(&presorted);
        let mut workspace = PeakPackWorkspace::default();
        let schedule = zero_min_release_schedule(&presorted);
        let specialized_peak = pack_zero_min_offset_peak_ranked(
            &mut workspace,
            &schedule,
            zero_min_ranked_items(&presorted),
            presorted.len(),
        );

        assert_eq!(offsets[&StackObjId::new(1)], 0);
        assert_eq!(offsets[&StackObjId::new(2)], 4);
        assert_eq!(offsets[&StackObjId::new(3)], 10);
        assert_eq!(offsets[&StackObjId::new(4)], 4);
        assert_eq!(offsets[&StackObjId::new(5)], 6);
        assert_eq!(generic_peak, 13);
        assert_eq!(specialized_peak, generic_peak);
    }

    #[test]
    fn packer_materializes_gap_when_min_offset_skips_frontier() {
        let presorted = [
            PackedObject {
                id: StackObjId::new(1),
                size_words: 4,
                interval: LiveInterval { start: 0, end: 5 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(2),
                size_words: 2,
                interval: LiveInterval { start: 1, end: 1 },
                min_offset_words: 10,
            },
            PackedObject {
                id: StackObjId::new(3),
                size_words: 8,
                interval: LiveInterval { start: 2, end: 4 },
                min_offset_words: 0,
            },
        ];

        let (offsets, max_used) = pack_objects_presorted(&presorted);

        assert_eq!(offsets[&StackObjId::new(1)], 0);
        assert_eq!(offsets[&StackObjId::new(2)], 10);
        assert_eq!(offsets[&StackObjId::new(3)], 4);
        assert_eq!(max_used, 12);
        assert_eq!(pack_objects_peak_presorted(&presorted), 12);
    }

    #[test]
    fn zero_min_peak_packer_matches_generic_peak_for_sparse_trial_subset() {
        let universe = [
            PackedObject {
                id: StackObjId::new(1),
                size_words: 3,
                interval: LiveInterval { start: 0, end: 5 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(2),
                size_words: 2,
                interval: LiveInterval { start: 1, end: 1 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(3),
                size_words: 4,
                interval: LiveInterval { start: 2, end: 6 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(4),
                size_words: 5,
                interval: LiveInterval { start: 3, end: 4 },
                min_offset_words: 0,
            },
        ];
        let present = [0usize, 2, 3];
        let subset = present.map(|index| universe[index]);

        let generic_peak = pack_objects_peak_presorted(&subset);
        let mut workspace = PeakPackWorkspace::default();
        let schedule = zero_min_release_schedule(&universe);
        let specialized_peak = pack_zero_min_offset_peak_ranked(
            &mut workspace,
            &schedule,
            present.into_iter().map(|order_idx| RankedPeakPackItem {
                order_idx: order_idx as u32,
                start_rank: universe[order_idx].interval.start,
                size_words: universe[order_idx].size_words,
            }),
            subset.len(),
        );

        assert_eq!(specialized_peak, generic_peak);
    }

    #[test]
    fn zero_min_peak_packer_matches_generic_peak_when_frontier_forms_after_merge() {
        let objects = [
            PackedObject {
                id: StackObjId::new(4),
                size_words: 4,
                interval: LiveInterval { start: 0, end: 4 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(2),
                size_words: 1,
                interval: LiveInterval { start: 3, end: 4 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(1),
                size_words: 6,
                interval: LiveInterval { start: 5, end: 8 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(3),
                size_words: 1,
                interval: LiveInterval { start: 6, end: 12 },
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(5),
                size_words: 4,
                interval: LiveInterval { start: 7, end: 10 },
                min_offset_words: 0,
            },
        ];

        let generic_peak = pack_objects_peak_presorted(&objects);
        let mut workspace = PeakPackWorkspace::default();
        let schedule = zero_min_release_schedule(&objects);
        let specialized_peak = pack_zero_min_offset_peak_ranked(
            &mut workspace,
            &schedule,
            zero_min_ranked_items(&objects),
            objects.len(),
        );

        assert_eq!(generic_peak, 11);
        assert_eq!(specialized_peak, generic_peak);
    }

    fn zero_min_ranked_items(
        objects: &[PackedObject],
    ) -> impl Iterator<Item = RankedPeakPackItem> + '_ {
        objects
            .iter()
            .enumerate()
            .map(|(order_idx, obj)| RankedPeakPackItem {
                order_idx: order_idx as u32,
                start_rank: obj.interval.start,
                size_words: obj.size_words,
            })
    }

    fn zero_min_release_schedule(objects: &[PackedObject]) -> ReleaseSchedule {
        ReleaseSchedule::from_end_ranks(
            &objects
                .iter()
                .map(|obj| obj.interval.end)
                .collect::<Vec<_>>(),
            objects
                .iter()
                .map(|obj| obj.interval.end)
                .max()
                .map_or(0, |rank| rank as usize + 1),
        )
    }

    fn next_test_u32(seed: &mut u64) -> u32 {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        (*seed >> 32) as u32
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        critical_edge::CriticalEdgeSplitter,
        domtree::DomTree,
        isa::evm::{EvmBackend, canonicalize_alias_value},
        liveness::{InstLiveness, Liveness},
        stackalloc::StackifyBuilder,
    };
    use sonatina_parser::{ParsedModule, parse_module};
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};
    use std::fmt::Write;

    fn test_isa() -> Evm {
        Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        })
    }

    fn region(block: u32, start_boundary: u32, end_boundary: u32) -> LiveRegion {
        LiveRegion {
            segments: SmallVec::from_vec(vec![BlockLiveSegment {
                block: BlockId::from_u32(block),
                start_boundary,
                end_boundary,
            }]),
            first_rank: start_boundary,
            last_rank: end_boundary,
        }
    }

    fn analyze_function(
        input: &str,
        func_name: &str,
        stack_reach: u8,
    ) -> (ParsedModule, FuncRef, FuncAnalysis, FuncStackObjects) {
        let parsed = parse_module(input).expect("module parses");
        let isa = test_isa();
        let backend = EvmBackend::new(test_isa());
        let funcs = parsed.module.funcs();
        let ptr_escape =
            super::super::ptr_escape::compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func| {
                parsed
                    .module
                    .ctx
                    .func_sig(func, |sig| sig.name() == func_name)
            })
            .unwrap_or_else(|| panic!("function `{func_name}` exists"));

        let mut analysis = None;
        parsed.module.func_store.modify(func_ref, |function| {
            let mut cfg = sonatina_ir::cfg::ControlFlowGraph::new();
            cfg.compute(function);
            CriticalEdgeSplitter::new().run(function, &mut cfg);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut inst_liveness = InstLiveness::new();
            inst_liveness.compute(function, &cfg, &liveness);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let value_aliases =
                backend.compute_stackify_value_aliases(function, &parsed.module.ctx);

            let mut stack_liveness = Liveness::new();
            stack_liveness.compute_with_value_normalizer(function, &cfg, |value| {
                canonicalize_alias_value(&value_aliases, value)
            });

            let alloc = StackifyBuilder::new(function, &cfg, &dom, &stack_liveness, stack_reach)
                .with_value_aliases(&value_aliases)
                .compute();

            analysis = Some(FuncAnalysis {
                alloc,
                inst_liveness,
                block_order: dom.rpo().to_vec(),
                value_aliases,
            });
        });
        let analysis = analysis.expect("analysis computed");

        let alloc_ctx = StaticArenaAllocCtx::new(&parsed.module.ctx, &isa, &ptr_escape);
        let stack = parsed.module.func_store.view(func_ref, |function| {
            alloc_ctx.compute_func_stack_objects(func_ref, function, &analysis)
        });
        (parsed, func_ref, analysis, stack)
    }

    #[test]
    fn aliased_spill_is_marked_live_across_at_internal_call() {
        let (parsed, func_ref, analysis, stack) = analyze_function(
            include_str!("../../../tests/fixtures/fe_lazy_merkle_proof_element_1_pass6.sntn"),
            "lazyimtdata_hb575fd00dcf9c59f_merkle_proof_elements",
            16,
        );

        let spill_value = analysis.canonicalize_value(
            parsed
                .debug
                .value(func_ref, "v5")
                .expect("aliased pointer value exists"),
        );
        let spill_obj = analysis.alloc.spill_obj[spill_value].expect("spill object exists");

        let call = stack
            .call_sites
            .iter()
            .find(|call| {
                parsed.module.ctx.func_sig(call.callee, |sig| {
                    sig.name() == "lazyimtdata_hb575fd00dcf9c59f_levels_for_root"
                })
            })
            .expect("levels_for_root call exists");

        assert!(
            call.live_across_objs.contains(&spill_obj),
            "canonical spill object for aliased pointer should be live across the internal call"
        );
    }

    #[test]
    fn conservative_closure_allocas_expands_and_marks_unknown() {
        let root = InstId::from_u32(1);
        let child = InstId::from_u32(2);
        let unrelated = InstId::from_u32(3);
        let mut edges = FxHashMap::default();
        edges.insert(root, FxHashSet::from_iter([child]));
        let unknown = FxHashSet::from_iter([child]);
        let all_allocas = FxHashSet::from_iter([root, child, unrelated]);
        let closure = AllocaClosureCtx {
            edges: &edges,
            unknown: &unknown,
            all_allocas: &all_allocas,
        };

        let expanded = closure.expand_roots([root]);
        assert!(expanded.hit_unknown);
        assert_eq!(expanded.allocas, all_allocas);
    }

    #[test]
    fn loop_carried_spill_region_reaches_loop_header_via_backedge() {
        let mut src = String::from(
            r#"
target = "evm-ethereum-osaka"

func private %loop_spill() -> i256 {
block0:
    jump block1;

block1:
"#,
        );
        for i in 0..18 {
            let _ = writeln!(
                &mut src,
                "    v{}.i256 = phi ({}.i256 block0) (v{} block2);",
                i + 1,
                i,
                i + 20
            );
        }
        src.push_str(
            r#"
    v19.i256 = phi (0.i256 block0) (v38 block2);
    v39.i1 = lt v19 1.i256;
    br v39 block2 block3;

block2:
"#,
        );
        for i in 0..18 {
            let _ = writeln!(&mut src, "    v{}.i256 = add v{} 1.i256;", i + 20, i + 1);
        }
        src.push_str(
            r#"
    v38.i256 = add v19 1.i256;
    jump block1;

block3:
    return v18;
}
"#,
        );

        let (parsed, func_ref, analysis, stack) = analyze_function(&src, "loop_spill", 16);
        let spilled =
            analysis.canonicalize_value(parsed.debug.value(func_ref, "v18").expect("v18 exists"));
        let spill_obj =
            analysis.alloc.spill_obj[spilled].expect("loop-carried phi spill object exists");
        let region = &stack.obj_facts[&spill_obj].region;
        assert!(
            region
                .segments
                .iter()
                .any(|segment| segment.block == BlockId::from_u32(1)),
            "backedge spill should stay live in the loop header region: {region:?}"
        );
        assert!(
            region
                .segments
                .iter()
                .any(|segment| segment.block == BlockId::from_u32(2)),
            "backedge spill should stay live through the looping predecessor block: {region:?}"
        );
    }

    #[test]
    fn loop_carried_alloca_region_reaches_loop_header_via_backedge() {
        let (parsed, func_ref, _analysis, stack) = analyze_function(
            r#"
target = "evm-ethereum-osaka"

func private %loop_alloca_phi() -> i256 {
    block0:
        v0.*i256 = alloca i256;
        mstore v0 1.i256 i256;
        jump block1;

    block1:
        v1.*i256 = phi (v0 block0) (v4 block2);
        v2.i256 = phi (0.i256 block0) (v5 block2);
        v3.i1 = lt v2 1.i256;
        br v3 block2 block3;

    block2:
        v4.*i256 = alloca i256;
        mstore v4 2.i256 i256;
        v5.i256 = add v2 1.i256;
        jump block1;

    block3:
        v6.i256 = mload v1 i256;
        return v6;
}
"#,
            "loop_alloca_phi",
            16,
        );

        let loop_alloca = parsed.debug.value(func_ref, "v4").expect("v4 exists");
        let alloca_inst = parsed.module.func_store.view(func_ref, |function| {
            function
                .dfg
                .value_inst(loop_alloca)
                .expect("v4 is defined by alloca")
        });
        let obj_id = stack.alloca_ids[&alloca_inst];
        let region = &stack.obj_facts[&obj_id].region;
        assert!(
            region
                .segments
                .iter()
                .any(|segment| segment.block == BlockId::from_u32(1)),
            "loop-carried alloca should stay live in the loop header across the backedge: {region:?}"
        );
        assert!(
            region
                .segments
                .iter()
                .any(|segment| segment.block == BlockId::from_u32(2)),
            "loop-carried alloca should remain live through its defining block: {region:?}"
        );
    }

    #[test]
    fn phi_operand_allocas_live_on_predecessor_tails_not_successor_entry() {
        let mut src = String::from(
            r#"
target = "evm-ethereum-osaka"

func private %branch_phi(v0.i1) -> i32 {
block0:
    br v0 block1 block2;

block1:
"#,
        );
        for i in 0..18 {
            let _ = writeln!(&mut src, "    v{}.i32 = add {i}.i32 1.i32;", i + 1);
        }
        src.push_str(
            r#"
    jump block3;

block2:
"#,
        );
        for i in 0..18 {
            let _ = writeln!(&mut src, "    v{}.i32 = add {}.i32 1.i32;", i + 19, 100 + i);
        }
        src.push_str(
            r#"
    jump block3;

block3:
"#,
        );
        for i in 0..18 {
            let _ = writeln!(
                &mut src,
                "    v{}.i32 = phi (v{} block1) (v{} block2);",
                i + 37,
                i + 1,
                i + 19
            );
        }
        src.push_str(
            r#"
    return v54;
}
"#,
        );

        let (parsed, func_ref, analysis, stack) = analyze_function(&src, "branch_phi", 16);
        let left_region = (1..=18)
            .find_map(|idx| {
                let name = format!("v{idx}");
                let value = analysis.canonicalize_value(
                    parsed
                        .debug
                        .value(func_ref, &name)
                        .expect("branch value exists"),
                );
                let obj = analysis.alloc.spill_obj[value]?;
                Some(&stack.obj_facts[&obj].region)
            })
            .expect("left branch should produce a spilled phi operand value");
        let right_region = (19..=36)
            .find_map(|idx| {
                let name = format!("v{idx}");
                let value = analysis.canonicalize_value(
                    parsed
                        .debug
                        .value(func_ref, &name)
                        .expect("branch value exists"),
                );
                let obj = analysis.alloc.spill_obj[value]?;
                Some(&stack.obj_facts[&obj].region)
            })
            .expect("right branch should produce a spilled phi operand value");

        assert!(
            left_region
                .segments
                .iter()
                .any(|segment| segment.block == BlockId::from_u32(1)),
            "left phi operand spill should stay live through its predecessor block: {left_region:?}"
        );
        assert!(
            right_region
                .segments
                .iter()
                .any(|segment| segment.block == BlockId::from_u32(2)),
            "right phi operand spill should stay live through its predecessor block: {right_region:?}"
        );
        assert!(
            left_region
                .segments
                .iter()
                .all(|segment| segment.block != BlockId::from_u32(3)),
            "left phi operand spill should not be treated as successor-entry live for the phi block: {left_region:?}"
        );
        assert!(
            right_region
                .segments
                .iter()
                .all(|segment| segment.block != BlockId::from_u32(3)),
            "right phi operand spill should not be treated as successor-entry live for the phi block: {right_region:?}"
        );
        assert!(
            !left_region.overlaps(right_region),
            "branch-exclusive phi operand spills should not conflict: left={left_region:?} right={right_region:?}"
        );
    }

    #[test]
    fn closure_expanded_child_alloca_becomes_visible_and_live_at_call() {
        let (parsed, func_ref, _analysis, stack) = analyze_function(
            r#"
target = "evm-ethereum-osaka"

func private %callee(v0.*i256) -> i256 {
block0:
    mstore v0 7.i256 i256;
    return 0.i256;
}

func private %closure_visible() -> i256 {
block0:
    v0.**i256 = alloca *i256;
    v1.*i256 = alloca i256;
    mstore v1 1.i256 i256;
    mstore v0 v1 *i256;
    v2.*i256 = mload v0 *i256;
    v3.i256 = call %callee v2;
    v4.i256 = mload v1 i256;
    return v4;
}
"#,
            "closure_visible",
            16,
        );

        let child_alloca = parsed.module.func_store.view(func_ref, |function| {
            function
                .dfg
                .value_inst(parsed.debug.value(func_ref, "v1").expect("v1 exists"))
                .expect("v1 is defined by alloca")
        });
        let child_obj = stack.alloca_ids[&child_alloca];
        let call = stack
            .call_sites
            .iter()
            .find(|call| {
                parsed
                    .module
                    .ctx
                    .func_sig(call.callee, |sig| sig.name() == "callee")
            })
            .expect("callee call exists");

        assert!(
            call.callee_visible_objs.contains(&child_obj),
            "closure-expanded child alloca should be visible to the callee"
        );
        assert!(
            call.live_across_objs.contains(&child_obj),
            "closure-expanded child alloca should stay live across the call when read afterward"
        );
    }

    #[test]
    fn exact_pack_reuses_storage_for_branch_exclusive_regions() {
        let mut objects = vec![
            PackedObject {
                id: StackObjId::new(1),
                size_words: 4,
                region: region(0, 0, 2),
                min_offset_words: 0,
            },
            PackedObject {
                id: StackObjId::new(2),
                size_words: 3,
                region: region(1, 0, 2),
                min_offset_words: 0,
            },
        ];
        objects.sort_unstable_by_key(|obj| obj.region.sort_key(obj.id));

        let (offsets, max_used) = pack_objects_presorted(&objects);
        assert_eq!(offsets[&StackObjId::new(1)], 0);
        assert_eq!(offsets[&StackObjId::new(2)], 0);
        assert_eq!(max_used, 4);
    }

    #[test]
    fn exact_pack_respects_conflicts_and_min_offsets() {
        let items = vec![
            ExactPackItem {
                id: StackObjId::new(1),
                idx: LocalObjIdx::new(0),
                size_words: 3,
                min_offset_words: 0,
            },
            ExactPackItem {
                id: StackObjId::new(2),
                idx: LocalObjIdx::new(1),
                size_words: 2,
                min_offset_words: 1,
            },
            ExactPackItem {
                id: StackObjId::new(3),
                idx: LocalObjIdx::new(2),
                size_words: 1,
                min_offset_words: 5,
            },
        ];
        let mut conflicts = vec![BitSet::default(); 3];
        let _ = conflicts[0].insert(LocalObjIdx::new(1));
        let _ = conflicts[1].insert(LocalObjIdx::new(0));

        let packed = pack_exact_with_offsets(&items, &conflicts);
        assert_eq!(packed.offsets[&StackObjId::new(1)], 0);
        assert_eq!(packed.offsets[&StackObjId::new(2)], 3);
        assert_eq!(packed.offsets[&StackObjId::new(3)], 5);
        assert_eq!(packed.max_used, 6);
    }
}
