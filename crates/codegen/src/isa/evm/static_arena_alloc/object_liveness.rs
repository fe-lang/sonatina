use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
};

use crate::bitset::BitSet;

use super::{
    super::memory_plan::FuncAnalysis, CallSiteObjects, LocalObjIdx, Provenance, StackObjId,
};

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

#[derive(Default)]
pub(crate) struct ExpandedAllocaRoots {
    pub(crate) allocas: FxHashSet<InstId>,
    pub(crate) hit_unknown: bool,
}

pub(crate) struct AllocaClosureCtx<'a> {
    pub(crate) edges: &'a FxHashMap<InstId, FxHashSet<InstId>>,
    pub(crate) unknown: &'a FxHashSet<InstId>,
    pub(crate) all_allocas: &'a FxHashSet<InstId>,
}

impl AllocaClosureCtx<'_> {
    pub(crate) fn expand_roots(
        &self,
        roots: impl IntoIterator<Item = InstId>,
    ) -> ExpandedAllocaRoots {
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
    inst_index_in_block: FxHashMap<InstId, u32>,
}

pub(super) struct ComputeCtx<'a, 'b> {
    pub(super) analysis: &'a FuncAnalysis,
    pub(super) isa: &'a Evm,
    pub(super) prov: &'a SecondaryMap<ValueId, Provenance>,
    pub(super) spill_local_by_value: &'a SecondaryMap<ValueId, Option<LocalObjIdx>>,
    pub(super) alloca_local_by_inst: &'a FxHashMap<InstId, LocalObjIdx>,
    pub(super) closure: &'a AllocaClosureCtx<'b>,
    pub(super) unknown_barrier_objs: &'a mut FxHashSet<StackObjId>,
    pub(super) obj_id_by_local: &'a [StackObjId],
    pub(super) alloca_ids: &'a FxHashMap<InstId, StackObjId>,
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
    ctx: &mut ComputeCtx<'_, '_>,
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

pub(super) fn compute_regions_and_calls(
    function: &Function,
    cfg: &ControlFlowGraph,
    block_order: &[BlockId],
    ctx: &mut ComputeCtx<'_, '_>,
) -> (Vec<LiveRegion>, Vec<CallSiteObjects>) {
    let events = build_object_event_index(function, block_order, ctx);
    let block_live = solve_object_block_liveness(function, cfg, block_order, &events);
    let regions = emit_regions(
        function,
        block_order,
        &events,
        &block_live,
        ctx.obj_id_by_local.len(),
    );

    let mut call_sites = Vec::new();
    for &block in block_order {
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
                .map(|local_idx| ctx.obj_id_by_local[local_idx.as_u32() as usize])
                .collect();
            live_across_objs.sort_unstable_by_key(|id| id.as_u32());

            let mut visible_objs: FxHashSet<StackObjId> = FxHashSet::default();
            let mut roots: FxHashSet<InstId> = FxHashSet::default();
            for &arg in call.args() {
                for base in ctx.prov[arg].alloca_insts() {
                    roots.insert(base);
                }
            }
            let expanded = ctx.closure.expand_roots(roots.iter().copied());
            for alloca in expanded.allocas {
                if let Some(&id) = ctx.alloca_ids.get(&alloca) {
                    visible_objs.insert(id);
                    if expanded.hit_unknown {
                        ctx.unknown_barrier_objs.insert(id);
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

    (regions, call_sites)
}
