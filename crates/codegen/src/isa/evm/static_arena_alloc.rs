//! StaticArena stack-object layout (allocas + spills).
//!
//! Memory model:
//! - `MemScheme::StaticArena` uses a shared base (`STATIC_BASE`) across functions.
//! - A call to a StaticArena callee `g` may clobber the prefix `[0..need_words(g))`.
//! - Any caller object live across that call must be placed at offset `>= need_words(g)`.
//!
//! Packing:
//! - Variable-sized linear scan over live intervals with a free-segment map.
//! - Each object has a lower bound (`min_offset_words`) derived from call clobber constraints.

use cranelift_entity::{EntityRef, SecondaryMap, entity_impl};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};
use std::{cmp::Reverse, collections::BinaryHeap};

use crate::{bitset::BitSet, liveness::InstLiveness};

use super::{
    memory_plan::{FuncAnalysis, WORD_BYTES},
    provenance::{Provenance, compute_provenance},
    ptr_escape::PtrEscapeSummary,
};

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct StackObjId(u32);
entity_impl!(StackObjId);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum StackObjKind {
    Alloca(InstId),
    Spill(ValueId),
    Shadow(InstId),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct LiveInterval {
    pub(crate) start: u32,
    pub(crate) end: u32,
}

#[derive(Clone, Debug)]
pub(crate) struct StackObj {
    pub(crate) id: StackObjId,
    pub(crate) kind: StackObjKind,
    pub(crate) size_words: u32,
    pub(crate) interval: LiveInterval,
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
    pub(crate) interval: LiveInterval,
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
    pub(crate) inst_pos: u32,
    pub(crate) callee: FuncRef,
    pub(crate) result_count: u8,
    #[allow(dead_code)]
    pub(crate) arg_count: u8,
    pub(crate) live_out_objs: Vec<StackObjId>,
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

pub(crate) fn compute_block_end_pos(
    function: &Function,
    inst_pos: &FxHashMap<InstId, u32>,
) -> FxHashMap<BlockId, u32> {
    let mut out: FxHashMap<BlockId, u32> = FxHashMap::default();
    for block in function.layout.iter_block() {
        let mut end: Option<u32> = None;
        for inst in function.layout.iter_inst(block) {
            end = Some(inst_pos.get(&inst).copied().unwrap_or_default());
        }
        out.insert(block, end.unwrap_or(0));
    }
    out
}

pub(crate) fn compute_func_stack_objects(
    func_ref: FuncRef,
    function: &Function,
    ctx: &StaticArenaAllocCtx<'_>,
    analysis: &FuncAnalysis,
) -> FuncStackObjects {
    let (inst_order, inst_pos) = compute_inst_order(function, &analysis.block_order);
    let block_end_pos = compute_block_end_pos(function, &inst_pos);

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

    let spill_intervals = compute_spill_intervals(
        function,
        analysis,
        ctx.isa,
        &inst_order,
        &inst_pos,
        &block_end_pos,
        &spilled_values,
    );

    let mut objects: Vec<StackObj> = Vec::new();
    for v in spilled_values.iter() {
        let id = spill_obj[v].expect("spilled value missing stack object id");
        objects.push(StackObj {
            id,
            kind: StackObjKind::Spill(v),
            size_words: 1,
            interval: spill_intervals
                .get(&v)
                .copied()
                .unwrap_or(LiveInterval { start: 0, end: 0 }),
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

    let alloca_intervals = compute_alloca_intervals(
        function,
        ctx.isa,
        &inst_order,
        &inst_pos,
        &block_end_pos,
        &analysis.inst_liveness,
        prov,
    );

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
            interval: alloca_intervals
                .get(&inst)
                .copied()
                .unwrap_or(LiveInterval {
                    start: inst_pos.get(&inst).copied().unwrap_or_default(),
                    end: inst_pos.get(&inst).copied().unwrap_or_default(),
                }),
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
    let mut call_sites: Vec<CallSiteObjects> = Vec::new();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let Some(call) = function.dfg.cast_call(inst) else {
                continue;
            };
            let pos = inst_pos.get(&inst).copied().unwrap_or_default();
            let callee = *call.callee();
            let local_return = ctx.module.func_effects(callee).may_return_to_caller();
            let arg_count = u8::try_from(call.args().len()).expect("call arg count too large");
            let call_results = function.dfg.inst_results(inst);
            let canonical_call_results: FxHashSet<ValueId> = call_results
                .iter()
                .map(|&value| analysis.canonicalize_value(value))
                .collect();
            let result_count =
                u8::try_from(call_results.len()).expect("call result count too large");

            let mut set: FxHashSet<StackObjId> = FxHashSet::default();
            let mut roots: FxHashSet<InstId> = FxHashSet::default();
            if local_return {
                for v in analysis.inst_liveness.live_out(inst).iter() {
                    let v = analysis.canonicalize_value(v);
                    if canonical_call_results.contains(&v) {
                        continue;
                    }

                    if let Some(obj) = spill_obj[v] {
                        set.insert(obj);
                    }

                    for base in prov[v].alloca_insts() {
                        roots.insert(base);
                    }
                }
            }

            let (allocas, unknown_live) = conservative_closure_allocas(
                roots.iter().copied(),
                &local_edges,
                &local_unknown,
                &all_allocas,
            );
            for base in allocas {
                if let Some(&id) = alloca_ids.get(&base) {
                    set.insert(id);
                    if unknown_live {
                        unknown_barrier_objs.insert(id);
                    }
                }
            }

            let mut live_objs: Vec<StackObjId> = set.into_iter().collect();
            live_objs.sort_unstable_by_key(|id| id.as_u32());

            let mut visible_objs: FxHashSet<StackObjId> = FxHashSet::default();
            let mut roots: FxHashSet<InstId> = FxHashSet::default();
            for &arg in call.args() {
                for base in prov[arg].alloca_insts() {
                    roots.insert(base);
                }
            }
            let (allocas, unknown_visible) = conservative_closure_allocas(
                roots.iter().copied(),
                &local_edges,
                &local_unknown,
                &all_allocas,
            );
            for base in allocas {
                if let Some(&id) = alloca_ids.get(&base) {
                    visible_objs.insert(id);
                    if unknown_visible {
                        unknown_barrier_objs.insert(id);
                    }
                }
            }
            let mut callee_visible_objs: Vec<StackObjId> = visible_objs.into_iter().collect();
            callee_visible_objs.sort_unstable_by_key(|id| id.as_u32());
            call_sites.push(CallSiteObjects {
                inst,
                inst_pos: pos,
                callee,
                result_count,
                arg_count,
                live_out_objs: live_objs,
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
                interval: obj.interval,
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
        for &obj in &call.live_out_objs {
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

fn compute_spill_intervals(
    function: &Function,
    analysis: &FuncAnalysis,
    isa: &Evm,
    inst_order: &[InstId],
    inst_pos: &FxHashMap<InstId, u32>,
    block_end_pos: &FxHashMap<BlockId, u32>,
    spilled: &BitSet<ValueId>,
) -> FxHashMap<ValueId, LiveInterval> {
    let mut start: FxHashMap<ValueId, u32> = FxHashMap::default();
    let mut end: FxHashMap<ValueId, u32> = FxHashMap::default();

    for v in spilled.iter() {
        let start_pos = if matches!(function.dfg.value(v), sonatina_ir::Value::Arg { .. }) {
            0
        } else if let Some(inst) = function.dfg.value_inst(v) {
            inst_pos.get(&inst).copied().unwrap_or_default()
        } else {
            0
        };
        start.insert(v, start_pos);
        end.insert(v, start_pos);
    }

    for &inst in inst_order {
        let pos = inst_pos.get(&inst).copied().unwrap_or_default();
        let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
        if let EvmInstKind::Phi(phi) = data {
            for (val, pred) in phi.args().iter() {
                let val = analysis.canonicalize_value(*val);
                if spilled.contains(val) {
                    let use_pos = block_end_pos.get(pred).copied().unwrap_or_default();
                    end.entry(val).and_modify(|e| *e = (*e).max(use_pos));
                }
            }
        } else {
            function.dfg.inst(inst).for_each_value(&mut |v| {
                let v = analysis.canonicalize_value(v);
                if spilled.contains(v) {
                    end.entry(v).and_modify(|e| *e = (*e).max(pos));
                }
            });
        }

        for v in analysis.inst_liveness.live_out(inst).iter() {
            let v = analysis.canonicalize_value(v);
            if spilled.contains(v) {
                end.entry(v).and_modify(|e| *e = (*e).max(pos));
            }
        }
    }

    let mut out: FxHashMap<ValueId, LiveInterval> = FxHashMap::default();
    for v in spilled.iter() {
        let s = start.get(&v).copied().unwrap_or(0);
        let e = end.get(&v).copied().unwrap_or(s);
        out.insert(v, LiveInterval { start: s, end: e });
    }
    out
}

fn compute_alloca_intervals(
    function: &Function,
    isa: &Evm,
    inst_order: &[InstId],
    inst_pos: &FxHashMap<InstId, u32>,
    block_end_pos: &FxHashMap<BlockId, u32>,
    inst_liveness: &InstLiveness,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> FxHashMap<InstId, LiveInterval> {
    let mut allocas: FxHashSet<InstId> = FxHashSet::default();
    for &inst in inst_order {
        if matches!(
            isa.inst_set().resolve_inst(function.dfg.inst(inst)),
            EvmInstKind::Alloca(_)
        ) {
            allocas.insert(inst);
        }
    }

    let mut last_live: FxHashMap<InstId, u32> = FxHashMap::default();
    for &inst in &allocas {
        let pos = inst_pos.get(&inst).copied().unwrap_or_default();
        last_live.insert(inst, pos);
    }

    for &inst in inst_order {
        let pos = inst_pos.get(&inst).copied().unwrap_or_default();
        let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
        if let EvmInstKind::Phi(phi) = data {
            for (val, pred) in phi.args().iter() {
                let use_pos = block_end_pos.get(pred).copied().unwrap_or_default();
                for base in prov[*val].alloca_insts() {
                    let entry = last_live.get_mut(&base).expect("missing alloca last-live");
                    *entry = (*entry).max(use_pos);
                }
            }
        } else {
            function.dfg.inst(inst).for_each_value(&mut |v| {
                for base in prov[v].alloca_insts() {
                    let entry = last_live.get_mut(&base).expect("missing alloca last-live");
                    *entry = (*entry).max(pos);
                }
            });
        }

        for v in inst_liveness.live_out(inst).iter() {
            if prov[v].is_empty() {
                continue;
            }
            for base in prov[v].alloca_insts() {
                let entry = last_live.get_mut(&base).expect("missing alloca last-live");
                *entry = (*entry).max(pos);
            }
        }
    }

    let mut out: FxHashMap<InstId, LiveInterval> = FxHashMap::default();
    for &inst in &allocas {
        let start = inst_pos.get(&inst).copied().unwrap_or_default();
        let end = last_live.get(&inst).copied().unwrap_or(start);
        out.insert(inst, LiveInterval { start, end });
    }
    out
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct PackedObject {
    pub(crate) id: StackObjId,
    pub(crate) size_words: u32,
    pub(crate) interval: LiveInterval,
    pub(crate) min_offset_words: u32,
}

#[derive(Clone, Copy, Debug)]
struct FreeSegment {
    start: u32,
    len: u32,
}

impl FreeSegment {
    fn end(self) -> u32 {
        self.start
            .checked_add(self.len)
            .expect("free segment overflow")
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct RankedPeakPackItem {
    pub(crate) order_idx: u32,
    pub(crate) start_rank: u32,
    pub(crate) size_words: u32,
}

#[derive(Clone, Debug)]
pub(crate) struct ReleaseSchedule {
    by_end_rank: Vec<std::ops::Range<usize>>,
    order_indices: Vec<u32>,
}

impl ReleaseSchedule {
    pub(crate) fn from_end_ranks(end_ranks_by_order: &[u32], rank_count: usize) -> Self {
        let mut order_indices: Vec<u32> = (0..end_ranks_by_order.len())
            .map(|order_idx| order_idx as u32)
            .collect();
        order_indices
            .sort_unstable_by_key(|&order_idx| (end_ranks_by_order[order_idx as usize], order_idx));

        let mut by_end_rank = vec![0..0; rank_count];
        let mut cursor = 0usize;
        for (rank, range) in by_end_rank.iter_mut().enumerate() {
            let start = cursor;
            while let Some(&order_idx) = order_indices.get(cursor)
                && end_ranks_by_order[order_idx as usize] == rank as u32
            {
                cursor += 1;
            }
            *range = start..cursor;
        }

        Self {
            by_end_rank,
            order_indices,
        }
    }
}

#[derive(Default)]
struct PeakFreeTree {
    root: Option<u32>,
    nodes: Vec<PeakFreeNode>,
    frontier: Option<FreeSegment>,
}

#[derive(Clone, Copy, Debug)]
struct PeakFreeNode {
    seg: FreeSegment,
    prio: u64,
    parent: Option<u32>,
    left: Option<u32>,
    right: Option<u32>,
    max_len: u32,
}

impl PeakFreeTree {
    fn reset(&mut self, capacity_hint: usize) {
        self.root = None;
        self.nodes.clear();
        self.frontier = None;
        if self.nodes.capacity() < capacity_hint {
            self.nodes.reserve(capacity_hint - self.nodes.capacity());
        }
    }

    fn insert(&mut self, start: u32, len: u32, max_used: u32) {
        if len == 0 {
            return;
        }

        let mut segment = FreeSegment { start, len };
        if let Some(frontier) = self.frontier
            && segment.end() == frontier.start
        {
            self.frontier = None;
            segment.len = segment
                .len
                .checked_add(frontier.len)
                .expect("free segment overflow");
        }

        let succ_idx = self.lower_bound(segment.start);
        let pred_idx = succ_idx
            .and_then(|idx| self.predecessor(idx))
            .or_else(|| self.max_node(self.root));

        if let Some(pred_idx) = pred_idx {
            let pred = self.nodes[pred_idx as usize].seg;
            if pred.end() == segment.start {
                self.remove_node(pred_idx);
                segment.start = pred.start;
                segment.len = segment
                    .len
                    .checked_add(pred.len)
                    .expect("free segment overflow");
            }
        }

        if let Some(succ_idx) = succ_idx {
            let succ = self.nodes[succ_idx as usize].seg;
            if segment.end() == succ.start {
                self.remove_node(succ_idx);
                segment.len = segment
                    .len
                    .checked_add(succ.len)
                    .expect("free segment overflow");
            }
        }

        if segment.end() == max_used {
            self.frontier = Some(segment);
            return;
        }

        let node_idx = self.alloc_node(segment);
        self.insert_node(node_idx);
    }

    fn take_fit(&mut self, size_words: u32) -> Option<FreeSegment> {
        let mut cursor = self.root;
        while let Some(idx) = cursor {
            let left = self.nodes[idx as usize].left;
            if self.max_len(left) >= size_words {
                cursor = left;
                continue;
            }
            if self.nodes[idx as usize].seg.len >= size_words {
                let seg = self.nodes[idx as usize].seg;
                self.remove_node(idx);
                return Some(seg);
            }
            let right = self.nodes[idx as usize].right;
            if self.max_len(right) >= size_words {
                cursor = right;
                continue;
            }
            return None;
        }
        None
    }

    fn take_frontier(&mut self) -> Option<FreeSegment> {
        self.frontier.take()
    }

    fn alloc_node(&mut self, seg: FreeSegment) -> u32 {
        let idx = self.nodes.len() as u32;
        self.nodes.push(PeakFreeNode {
            seg,
            prio: priority_for(seg.start),
            parent: None,
            left: None,
            right: None,
            max_len: seg.len,
        });
        idx
    }

    fn max_len(&self, root: Option<u32>) -> u32 {
        root.map_or(0, |idx| self.nodes[idx as usize].max_len)
    }

    fn recompute(&mut self, idx: u32) {
        let node = self.nodes[idx as usize];
        self.nodes[idx as usize].max_len = node
            .seg
            .len
            .max(self.max_len(node.left))
            .max(self.max_len(node.right));
    }

    fn update_parent(&mut self, child: Option<u32>, parent: Option<u32>) {
        if let Some(child) = child {
            self.nodes[child as usize].parent = parent;
        }
    }

    fn set_left(&mut self, parent: u32, child: Option<u32>) {
        self.nodes[parent as usize].left = child;
        self.update_parent(child, Some(parent));
    }

    fn set_right(&mut self, parent: u32, child: Option<u32>) {
        self.nodes[parent as usize].right = child;
        self.update_parent(child, Some(parent));
    }

    fn replace_child(&mut self, parent: Option<u32>, old: u32, new: Option<u32>) {
        if let Some(parent) = parent {
            if self.nodes[parent as usize].left == Some(old) {
                self.set_left(parent, new);
            } else {
                debug_assert_eq!(self.nodes[parent as usize].right, Some(old));
                self.set_right(parent, new);
            }
        } else {
            self.root = new;
            self.update_parent(new, None);
        }
    }

    fn recompute_upwards(&mut self, mut node: Option<u32>) {
        while let Some(idx) = node {
            self.recompute(idx);
            node = self.nodes[idx as usize].parent;
        }
    }

    fn rotate_left(&mut self, idx: u32) {
        let right = self.nodes[idx as usize]
            .right
            .expect("rotate_left requires right child");
        let parent = self.nodes[idx as usize].parent;
        let beta = self.nodes[right as usize].left;
        self.replace_child(parent, idx, Some(right));
        self.set_right(idx, beta);
        self.set_left(right, Some(idx));
        self.recompute(idx);
        self.recompute(right);
    }

    fn rotate_right(&mut self, idx: u32) {
        let left = self.nodes[idx as usize]
            .left
            .expect("rotate_right requires left child");
        let parent = self.nodes[idx as usize].parent;
        let beta = self.nodes[left as usize].right;
        self.replace_child(parent, idx, Some(left));
        self.set_left(idx, beta);
        self.set_right(left, Some(idx));
        self.recompute(idx);
        self.recompute(left);
    }

    fn lower_bound(&self, key: u32) -> Option<u32> {
        let mut cursor = self.root;
        let mut candidate = None;
        while let Some(idx) = cursor {
            let node = self.nodes[idx as usize];
            if node.seg.start < key {
                cursor = node.right;
            } else {
                candidate = Some(idx);
                cursor = node.left;
            }
        }
        candidate
    }

    fn max_node(&self, mut node: Option<u32>) -> Option<u32> {
        while let Some(idx) = node
            && let Some(right) = self.nodes[idx as usize].right
        {
            node = Some(right);
        }
        node
    }

    fn predecessor(&self, idx: u32) -> Option<u32> {
        if self.nodes[idx as usize].left.is_some() {
            return self.max_node(self.nodes[idx as usize].left);
        }
        let mut cursor = idx;
        let mut parent = self.nodes[cursor as usize].parent;
        while let Some(parent_idx) = parent {
            if self.nodes[parent_idx as usize].right == Some(cursor) {
                return Some(parent_idx);
            }
            cursor = parent_idx;
            parent = self.nodes[cursor as usize].parent;
        }
        None
    }

    fn insert_node(&mut self, node_idx: u32) {
        let start = self.nodes[node_idx as usize].seg.start;
        let Some(mut cursor) = self.root else {
            self.root = Some(node_idx);
            return;
        };
        loop {
            if start < self.nodes[cursor as usize].seg.start {
                if let Some(left) = self.nodes[cursor as usize].left {
                    cursor = left;
                } else {
                    self.set_left(cursor, Some(node_idx));
                    break;
                }
            } else if let Some(right) = self.nodes[cursor as usize].right {
                cursor = right;
            } else {
                self.set_right(cursor, Some(node_idx));
                break;
            }
        }

        while let Some(parent) = self.nodes[node_idx as usize].parent {
            if self.nodes[parent as usize].prio <= self.nodes[node_idx as usize].prio {
                break;
            }
            if self.nodes[parent as usize].left == Some(node_idx) {
                self.rotate_right(parent);
            } else {
                self.rotate_left(parent);
            }
        }
        self.recompute_upwards(Some(node_idx));
    }

    fn remove_node(&mut self, idx: u32) {
        while self.nodes[idx as usize].left.is_some() || self.nodes[idx as usize].right.is_some() {
            match (
                self.nodes[idx as usize].left,
                self.nodes[idx as usize].right,
            ) {
                (Some(left), Some(right)) => {
                    if self.nodes[left as usize].prio <= self.nodes[right as usize].prio {
                        self.rotate_right(idx);
                    } else {
                        self.rotate_left(idx);
                    }
                }
                (Some(_), None) => self.rotate_right(idx),
                (None, Some(_)) => self.rotate_left(idx),
                (None, None) => unreachable!(),
            }
        }

        let parent = self.nodes[idx as usize].parent;
        self.replace_child(parent, idx, None);
        self.nodes[idx as usize].parent = None;
        self.recompute_upwards(parent);
    }
}

fn priority_for(start: u32) -> u64 {
    let mut x = u64::from(start).wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

#[derive(Default)]
pub(crate) struct PeakPackWorkspace {
    free: PeakFreeTree,
    active_epoch: Vec<u32>,
    active_off: Vec<u32>,
    active_size: Vec<u32>,
    epoch: u32,
}

impl PeakPackWorkspace {
    fn reset(&mut self, capacity_hint: usize, universe_len: usize) {
        self.free.reset(capacity_hint);
        if self.active_epoch.len() < universe_len {
            self.active_epoch.resize(universe_len, 0);
            self.active_off.resize(universe_len, 0);
            self.active_size.resize(universe_len, 0);
        }
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.active_epoch.fill(0);
            self.epoch = 1;
        }
    }
}

trait FreeList {
    fn with_capacity(capacity: usize) -> Self;
    fn insert(&mut self, start: u32, len: u32);
    fn take_fit(&mut self, min_offset_words: u32, size_words: u32) -> Option<FreeSegment>;
    fn take_frontier_segment(&mut self, max_used: u32) -> Option<FreeSegment>;
}

struct SortedFreeList(Vec<FreeSegment>);

#[cfg(test)]
struct UnsortedFreeList(Vec<FreeSegment>);

impl FreeList for SortedFreeList {
    fn with_capacity(capacity: usize) -> Self {
        Self(Vec::with_capacity(capacity))
    }

    fn insert(&mut self, start: u32, len: u32) {
        insert_free_segment_sorted(&mut self.0, start, len);
    }

    fn take_fit(&mut self, min_offset_words: u32, size_words: u32) -> Option<FreeSegment> {
        find_first_fit_segment(&self.0, min_offset_words, size_words)
            .map(|index| self.0.remove(index))
    }

    fn take_frontier_segment(&mut self, max_used: u32) -> Option<FreeSegment> {
        match self.0.last().copied() {
            Some(segment) if segment.end() == max_used => self.0.pop(),
            _ => None,
        }
    }
}

#[cfg(test)]
impl FreeList for UnsortedFreeList {
    fn with_capacity(capacity: usize) -> Self {
        Self(Vec::with_capacity(capacity))
    }

    fn insert(&mut self, start: u32, len: u32) {
        insert_free_segment_unsorted(&mut self.0, start, len);
    }

    fn take_fit(&mut self, min_offset_words: u32, size_words: u32) -> Option<FreeSegment> {
        find_min_start_fit_segment(&self.0, min_offset_words, size_words)
            .map(|index| self.0.swap_remove(index))
    }

    fn take_frontier_segment(&mut self, max_used: u32) -> Option<FreeSegment> {
        self.0
            .iter()
            .position(|&segment| segment.end() == max_used)
            .map(|index| self.0.swap_remove(index))
    }
}

#[cfg(test)]
pub(crate) fn pack_objects(objects: &mut [PackedObject]) -> (FxHashMap<StackObjId, u32>, u32) {
    objects.sort_unstable_by_key(|o| (o.interval.start, o.interval.end, o.id.as_u32()));
    pack_objects_presorted(objects)
}

pub(crate) fn pack_objects_presorted(
    objects: &[PackedObject],
) -> (FxHashMap<StackObjId, u32>, u32) {
    let mut out = FxHashMap::with_capacity_and_hasher(objects.len(), Default::default());
    let max_used = pack_objects_impl(objects.iter().copied(), objects.len(), |id, off| {
        let _ = out.insert(id, off);
    });
    (out, max_used)
}

#[cfg(test)]
pub(crate) fn pack_objects_peak_presorted(objects: &[PackedObject]) -> u32 {
    pack_objects_peak(objects.iter().copied())
}

#[cfg(test)]
pub(crate) fn pack_objects_peak(objects: impl IntoIterator<Item = PackedObject>) -> u32 {
    let iter = objects.into_iter();
    let (lower_bound, _) = iter.size_hint();
    pack_objects_with_free::<UnsortedFreeList>(iter, lower_bound, |_, _| {})
}

pub(crate) fn pack_zero_min_offset_peak_ranked(
    workspace: &mut PeakPackWorkspace,
    schedule: &ReleaseSchedule,
    items: impl IntoIterator<Item = RankedPeakPackItem>,
    capacity_hint: usize,
) -> u32 {
    workspace.reset(capacity_hint, schedule.order_indices.len());
    let mut max_used: u32 = 0;
    let mut drained_rank = 0usize;
    let mut drained_within_rank = 0usize;

    for item in items {
        while drained_rank < item.start_rank as usize {
            let range = &schedule.by_end_rank[drained_rank];
            while drained_within_rank < range.len() {
                let order_idx = schedule.order_indices[range.start + drained_within_rank] as usize;
                drained_within_rank += 1;
                if workspace.active_epoch[order_idx] == workspace.epoch {
                    workspace.free.insert(
                        workspace.active_off[order_idx],
                        workspace.active_size[order_idx],
                        max_used,
                    );
                }
            }
            drained_rank += 1;
            drained_within_rank = 0;
        }
        if let Some(range) = schedule.by_end_rank.get(drained_rank) {
            while drained_within_rank < range.len() {
                let order_idx = schedule.order_indices[range.start + drained_within_rank];
                if order_idx >= item.order_idx {
                    break;
                }
                drained_within_rank += 1;
                let order_idx = order_idx as usize;
                if workspace.active_epoch[order_idx] == workspace.epoch {
                    workspace.free.insert(
                        workspace.active_off[order_idx],
                        workspace.active_size[order_idx],
                        max_used,
                    );
                }
            }
        }

        if item.size_words == 0 {
            continue;
        }

        let off = if let Some(segment) = workspace.free.take_fit(item.size_words) {
            if segment.len > item.size_words {
                workspace.free.insert(
                    segment
                        .start
                        .checked_add(item.size_words)
                        .expect("free segment overflow"),
                    segment
                        .len
                        .checked_sub(item.size_words)
                        .expect("free segment underflow"),
                    max_used,
                );
            }
            segment.start
        } else if let Some(segment) = workspace.free.take_frontier() {
            if segment.len > item.size_words {
                workspace.free.frontier = Some(FreeSegment {
                    start: segment
                        .start
                        .checked_add(item.size_words)
                        .expect("free segment overflow"),
                    len: segment
                        .len
                        .checked_sub(item.size_words)
                        .expect("free segment underflow"),
                });
            }
            segment.start
        } else {
            max_used
        };
        let order_idx = item.order_idx as usize;
        workspace.active_epoch[order_idx] = workspace.epoch;
        workspace.active_off[order_idx] = off;
        workspace.active_size[order_idx] = item.size_words;
        max_used = max_used.max(
            off.checked_add(item.size_words)
                .expect("locals size overflow"),
        );
    }

    max_used
}

fn pack_objects_impl(
    objects: impl IntoIterator<Item = PackedObject>,
    lower_bound: usize,
    mut record: impl FnMut(StackObjId, u32),
) -> u32 {
    pack_objects_with_free::<SortedFreeList>(objects, lower_bound, &mut record)
}

fn pack_objects_with_free<F: FreeList>(
    objects: impl IntoIterator<Item = PackedObject>,
    lower_bound: usize,
    mut record: impl FnMut(StackObjId, u32),
) -> u32 {
    let mut active: BinaryHeap<Reverse<(u32, u32, u32, u32)>> =
        BinaryHeap::with_capacity(lower_bound);
    let mut free = F::with_capacity(lower_bound);
    let mut max_used: u32 = 0;

    for obj in objects {
        while let Some(Reverse((end, off, size, _id))) = active.peek().copied()
            && end <= obj.interval.start
        {
            let _ = active.pop();
            free.insert(off, size);
        }

        if obj.size_words == 0 {
            record(obj.id, 0);
            continue;
        }

        let off = if let Some(segment) = free.take_fit(obj.min_offset_words, obj.size_words) {
            let (alloc_start, prefix, suffix) =
                split_free_segment(segment, obj.min_offset_words, obj.size_words);
            free.insert(prefix.start, prefix.len);
            free.insert(suffix.start, suffix.len);
            alloc_start
        } else {
            let old_max_used = max_used;
            if let Some(segment) = free.take_frontier_segment(old_max_used) {
                let alloc_start = segment.start.max(obj.min_offset_words);
                free.insert(
                    segment.start,
                    alloc_start
                        .checked_sub(segment.start)
                        .expect("free segment underflow"),
                );
                alloc_start
            } else {
                let alloc_start = obj.min_offset_words.max(old_max_used);
                free.insert(
                    old_max_used,
                    alloc_start
                        .checked_sub(old_max_used)
                        .expect("free segment underflow"),
                );
                alloc_start
            }
        };

        record(obj.id, off);
        active.push(Reverse((
            obj.interval.end,
            off,
            obj.size_words,
            obj.id.as_u32(),
        )));
        max_used = max_used.max(
            off.checked_add(obj.size_words)
                .expect("locals size overflow"),
        );
    }

    max_used
}

fn split_free_segment(
    segment: FreeSegment,
    min_offset_words: u32,
    size_words: u32,
) -> (u32, FreeSegment, FreeSegment) {
    let end = segment
        .start
        .checked_add(segment.len)
        .expect("free segment overflow");
    let alloc_start = segment.start.max(min_offset_words);
    let alloc_end = alloc_start
        .checked_add(size_words)
        .expect("free segment overflow");
    (
        alloc_start,
        FreeSegment {
            start: segment.start,
            len: alloc_start
                .checked_sub(segment.start)
                .expect("free segment underflow"),
        },
        FreeSegment {
            start: alloc_end,
            len: end.checked_sub(alloc_end).expect("free segment underflow"),
        },
    )
}

fn find_first_fit_segment(
    free: &[FreeSegment],
    min_offset_words: u32,
    size_words: u32,
) -> Option<usize> {
    free.iter()
        .position(|segment| free_segment_fits(*segment, min_offset_words, size_words))
}

#[cfg(test)]
fn find_min_start_fit_segment(
    free: &[FreeSegment],
    min_offset_words: u32,
    size_words: u32,
) -> Option<usize> {
    let mut best: Option<(usize, u32)> = None;
    for (index, segment) in free.iter().enumerate() {
        if !free_segment_fits(*segment, min_offset_words, size_words) {
            continue;
        }
        match best {
            None => best = Some((index, segment.start)),
            Some((_, best_start)) if segment.start < best_start => {
                best = Some((index, segment.start));
            }
            _ => {}
        }
    }
    best.map(|(index, _)| index)
}

fn free_segment_fits(segment: FreeSegment, min_offset_words: u32, size_words: u32) -> bool {
    let alloc_start = segment.start.max(min_offset_words);
    let alloc_end = alloc_start
        .checked_add(size_words)
        .expect("free segment overflow");
    segment.end() >= alloc_end
}

fn insert_free_segment_sorted(free: &mut Vec<FreeSegment>, start: u32, len: u32) {
    if len == 0 {
        return;
    }

    let mut start = start;
    let mut len = len;
    let mut index = free
        .binary_search_by_key(&start, |segment| segment.start)
        .unwrap_or_else(|index| index);

    if index != 0 {
        let prev = free[index - 1];
        if prev.end() == start {
            start = prev.start;
            len = len.checked_add(prev.len).expect("free segment overflow");
            let _ = free.remove(index - 1);
            index -= 1;
        }
    }

    if index < free.len() {
        let next = free[index];
        let end = start.checked_add(len).expect("free segment overflow");
        if end == next.start {
            len = len.checked_add(next.len).expect("free segment overflow");
            let _ = free.remove(index);
        }
    }

    free.insert(index, FreeSegment { start, len });
}

#[cfg(test)]
fn insert_free_segment_unsorted(free: &mut Vec<FreeSegment>, start: u32, len: u32) {
    if len == 0 {
        return;
    }

    let mut start = start;
    let mut len = len;
    let mut index = 0;
    while index < free.len() {
        let segment = free[index];
        let end = start.checked_add(len).expect("free segment overflow");
        if segment.end() == start {
            start = segment.start;
            len = len.checked_add(segment.len).expect("free segment overflow");
            let _ = free.swap_remove(index);
            continue;
        }
        if end == segment.start {
            len = len.checked_add(segment.len).expect("free segment overflow");
            let _ = free.swap_remove(index);
            continue;
        }
        index += 1;
    }

    free.push(FreeSegment { start, len });
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
