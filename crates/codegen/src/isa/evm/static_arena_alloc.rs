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
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};
use std::{
    cmp::Reverse,
    collections::{BTreeMap, BinaryHeap},
};

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
enum StackObjKind {
    Alloca(InstId),
    Spill(ValueId),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct LiveInterval {
    start: u32,
    end: u32,
}

#[derive(Clone, Debug)]
struct StackObj {
    id: StackObjId,
    kind: StackObjKind,
    size_words: u32,
    interval: LiveInterval,
    min_offset_words: u32,
}

pub(crate) struct FuncObjectLayout {
    pub(crate) obj_offset_words: FxHashMap<StackObjId, u32>,
    pub(crate) alloca_offset_words: FxHashMap<InstId, u32>,
    pub(crate) spill_obj: SecondaryMap<ValueId, Option<StackObjId>>,
    pub(crate) locals_words: u32,
}

pub(crate) struct CallSiteLiveObjects {
    pub(crate) inst: InstId,
    pub(crate) callee: FuncRef,
    pub(crate) has_return: bool,
    pub(crate) arg_count: u8,
    pub(crate) live_out_objs: Vec<StackObjId>,
    pub(crate) must_layout_objs: Vec<StackObjId>,
}

pub(crate) struct FuncStackObjects {
    objects: Vec<StackObj>,
    pub(crate) obj_size_words: FxHashMap<StackObjId, u32>,
    pub(crate) alloca_ids: FxHashMap<InstId, StackObjId>,
    pub(crate) spill_obj: SecondaryMap<ValueId, Option<StackObjId>>,
    pub(crate) call_sites: Vec<CallSiteLiveObjects>,
    pub(crate) requires_dynamic_frame: bool,
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

    pub(crate) fn plan_func_objects(
        &self,
        func_ref: FuncRef,
        function: &Function,
        analysis: &FuncAnalysis,
    ) -> FuncObjectLayout {
        let stack = self.compute_func_stack_objects(func_ref, function, analysis);
        let min_offset_words: FxHashMap<StackObjId, u32> = FxHashMap::default();
        let (obj_offset_words, locals_words) =
            pack_objects_with_min_offsets(&stack, &min_offset_words);
        build_func_object_layout(&stack, obj_offset_words, locals_words)
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
            .arg_may_be_returned
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
    for v in function.dfg.values.keys() {
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
        ctx.isa,
        &inst_order,
        &inst_pos,
        &block_end_pos,
        &analysis.inst_liveness,
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
            min_offset_words: 0,
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
            min_offset_words: 0,
        });
    }

    let mut requires_dynamic_frame = false;
    let mut call_sites: Vec<CallSiteLiveObjects> = Vec::new();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let Some(call) = function.dfg.cast_call(inst) else {
                continue;
            };
            let arg_count = u8::try_from(call.args().len()).expect("call arg count too large");

            let def = function.dfg.inst_result(inst);
            let mut set: FxHashSet<StackObjId> = FxHashSet::default();
            let mut roots: FxHashSet<InstId> = FxHashSet::default();
            for v in analysis.inst_liveness.live_out(inst).iter() {
                if Some(v) == def {
                    continue;
                }

                if let Some(obj) = spill_obj[v] {
                    set.insert(obj);
                }

                for base in prov[v].alloca_insts() {
                    roots.insert(base);
                }
            }

            let allocas = if requires_dynamic_frame {
                roots
            } else {
                match closure_allocas(roots.iter().copied(), &local_edges, &local_unknown) {
                    Ok(s) => s,
                    Err(UnknownLocalPtr) => {
                        requires_dynamic_frame = true;
                        roots
                    }
                }
            };
            for base in allocas {
                if let Some(&id) = alloca_ids.get(&base) {
                    set.insert(id);
                }
            }

            let mut live_objs: Vec<StackObjId> = set.into_iter().collect();
            live_objs.sort_unstable_by_key(|id| id.as_u32());

            let mut must_layout: FxHashSet<StackObjId> = FxHashSet::default();
            let mut roots: FxHashSet<InstId> = FxHashSet::default();
            for &arg in call.args() {
                for base in prov[arg].alloca_insts() {
                    roots.insert(base);
                }
            }
            let allocas = if requires_dynamic_frame {
                roots
            } else {
                match closure_allocas(roots.iter().copied(), &local_edges, &local_unknown) {
                    Ok(s) => s,
                    Err(UnknownLocalPtr) => {
                        requires_dynamic_frame = true;
                        roots
                    }
                }
            };
            for base in allocas {
                if let Some(&id) = alloca_ids.get(&base) {
                    must_layout.insert(id);
                }
            }
            let mut must_layout_objs: Vec<StackObjId> = must_layout.into_iter().collect();
            must_layout_objs.sort_unstable_by_key(|id| id.as_u32());
            call_sites.push(CallSiteLiveObjects {
                inst,
                callee: *call.callee(),
                has_return: function.dfg.inst_result(inst).is_some(),
                arg_count,
                live_out_objs: live_objs,
                must_layout_objs,
            });
        }
    }

    let mut obj_size_words: FxHashMap<StackObjId, u32> = FxHashMap::default();
    for obj in &objects {
        obj_size_words.insert(obj.id, obj.size_words);
    }

    FuncStackObjects {
        objects,
        obj_size_words,
        alloca_ids,
        spill_obj,
        call_sites,
        requires_dynamic_frame,
    }
}

pub(crate) fn pack_objects_with_min_offsets(
    stack: &FuncStackObjects,
    min_offset_words: &FxHashMap<StackObjId, u32>,
) -> (FxHashMap<StackObjId, u32>, u32) {
    let mut objs: Vec<StackObj> = stack.objects.clone();
    for obj in &mut objs {
        if let Some(k) = min_offset_words.get(&obj.id) {
            obj.min_offset_words = (*k).max(obj.min_offset_words);
        }
    }
    pack_objects(&mut objs)
}

pub(crate) fn build_func_object_layout(
    stack: &FuncStackObjects,
    obj_offset_words: FxHashMap<StackObjId, u32>,
    locals_words: u32,
) -> FuncObjectLayout {
    let mut alloca_offset_words: FxHashMap<InstId, u32> = FxHashMap::default();
    for (inst, id) in stack.alloca_ids.iter() {
        if let Some(off) = obj_offset_words.get(id) {
            alloca_offset_words.insert(*inst, *off);
        }
    }

    FuncObjectLayout {
        obj_offset_words,
        alloca_offset_words,
        spill_obj: stack.spill_obj.clone(),
        locals_words,
    }
}

#[cfg(debug_assertions)]
pub(crate) fn verify_object_packing(
    func_ref: FuncRef,
    stack: &FuncStackObjects,
    obj_offset_words: &FxHashMap<StackObjId, u32>,
    locals_words: u32,
) {
    let mut max_end: u32 = 0;
    for obj in &stack.objects {
        let off = obj_offset_words
            .get(&obj.id)
            .copied()
            .unwrap_or_else(|| panic!("missing offset for obj {}", obj.id.as_u32()));
        let end = off
            .checked_add(obj.size_words)
            .unwrap_or_else(|| panic!("obj {} end overflows", obj.id.as_u32()));

        max_end = max_end.max(end);
        if end > locals_words {
            panic!(
                "StaticArena density violated in func {}: obj {} ends at {end} > locals_words={locals_words}",
                func_ref.as_u32(),
                obj.id.as_u32()
            );
        }
    }
    if max_end != locals_words {
        panic!(
            "StaticArena locals_words mismatch in func {}: locals_words={locals_words} but max_end={max_end}",
            func_ref.as_u32()
        );
    }

    let objects = &stack.objects;
    for i in 0..objects.len() {
        for j in (i + 1)..objects.len() {
            let o1 = &objects[i];
            let o2 = &objects[j];
            if o1.size_words == 0
                || o2.size_words == 0
                || o1.interval.end < o2.interval.start
                || o2.interval.end < o1.interval.start
            {
                continue;
            }

            let off1 = obj_offset_words[&o1.id];
            let off2 = obj_offset_words[&o2.id];
            let end1 = off1 + o1.size_words;
            let end2 = off2 + o2.size_words;
            if end1 <= off2 || end2 <= off1 {
                continue;
            }

            panic!(
                "StaticArena overlap in func {}: {:?}@[{off1},{end1}) vs {:?}@[{off2},{end2}) (intervals {:?} vs {:?})",
                func_ref.as_u32(),
                o1.kind,
                o2.kind,
                o1.interval,
                o2.interval,
            );
        }
    }
}

fn compute_spill_intervals(
    function: &Function,
    isa: &Evm,
    inst_order: &[InstId],
    inst_pos: &FxHashMap<InstId, u32>,
    block_end_pos: &FxHashMap<BlockId, u32>,
    inst_liveness: &InstLiveness,
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
                if spilled.contains(*val) {
                    let use_pos = block_end_pos.get(pred).copied().unwrap_or_default();
                    end.entry(*val).and_modify(|e| *e = (*e).max(use_pos));
                }
            }
        } else {
            function.dfg.inst(inst).for_each_value(&mut |v| {
                if spilled.contains(v) {
                    end.entry(v).and_modify(|e| *e = (*e).max(pos));
                }
            });
        }

        for v in inst_liveness.live_out(inst).iter() {
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

fn pack_objects(objects: &mut [StackObj]) -> (FxHashMap<StackObjId, u32>, u32) {
    objects.sort_unstable_by_key(|o| (o.interval.start, o.interval.end, o.id.as_u32()));

    let mut out: FxHashMap<StackObjId, u32> = FxHashMap::default();
    let mut active: BinaryHeap<Reverse<(u32, u32, u32, u32)>> = BinaryHeap::new(); // (end, off, size, id)
    let mut free: BTreeMap<u32, u32> = BTreeMap::new(); // start -> len
    let mut max_used: u32 = 0;

    for obj in objects.iter() {
        while let Some(Reverse((end, off, size, _id))) = active.peek().copied()
            && end < obj.interval.start
        {
            let _ = active.pop();
            insert_free_segment(&mut free, off, size);
        }

        if obj.size_words == 0 {
            out.insert(obj.id, 0);
            continue;
        }

        let mut found: Option<(u32, u32)> = free
            .range(..=obj.min_offset_words)
            .next_back()
            .filter(|&(&start, &len)| {
                let end = start.checked_add(len).expect("free segment overflow");
                let alloc_start = start.max(obj.min_offset_words);
                let alloc_end = alloc_start
                    .checked_add(obj.size_words)
                    .expect("free segment overflow");
                end >= alloc_end
            })
            .map(|(&start, &len)| (start, len));

        if found.is_none() {
            found = free
                .range(obj.min_offset_words..)
                .find(|&(_, &len)| len >= obj.size_words)
                .map(|(&start, &len)| (start, len));
        }

        let off = if let Some((start, len)) = found {
            free.remove(&start);

            let end = start.checked_add(len).expect("free segment overflow");
            let alloc_start = start.max(obj.min_offset_words);
            let alloc_end = alloc_start
                .checked_add(obj.size_words)
                .expect("free segment overflow");

            insert_free_segment(
                &mut free,
                start,
                alloc_start
                    .checked_sub(start)
                    .expect("free segment underflow"),
            );
            insert_free_segment(
                &mut free,
                alloc_end,
                end.checked_sub(alloc_end).expect("free segment underflow"),
            );

            alloc_start
        } else {
            let off = obj.min_offset_words.max(max_used);
            max_used = off
                .checked_add(obj.size_words)
                .expect("locals size overflow");
            off
        };

        out.insert(obj.id, off);
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

    (out, max_used)
}

fn insert_free_segment(free: &mut BTreeMap<u32, u32>, start: u32, len: u32) {
    if len == 0 {
        return;
    }

    let mut start = start;
    let mut len = len;

    if let Some((&p_start, &p_len)) = free.range(..start).next_back() {
        let p_end = p_start.checked_add(p_len).expect("free segment overflow");
        if p_end == start {
            start = p_start;
            len = len.checked_add(p_len).expect("free segment overflow");
            free.remove(&p_start);
        }
    }

    if let Some((&n_start, &n_len)) = free.range(start..).next() {
        let end = start.checked_add(len).expect("free segment overflow");
        if end == n_start {
            len = len.checked_add(n_len).expect("free segment overflow");
            free.remove(&n_start);
        }
    }

    free.insert(start, len);
}

fn conservative_unknown_ptr_summary(module: &ModuleCtx, func_ref: FuncRef) -> PtrEscapeSummary {
    let arg_count = module.func_sig(func_ref, |sig| sig.args().len());
    PtrEscapeSummary {
        arg_may_escape: vec![true; arg_count],
        arg_may_be_returned: vec![true; arg_count],
        returns_any_ptr: module.func_sig(func_ref, |sig| sig.ret_ty().is_pointer(module)),
    }
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
                EvmInstKind::Return(ret) => {
                    let Some(ret_val) = *ret.arg() else {
                        continue;
                    };
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
