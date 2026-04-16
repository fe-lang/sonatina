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

use crate::bitset::BitSet;
use cranelift_entity::{EntityRef, SecondaryMap, entity_impl};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstId, InstSetExt, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use super::{
    escape_scan::{EscapeScanCtx, EscapeSink, EscapeSource, for_each_escape_event_at_inst},
    memory_plan::{FuncAnalysis, WORD_BYTES},
    provenance::{Provenance, compute_provenance},
    ptr_escape::PtrEscapeSummary,
};

mod exact_pack;
mod object_liveness;

pub(crate) use exact_pack::{
    ExactPackItem, PackedObject, pack_exact_peak, pack_exact_with_offsets, pack_objects_presorted,
};
#[cfg(test)]
pub(crate) use object_liveness::BlockLiveSegment;
pub(crate) use object_liveness::LiveRegion;
use object_liveness::{
    AllocaClosureCtx, ComputeCtx as ObjectLivenessCtx, compute_regions_and_calls,
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

    let escaping_sites = compute_escaping_allocas(
        function,
        ctx.module,
        ctx.isa,
        ctx.ptr_escape,
        prov,
        &prov_info.local_mem,
    );
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
    let mut liveness_ctx = ObjectLivenessCtx {
        analysis,
        isa: ctx.isa,
        prov,
        spill_local_by_value: &spill_local_by_value,
        alloca_local_by_inst: &alloca_local_by_inst,
        closure: &closure,
        unknown_barrier_objs: &mut unknown_barrier_objs,
        obj_id_by_local: &obj_id_by_local,
        alloca_ids: &alloca_ids,
    };
    let (regions, call_sites) =
        compute_regions_and_calls(function, &cfg, &block_order, &mut liveness_ctx);
    for (idx, region) in regions.into_iter().enumerate() {
        objects[idx].region = region;
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

fn conservative_unknown_ptr_summary(module: &ModuleCtx, func_ref: FuncRef) -> PtrEscapeSummary {
    PtrEscapeSummary::conservative_unknown_ctx(module, func_ref)
}

fn compute_escaping_allocas(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    prov: &SecondaryMap<ValueId, Provenance>,
    local_mem: &FxHashMap<InstId, Provenance>,
) -> FxHashMap<InstId, Vec<AllocaEscapeSite>> {
    let mut escaping: FxHashMap<InstId, Vec<AllocaEscapeSite>> = FxHashMap::default();
    let scan_ctx = EscapeScanCtx {
        module,
        isa,
        ptr_escape,
        prov,
        local_mem,
    };

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            for_each_escape_event_at_inst(function, inst, scan_ctx, |event| match event.source {
                EscapeSource::Value(value) => {
                    let site = match event.sink {
                        EscapeSink::Return => AllocaEscapeSite::Return {
                            inst: event.inst,
                            value,
                        },
                        EscapeSink::NonLocalStore => AllocaEscapeSite::NonLocalStore {
                            inst: event.inst,
                            value,
                        },
                        EscapeSink::CallArg { callee, arg_index } => AllocaEscapeSite::CallArg {
                            inst: event.inst,
                            callee,
                            arg_index,
                            value,
                        },
                        EscapeSink::NonLocalCopy => {
                            unreachable!("mcopy does not emit direct-value escapes")
                        }
                    };
                    for base in prov[value].alloca_insts() {
                        escaping.entry(base).or_default().push(site.clone());
                    }
                }
                EscapeSource::LocalMem { addr, stored } => {
                    for base in stored.alloca_insts() {
                        escaping
                            .entry(base)
                            .or_default()
                            .push(AllocaEscapeSite::NonLocalCopy {
                                inst: event.inst,
                                addr,
                            });
                    }
                }
                EscapeSource::UnknownCopy => {}
            });
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
        value: ValueId,
    },
    NonLocalCopy {
        inst: InstId,
        addr: ValueId,
    },
    CallArg {
        inst: InstId,
        callee: FuncRef,
        arg_index: usize,
        value: ValueId,
    },
}

impl AllocaEscapeSite {
    fn sort_key(&self) -> (u32, u8, u32, u32) {
        match self {
            AllocaEscapeSite::Return { inst, value } => (inst.as_u32(), 0, value.as_u32(), 0),
            AllocaEscapeSite::NonLocalStore { inst, value } => {
                (inst.as_u32(), 1, value.as_u32(), 0)
            }
            AllocaEscapeSite::NonLocalCopy { inst, addr } => (inst.as_u32(), 2, addr.as_u32(), 0),
            AllocaEscapeSite::CallArg {
                inst,
                arg_index,
                value,
                ..
            } => (inst.as_u32(), 3, *arg_index as u32, value.as_u32()),
        }
    }

    fn render(&self, module: &ModuleCtx) -> String {
        match self {
            AllocaEscapeSite::Return { inst, value } => {
                format!("return of v{} at inst {}", value.as_u32(), inst.as_u32())
            }
            AllocaEscapeSite::NonLocalStore { inst, value } => format!(
                "non-local store of v{} at inst {}",
                value.as_u32(),
                inst.as_u32()
            ),
            AllocaEscapeSite::NonLocalCopy { inst, addr } => format!(
                "non-local copy of local pointer bytes from addr v{} at inst {}",
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
        sites.sort_unstable_by_key(AllocaEscapeSite::sort_key);
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
    #[should_panic(expected = "alloca escapes in store8_escape")]
    fn alloca_escape_via_nonlocal_mstore8_panics() {
        let _ = analyze_function(
            r#"
target = "evm-ethereum-osaka"

func private %store8_escape() -> i256 {
block0:
    v0.*i256 = alloca i256;
    v1.i256 = ptr_to_int v0 i256;
    evm_mstore8 0.i32 v1;
    return 0.i256;
}
"#,
            "store8_escape",
            16,
        );
    }

    #[test]
    #[should_panic(expected = "alloca escapes in mcopy_escape")]
    fn alloca_escape_via_nonlocal_mcopy_panics() {
        let _ = analyze_function(
            r#"
target = "evm-ethereum-osaka"

func private %mcopy_escape() -> i256 {
block0:
    v0.**i256 = alloca *i256;
    v1.*i256 = alloca i256;
    mstore v0 v1 *i256;
    evm_mcopy 0.i8 v0 32.i256;
    return 0.i256;
}
"#,
            "mcopy_escape",
            16,
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
