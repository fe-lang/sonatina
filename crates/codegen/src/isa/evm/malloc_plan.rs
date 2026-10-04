use cranelift_entity::SecondaryMap;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, AccessLoc, BlockId, Function, InstId, InstSetExt, Module, Type, Value, ValueId,
    cfg::ControlFlowGraph,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        data::{Mload, Mstore},
        evm::inst_set::EvmInstKind,
    },
    isa::{
        Isa,
        evm::{Evm, space::MEMORY},
    },
    module::{FuncRef, ModuleCtx},
};

use crate::{bitset::BitSet, liveness::InstLiveness, module_analysis::CallGraphSchedule};

use super::{
    escape_scan::{
        EscapeScanCtx, EscapeSink, EscapeSource, escape_source_may_be_heap_derived,
        for_each_escape_event_at_inst,
    },
    memory_plan::SemanticFuncPlan,
    private_malloc::PrivateMallocUseAnalysis,
    ptr_escape::PtrEscapeSummary,
    ptr_provenance::{Provenance, ProvenanceInfo},
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct MallocEscapeKind(u8);

impl MallocEscapeKind {
    pub(crate) const RETURNS_TO_CALLER: Self = Self(1 << 0);
    pub(crate) const STORED_NON_LOCAL: Self = Self(1 << 1);
    pub(crate) const UNKNOWN: Self = Self(1 << 2);

    pub(crate) fn has_global_or_unknown(self) -> bool {
        self.contains(Self::STORED_NON_LOCAL) || self.contains(Self::UNKNOWN)
    }

    fn contains(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
}

pub(crate) type TransientMallocCallBarriers = FxHashMap<FuncRef, bool>;

/// Computes whether calls to each function can invalidate transient mallocs.
pub(crate) fn compute_transient_malloc_call_barriers(
    module: &Module,
    schedule: &CallGraphSchedule,
    semantic_plans: &FxHashMap<FuncRef, SemanticFuncPlan>,
    isa: &Evm,
) -> TransientMallocCallBarriers {
    let mut local_results: Vec<_> = schedule
        .funcs()
        .par_iter()
        .copied()
        .map(|func| {
            let uses_dynamic_frame = semantic_plans
                .get(&func)
                .is_some_and(|plan| plan.dynamic_frame_layout().is_some());
            let uses_malloc = module
                .func_store
                .view(func, |function| func_uses_malloc(function, isa));
            (func, uses_dynamic_frame || uses_malloc)
        })
        .collect();
    local_results.sort_unstable_by_key(|(func, _)| func.as_u32());
    let local_barriers: TransientMallocCallBarriers = local_results.into_iter().collect();

    schedule.join_over_callees(
        |func| local_barriers[&func],
        |barrier, callee_barrier| *barrier |= *callee_barrier,
    )
}

pub(crate) fn should_restore_free_ptr_on_internal_returns(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    prov_info: &ProvenanceInfo,
    transient_mallocs: &FxHashSet<InstId>,
) -> bool {
    let mut has_internal_return = false;
    let mut has_persistent_malloc = false;

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            if let EvmInstKind::Call(call) = data
                && PtrEscapeSummary::get_or_conservative(ptr_escape, module, *call.callee())
                    .may_publish_heap
            {
                // Restoring the entry cursor also frees allocations published
                // by callees, even when no caller-owned pointer escapes.
                return false;
            }
            if matches!(data, EvmInstKind::Return(_)) {
                has_internal_return = true;
            }
            if matches!(data, EvmInstKind::EvmMalloc(_)) && !transient_mallocs.contains(&inst) {
                has_persistent_malloc = true;
            }
        }
    }

    if !has_internal_return || !has_persistent_malloc {
        return false;
    }

    let scan_ctx = EscapeScanCtx::new(function, module, isa, ptr_escape, prov_info);

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let mut escapes_heap = false;
            for_each_escape_event_at_inst(function, inst, &scan_ctx, |event| {
                escapes_heap |=
                    escape_source_may_be_heap_derived(function, &scan_ctx, &event.source);
            });
            if escapes_heap {
                return false;
            }
        }
    }

    true
}

pub(crate) fn insert_free_ptr_restore_on_internal_returns(function: &mut Function, isa: &Evm) {
    let Some(entry) = function.layout.entry_block() else {
        return;
    };

    let addr = function.dfg.make_imm_value(64i32);

    let mut insert_loc = CursorLocation::BlockTop(entry);
    for inst in function.layout.iter_inst(entry) {
        if function.dfg.is_phi(inst) {
            insert_loc = CursorLocation::At(inst);
        } else {
            break;
        }
    }

    let mut cursor = InstInserter::at_location(insert_loc);
    let load_inst = cursor.insert_inst_data(function, Mload::new(isa.inst_set(), addr, Type::I256));
    let saved = cursor.make_result(function, load_inst, Type::I256);
    cursor.attach_result(function, load_inst, saved);

    let mut return_insts: Vec<(sonatina_ir::BlockId, InstId)> = Vec::new();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if matches!(
                isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::Return(_)
            ) {
                return_insts.push((block, inst));
            }
        }
    }

    for (block, ret_inst) in return_insts {
        let prev = function.layout.prev_inst_of(ret_inst);
        let loc = prev.map_or(CursorLocation::BlockTop(block), CursorLocation::At);
        let mut cursor = InstInserter::at_location(loc);
        let _ = cursor.insert_inst_data(
            function,
            Mstore::new(isa.inst_set(), addr, saved, Type::I256),
        );
    }
}

pub(crate) fn compute_transient_mallocs(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    prov_info: &ProvenanceInfo,
    call_barriers: Option<&TransientMallocCallBarriers>,
    inst_liveness: &InstLiveness,
) -> FxHashSet<InstId> {
    let mut mallocs: FxHashSet<InstId> = FxHashSet::default();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if matches!(
                isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::EvmMalloc(_)
            ) {
                mallocs.insert(inst);
            }
        }
    }

    if mallocs.is_empty() {
        return FxHashSet::default();
    }

    let scan_ctx = EscapeScanCtx::new(function, module, isa, ptr_escape, prov_info);

    let block_malloc_in = compute_block_malloc_in(function, isa);
    let escape_kinds = compute_malloc_escape_kinds(function, &scan_ctx, &block_malloc_in);

    for malloc in escape_kinds.keys() {
        mallocs.remove(malloc);
    }

    let address_barriers = unknown_data_address_barriers(function, isa, prov_info);
    let private_mallocs: FxHashSet<_> = mallocs
        .iter()
        .copied()
        .filter(|&inst| {
            let EvmInstKind::EvmMalloc(malloc) =
                isa.inst_set().resolve_inst(function.dfg.inst(inst))
            else {
                return false;
            };
            address_barriers.is_some()
                && PrivateMallocUseAnalysis::new(function, module, isa, inst)
                    .analyze_bounded_private_address_uses(*malloc.size(), false)
                    .is_some()
        })
        .collect();

    for block in function.layout.iter_block() {
        let mut seen_mallocs = block_malloc_in[block].clone();
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));

            if matches!(data, EvmInstKind::EvmMalloc(_)) {
                let mut live = inst_liveness.live_out(inst).clone();
                for def in function.dfg.inst_results(inst) {
                    live.remove(*def);
                }

                remove_live_mallocs(
                    &mut mallocs,
                    &live,
                    prov_info,
                    &seen_mallocs,
                    &private_mallocs,
                    address_barriers
                        .as_ref()
                        .is_none_or(|barriers| barriers.contains(inst)),
                );
                seen_mallocs.insert(inst);
                continue;
            }

            let Some(call_info) = function.dfg.call_info(inst) else {
                continue;
            };

            let callee = call_info.callee();
            let is_barrier = call_barriers.is_none_or(|barriers| {
                *barriers.get(&callee).unwrap_or_else(|| {
                    panic!(
                        "missing transient malloc call barrier for callee {}",
                        callee.as_u32()
                    )
                })
            });
            if !is_barrier {
                continue;
            }

            // If a call can allocate or shift the dynamic stack pointer, then any malloc-derived
            // pointer passed *to* the call must be treated as non-transient, even if it is not
            // live after the call returns: the callee may allocate (or enter a frame) before it
            // dereferences the pointer argument, clobbering the pointed-to memory.
            let mut live = inst_liveness.live_out(inst).clone();
            let call = function
                .dfg
                .cast_call(inst)
                .expect("call_info must correspond to Call");
            for &arg in call.args() {
                live.insert(arg);
            }
            remove_live_mallocs(
                &mut mallocs,
                &live,
                prov_info,
                &seen_mallocs,
                &private_mallocs,
                address_barriers
                    .as_ref()
                    .is_none_or(|barriers| barriers.contains(inst)),
            );
        }
    }

    mallocs
}

fn func_uses_malloc(function: &Function, isa: &Evm) -> bool {
    function.layout.iter_block().any(|block| {
        function.layout.iter_inst(block).any(|inst| {
            matches!(
                isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::EvmMalloc(_)
            )
        })
    })
}

pub(crate) fn compute_malloc_escape_kinds_for_function(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    prov_info: &ProvenanceInfo,
) -> FxHashMap<InstId, MallocEscapeKind> {
    let scan_ctx = EscapeScanCtx::new(function, module, isa, ptr_escape, prov_info);
    let block_malloc_in = compute_block_malloc_in(function, isa);
    compute_malloc_escape_kinds(function, &scan_ctx, &block_malloc_in)
}

fn remove_live_mallocs(
    mallocs: &mut FxHashSet<InstId>,
    live: &BitSet<ValueId>,
    prov_info: &ProvenanceInfo,
    seen_mallocs: &BitSet<InstId>,
    private_mallocs: &FxHashSet<InstId>,
    unknown_address_is_reachable: bool,
) {
    let mut roots = Provenance::default();
    for value in live.iter() {
        let provenance = &prov_info.value[value];
        roots.union_with(provenance);
    }
    // Pointers saved in nested local or private heap containers remain live
    // even after their original SSA values die. Follow both kinds of storage.
    let reachable = prov_info.reachable_memory(&roots);
    for base in reachable.malloc_insts() {
        mallocs.remove(&base);
    }
    if reachable.is_unknown_ptr() {
        mallocs.retain(|malloc| {
            !seen_mallocs.contains(*malloc)
                || (!unknown_address_is_reachable && private_mallocs.contains(malloc))
        });
    }
}

/// Unknown scalar data does not retain an unobservable private buffer unless
/// it can be used as an address. Known roots are still closed over memory by
/// `remove_live_mallocs`; this only proves when additional unknown roots do not
/// apply. If memory contents can feed an address, preserve the original whole-
/// container barrier, including aliases and stores not represented in SSA.
fn unknown_data_address_barriers(
    function: &Function,
    isa: &Evm,
    prov_info: &ProvenanceInfo,
) -> Option<BitSet<InstId>> {
    let mut uses = BitSet::default();
    let mut direct_uses: SecondaryMap<InstId, BitSet<ValueId>> = SecondaryMap::new();
    for inst in function.layout.iter_all_insts() {
        if function.dfg.call_info(inst).is_some() {
            // A callee can interpret stored words as pointers without a local
            // SSA load. Retain the barrier until a read-demand summary proves it.
            return None;
        }
        if matches!(
            isa.inst_set().resolve_inst(function.dfg.inst(inst)),
            EvmInstKind::EvmMalloc(_)
        ) {
            continue;
        }
        if let Some(values) = function.dfg.return_args(inst) {
            for &value in values {
                uses.insert(value);
                direct_uses[inst].insert(value);
            }
        }
        for access in function.dfg.effects(inst).accesses {
            if access.space != MEMORY {
                continue;
            }
            let addr = match access.loc {
                AccessLoc::LinearExact { addr, bytes, .. } if bytes != 0 => addr,
                AccessLoc::LinearRange { addr, len }
                    if !function.dfg.value_imm(len).is_some_and(|len| len.is_zero()) =>
                {
                    // Extending a range can observe unrelated allocations just
                    // as changing its starting address can.
                    uses.insert(len);
                    direct_uses[inst].insert(len);
                    addr
                }
                AccessLoc::LinearExact { .. }
                | AccessLoc::LinearRange { .. }
                | AccessLoc::LinearExactImm { .. } => continue,
                _ => return None,
            };
            if prov_info.value[addr].has_no_known_bases() && function.dfg.value_imm(addr).is_none()
            {
                // Raw numeric addresses can alias a private buffer even when
                // computed from constants. Only fixed immediate ranges have
                // separate reservation evidence.
                return None;
            }
            // A known base does not make its address calculation private:
            // GEP indices and other offsets can still come from unknown data.
            uses.insert(addr);
            direct_uses[inst].insert(addr);
        }
    }
    loop {
        let mut changed = false;
        for inst in function.layout.iter_all_insts() {
            if !function
                .dfg
                .inst_results(inst)
                .iter()
                .any(|&value| uses.contains(value))
            {
                continue;
            }
            if matches!(
                isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::Alloca(_) | EvmInstKind::EvmMalloc(_)
            ) {
                // Fresh allocation addresses do not expose their size operands
                // as pointers. Their known roots remain lifetime barriers.
                continue;
            }
            if function
                .dfg
                .effects(inst)
                .accesses
                .iter()
                .any(|access| access.space == MEMORY && access.kind == AccessKind::Read)
            {
                return None;
            }
            function.dfg.inst(inst).for_each_value(&mut |value| {
                changed |= uses.insert(value);
            });
        }
        if !changed {
            break;
        }
    }

    // A counter computed from literals can contribute to an address without
    // carrying unknown pointer bits. Seed opaque inputs, then propagate only
    // along demanded computations; loop phis converge without tainting such
    // counters. Known allocation roots are handled separately by liveness.
    let mut unknown = BitSet::default();
    for value in uses.iter() {
        match function.dfg.get_value(value)? {
            Value::Immediate { .. } => {}
            Value::Inst { inst, .. } => {
                if matches!(
                    isa.inst_set().resolve_inst(function.dfg.inst(*inst)),
                    EvmInstKind::Alloca(_) | EvmInstKind::EvmMalloc(_)
                ) {
                    continue;
                }
                if function.dfg.effects(*inst).summary().has_effect()
                    || function.dfg.inst(*inst).collect_values().is_empty()
                {
                    unknown.insert(value);
                }
            }
            _ => {
                unknown.insert(value);
            }
        }
    }
    loop {
        let mut changed = false;
        for inst in function.layout.iter_all_insts() {
            if matches!(
                isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::Alloca(_) | EvmInstKind::EvmMalloc(_)
            ) || !function
                .dfg
                .inst(inst)
                .collect_values()
                .iter()
                .any(|value| unknown.contains(*value))
            {
                continue;
            }
            for &result in function.dfg.inst_results(inst) {
                if uses.contains(result) {
                    changed |= unknown.insert(result);
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Values can remain live as scalar data after their last address use. Only
    // memory observations reachable after the allocation can keep earlier
    // private buffers alive. Include backedges, but not initialization on an
    // entry path that cannot execute again.
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);
    let mut block_in: SecondaryMap<BlockId, bool> = SecondaryMap::new();
    let mut barriers = BitSet::default();
    loop {
        let mut changed = false;
        for block in cfg.post_order() {
            let mut future = cfg.succs_of(block).any(|succ| block_in[*succ]);
            let insts: Vec<_> = function.layout.iter_inst(block).collect();
            for inst in insts.into_iter().rev() {
                if future {
                    barriers.insert(inst);
                }
                future |= direct_uses[inst]
                    .iter()
                    .any(|value| unknown.contains(value));
            }
            if future && !block_in[block] {
                block_in[block] = true;
                changed = true;
            }
        }
        if !changed {
            return Some(barriers);
        }
    }
}

fn compute_block_malloc_in(
    function: &Function,
    isa: &Evm,
) -> SecondaryMap<BlockId, BitSet<InstId>> {
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    let mut block_in: SecondaryMap<BlockId, BitSet<InstId>> = SecondaryMap::new();
    let mut block_out: SecondaryMap<BlockId, BitSet<InstId>> = SecondaryMap::new();
    for block in function.layout.iter_block() {
        let _ = &mut block_in[block];
        let _ = &mut block_out[block];
    }

    let mut changed = true;
    while changed {
        changed = false;

        for block in function.layout.iter_block() {
            let mut next_in = BitSet::default();
            for pred in cfg.preds_of(block) {
                next_in.union_with(&block_out[*pred]);
            }

            let mut next_out = next_in.clone();
            for inst in function.layout.iter_inst(block) {
                if matches!(
                    isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                    EvmInstKind::EvmMalloc(_)
                ) {
                    next_out.insert(inst);
                }
            }

            if block_in[block] != next_in {
                block_in[block] = next_in;
                changed = true;
            }
            if block_out[block] != next_out {
                block_out[block] = next_out;
                changed = true;
            }
        }
    }

    block_in
}

fn record_escaping_provenance(
    escape_kinds: &mut FxHashMap<InstId, MallocEscapeKind>,
    provenance: &Provenance,
    prov_info: &ProvenanceInfo,
    seen_mallocs: &BitSet<InstId>,
    direct_kind: MallocEscapeKind,
) {
    let reachable = prov_info.reachable_memory(provenance);
    if reachable.is_unknown_ptr() {
        for malloc in seen_mallocs.iter() {
            record_escape_kind(escape_kinds, malloc, MallocEscapeKind::UNKNOWN);
        }
    }
    for malloc in reachable.malloc_insts() {
        record_escape_kind(escape_kinds, malloc, direct_kind);
    }
}

fn record_escape_kind(
    escape_kinds: &mut FxHashMap<InstId, MallocEscapeKind>,
    malloc: InstId,
    kind: MallocEscapeKind,
) {
    escape_kinds
        .entry(malloc)
        .and_modify(|cur| *cur = cur.union(kind))
        .or_insert(kind);
}

fn compute_malloc_escape_kinds(
    function: &Function,
    scan_ctx: &EscapeScanCtx<'_>,
    block_malloc_in: &SecondaryMap<BlockId, BitSet<InstId>>,
) -> FxHashMap<InstId, MallocEscapeKind> {
    let mut escape_kinds: FxHashMap<InstId, MallocEscapeKind> = FxHashMap::default();
    let prov = &scan_ctx.prov_info.value;

    for block in function.layout.iter_block() {
        let mut seen_mallocs = block_malloc_in[block].clone();
        for inst in function.layout.iter_inst(block) {
            for_each_escape_event_at_inst(function, inst, scan_ctx, |event| {
                let direct_kind = match event.sink {
                    EscapeSink::Return => MallocEscapeKind::RETURNS_TO_CALLER,
                    EscapeSink::NonLocalStore
                    | EscapeSink::NonLocalCopy
                    | EscapeSink::CallArg { .. } => MallocEscapeKind::STORED_NON_LOCAL,
                };

                let source = match &event.source {
                    EscapeSource::Value(value) => &prov[*value],
                    EscapeSource::Memory { stored, .. }
                    | EscapeSource::CallArgument { stored, .. } => stored,
                };
                record_escaping_provenance(
                    &mut escape_kinds,
                    source,
                    scan_ctx.prov_info,
                    &seen_mallocs,
                    direct_kind,
                );
            });

            if matches!(
                scan_ctx
                    .isa
                    .inst_set()
                    .resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::EvmMalloc(_)
            ) {
                seen_mallocs.insert(inst);
            }
        }
    }

    escape_kinds
}
