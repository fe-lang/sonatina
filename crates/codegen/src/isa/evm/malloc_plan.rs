use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, Type, ValueId,
    cfg::ControlFlowGraph,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        data::{Mload, Mstore},
        evm::inst_set::EvmInstKind,
    },
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use crate::{bitset::BitSet, liveness::InstLiveness};

use super::{
    mem_effects::FuncMemEffects,
    provenance::{Provenance, compute_value_provenance},
    ptr_escape::PtrEscapeSummary,
};

pub(crate) fn should_restore_free_ptr_on_internal_returns(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    transient_mallocs: &FxHashSet<InstId>,
) -> bool {
    let mut has_internal_return = false;
    let mut has_persistent_malloc = false;

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
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

    let prov = compute_value_provenance(function, module, isa, |callee| {
        ptr_escape
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| conservative_unknown_ptr_summary(module, callee))
            .arg_may_be_returned
    });

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            match data {
                EvmInstKind::Return(ret) => {
                    let Some(ret_val) = *ret.arg() else {
                        continue;
                    };
                    if value_may_be_heap_derived(function, module, ret_val, &prov) {
                        return false;
                    }
                }
                EvmInstKind::Mstore(mstore) => {
                    let addr = *mstore.addr();
                    if prov[addr].is_local_addr() {
                        continue;
                    }

                    let val = *mstore.value();
                    if value_may_be_heap_derived(function, module, val, &prov) {
                        return false;
                    }
                }
                EvmInstKind::Call(call) => {
                    let callee = *call.callee();
                    let callee_sum = ptr_escape
                        .get(&callee)
                        .cloned()
                        .unwrap_or_else(|| conservative_unknown_ptr_summary(module, callee));
                    for (idx, &arg) in call.args().iter().enumerate() {
                        if idx < callee_sum.arg_may_escape.len()
                            && callee_sum.arg_may_escape[idx]
                            && value_may_be_heap_derived(function, module, arg, &prov)
                        {
                            return false;
                        }
                    }
                }
                _ => {}
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
    mem_effects: Option<&FxHashMap<FuncRef, FuncMemEffects>>,
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

    let prov = compute_value_provenance(function, module, isa, |callee| {
        ptr_escape
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| conservative_unknown_ptr_summary(module, callee))
            .arg_may_be_returned
    });

    let block_malloc_in = compute_block_malloc_in(function, isa);
    let escaping =
        compute_escaping_mallocs(function, module, isa, ptr_escape, &prov, &block_malloc_in);

    for base in escaping {
        mallocs.remove(&base);
    }

    for block in function.layout.iter_block() {
        let mut seen_mallocs = block_malloc_in[block].clone();
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));

            if matches!(data, EvmInstKind::EvmMalloc(_)) {
                let mut live = inst_liveness.live_out(inst).clone();
                if let Some(def) = function.dfg.inst_result(inst) {
                    live.remove(def);
                }

                remove_live_mallocs(&mut mallocs, &live, &prov, &seen_mallocs);
                seen_mallocs.insert(inst);
                continue;
            }

            let Some(call) = function.dfg.call_info(inst) else {
                continue;
            };

            let callee = call.callee();
            let is_barrier = mem_effects.is_none_or(|effects| {
                let eff = effects.get(&callee).copied().unwrap_or_else(|| {
                    panic!(
                        "missing mem effects for callee {} in transient malloc analysis",
                        callee.as_u32()
                    )
                });
                eff.touches_heap_meta || eff.touches_dyn_frame
            });
            if !is_barrier {
                continue;
            }

            let live = inst_liveness.live_out(inst);
            remove_live_mallocs(&mut mallocs, live, &prov, &seen_mallocs);
        }
    }

    mallocs
}

fn remove_live_mallocs(
    mallocs: &mut FxHashSet<InstId>,
    live: &BitSet<ValueId>,
    prov: &SecondaryMap<ValueId, Provenance>,
    seen_mallocs: &BitSet<InstId>,
) {
    let mut has_unknown_ptr = false;
    for v in live.iter() {
        let v_prov = &prov[v];
        if v_prov.is_unknown_ptr() {
            has_unknown_ptr = true;
        }
        for base in v_prov.malloc_insts() {
            mallocs.remove(&base);
        }
    }

    if has_unknown_ptr {
        mallocs.retain(|m| !seen_mallocs.contains(*m));
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

fn record_escaping_mallocs(
    escaping: &mut FxHashSet<InstId>,
    value: ValueId,
    prov: &SecondaryMap<ValueId, Provenance>,
    seen_mallocs: &BitSet<InstId>,
) {
    let p = &prov[value];
    if p.is_unknown_ptr() {
        escaping.extend(seen_mallocs.iter());
    }
    escaping.extend(p.malloc_insts());
}

fn compute_escaping_mallocs(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    prov: &SecondaryMap<ValueId, Provenance>,
    block_malloc_in: &SecondaryMap<BlockId, BitSet<InstId>>,
) -> FxHashSet<InstId> {
    let mut escaping: FxHashSet<InstId> = FxHashSet::default();

    for block in function.layout.iter_block() {
        let mut seen_mallocs = block_malloc_in[block].clone();
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            match data {
                EvmInstKind::Return(ret) => {
                    let Some(ret_val) = *ret.arg() else {
                        continue;
                    };
                    record_escaping_mallocs(&mut escaping, ret_val, prov, &seen_mallocs);
                }
                EvmInstKind::Mstore(mstore) => {
                    let addr = *mstore.addr();
                    if prov[addr].is_local_addr() {
                        continue;
                    }

                    let val = *mstore.value();
                    record_escaping_mallocs(&mut escaping, val, prov, &seen_mallocs);
                }
                EvmInstKind::Call(call) => {
                    let callee = *call.callee();
                    let callee_sum = ptr_escape
                        .get(&callee)
                        .cloned()
                        .unwrap_or_else(|| conservative_unknown_ptr_summary(module, callee));
                    for (idx, &arg) in call.args().iter().enumerate() {
                        if idx < callee_sum.arg_may_escape.len() && callee_sum.arg_may_escape[idx] {
                            record_escaping_mallocs(&mut escaping, arg, prov, &seen_mallocs);
                        }
                    }
                }
                _ => {}
            }

            if matches!(data, EvmInstKind::EvmMalloc(_)) {
                seen_mallocs.insert(inst);
            }
        }
    }

    escaping
}

fn conservative_unknown_ptr_summary(module: &ModuleCtx, func_ref: FuncRef) -> PtrEscapeSummary {
    let arg_count = module.func_sig(func_ref, |sig| sig.args().len());
    PtrEscapeSummary {
        arg_may_escape: vec![true; arg_count],
        arg_may_be_returned: vec![true; arg_count],
        returns_any_ptr: module.func_sig(func_ref, |sig| sig.ret_ty().is_pointer(module)),
    }
}

fn value_may_be_heap_derived(
    function: &Function,
    module: &ModuleCtx,
    value: ValueId,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> bool {
    prov[value].malloc_insts().next().is_some()
        || prov[value].is_unknown_ptr()
        || (function.dfg.value_ty(value).is_pointer(module) && prov[value].is_empty())
}
