use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, InstId, InstSetExt, Type, ValueId,
    func_cursor::{CursorLocation, FuncCursor, InstInserter},
    inst::{
        data::{Mload, Mstore},
        evm::inst_set::EvmInstKind,
    },
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use crate::liveness::InstLiveness;

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

    let escaping = compute_escaping_mallocs(function, module, isa, ptr_escape, &prov);

    for base in escaping {
        mallocs.remove(&base);
    }

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));

            if matches!(data, EvmInstKind::EvmMalloc(_)) {
                let mut live = inst_liveness.live_out(inst).clone();
                if let Some(def) = function.dfg.inst_result(inst) {
                    live.remove(def);
                }

                remove_live_mallocs(&mut mallocs, &live, &prov);
                continue;
            }

            let Some(call) = function.dfg.call_info(inst) else {
                continue;
            };

            let callee = call.callee();
            let is_barrier = mem_effects.is_none_or(|effects| {
                let eff = effects.get(&callee).copied().unwrap_or_default();
                eff.touches_heap_meta || eff.touches_dyn_frame
            });
            if !is_barrier {
                continue;
            }

            let live = inst_liveness.live_out(inst);
            remove_live_mallocs(&mut mallocs, live, &prov);
        }
    }

    mallocs
}

fn remove_live_mallocs(
    mallocs: &mut FxHashSet<InstId>,
    live: &crate::bitset::BitSet<ValueId>,
    prov: &cranelift_entity::SecondaryMap<ValueId, Provenance>,
) {
    for v in live.iter() {
        for base in prov[v].malloc_insts() {
            mallocs.remove(&base);
        }
    }
}

fn compute_escaping_mallocs(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    prov: &cranelift_entity::SecondaryMap<ValueId, Provenance>,
) -> FxHashSet<InstId> {
    let mut escaping: FxHashSet<InstId> = FxHashSet::default();

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
            match data {
                EvmInstKind::Return(ret) => {
                    let Some(ret_val) = *ret.arg() else {
                        continue;
                    };
                    for base in prov[ret_val].malloc_insts() {
                        escaping.insert(base);
                    }
                }
                EvmInstKind::Mstore(mstore) => {
                    let addr = *mstore.addr();
                    if prov[addr].is_local_addr() {
                        continue;
                    }

                    let val = *mstore.value();
                    for base in prov[val].malloc_insts() {
                        escaping.insert(base);
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
                            for base in prov[arg].malloc_insts() {
                                escaping.insert(base);
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
    prov: &cranelift_entity::SecondaryMap<ValueId, Provenance>,
) -> bool {
    prov[value].malloc_insts().next().is_some()
        || (function.dfg.value_ty(value).is_pointer(module) && prov[value].is_empty())
}
