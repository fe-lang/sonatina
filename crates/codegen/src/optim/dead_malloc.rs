//! Remove write-only private malloc graphs in closed EVM computations.
//!
//! Local non-escape alone is insufficient: removing an allocation can change
//! later addresses and the free pointer, and removing stores can change MSIZE.
//! We require all memory accesses to stay within constant-size fresh allocations,
//! no calls or internal returns, and no observable allocation-derived integers.
//! This deliberately leaves raw memory/allocator interactions to memory planning.

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, AccessLoc, Function, I256, Type,
    inst::{
        BinaryInstKind, CastInstKind, InstClassKind, control_flow::Return, data::Mstore, downcast,
        evm::EvmMalloc,
    },
    isa::evm::space::MEMORY,
};

use crate::analysis::memory_access::MemoryAccessAnalysis;

pub(super) fn eliminate_dead_mallocs(func: &mut Function) -> bool {
    let mut sizes = FxHashMap::default();
    for inst in func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
    {
        if let Some(malloc) = downcast::<&EvmMalloc>(func.inst_set(), func.dfg.inst(inst)) {
            let Some(size) = func.dfg.value_imm(*malloc.size()).map(|imm| imm.as_i256()) else {
                return false;
            };
            if size <= I256::zero() || size > I256::from(i64::MAX) {
                return false;
            }
            sizes.insert(inst, size.trunc_to_i64());
        }
    }
    if sizes.is_empty() {
        return false;
    }

    let insts: Vec<_> = func
        .layout
        .iter_block()
        .flat_map(|block| func.layout.iter_inst(block))
        .collect();

    let mut analysis = MemoryAccessAnalysis::new();
    let mut live = FxHashSet::default();
    let mut stores = FxHashMap::default();
    let mut pointer_stores = Vec::new();
    let mut derived = FxHashMap::default();
    for &inst in &insts {
        for &result in func.dfg.inst_results(inst) {
            if let Some((base, offset)) = analysis.exact_malloc_addr(func, result) {
                derived.insert(result, (base, offset));
            }
        }
    }

    for &inst in &insts {
        let data = func.dfg.inst(inst);
        if func.dfg.call_info(inst).is_some()
            || downcast::<&Return>(func.inst_set(), data).is_some()
        {
            // A caller can observe the allocator or memory after an internal return.
            return false;
        }
        if sizes.contains_key(&inst) {
            continue;
        }
        let effects = func.dfg.effects(inst);
        let mut address_uses = FxHashMap::default();
        for access in effects
            .accesses
            .iter()
            .filter(|access| access.space == MEMORY)
        {
            let (addr, bytes) = match access.loc {
                AccessLoc::LinearExact { addr, bytes, .. } => (addr, i64::from(bytes)),
                AccessLoc::LinearRange { addr, len } => {
                    let Some(bytes) = func.dfg.value_imm(len).map(|imm| imm.as_i256()) else {
                        return false;
                    };
                    if bytes < I256::zero() || bytes > I256::from(i64::MAX) {
                        return false;
                    }
                    (addr, bytes.trunc_to_i64())
                }
                // Includes MSIZE, free-pointer access and unknown call effects.
                _ => return false,
            };
            if bytes == 0 {
                continue;
            }
            let Some(&(base, offset)) = derived.get(&addr) else {
                return false;
            };
            if offset < 0
                || offset
                    .checked_add(bytes)
                    .is_none_or(|end| end > sizes[&base])
            {
                return false;
            }
            *address_uses.entry(addr).or_insert(0usize) += 1;
            match access.kind {
                AccessKind::Read => {
                    live.insert(base);
                }
                AccessKind::Write => {
                    // Only erase ordinary stores, never an operation with additional effects.
                    if downcast::<&Mstore>(func.inst_set(), data).is_some() {
                        stores.insert(inst, base);
                    } else {
                        live.insert(base);
                    }
                }
            }
        }
        if let Some(store) = downcast::<&Mstore>(func.inst_set(), data)
            && derived.contains_key(store.value())
        {
            let Some(&target) = stores.get(&inst) else {
                return false;
            };
            pointer_stores.push(target);
            *address_uses.entry(*store.value()).or_insert(0) += 1;
        }
        // Casts and constant offsets preserve addresses without observing them.
        let transparent = matches!(
            data.kind(),
            InstClassKind::Cast(
                CastInstKind::PtrToInt | CastInstKind::IntToPtr | CastInstKind::Bitcast
            ) | InstClassKind::Binary(BinaryInstKind::Add | BinaryInstKind::Sub)
        ) && func
            .dfg
            .inst_results(inst)
            .iter()
            .all(|value| derived.contains_key(value));
        if transparent {
            // Narrow ptr-to-int casts observe truncated numeric addresses; they
            // cannot establish a fresh, disjoint memory address.
            if matches!(data.kind(), InstClassKind::Cast(CastInstKind::PtrToInt))
                && func
                    .dfg
                    .inst_results(inst)
                    .iter()
                    .any(|&value| func.dfg.value_ty(value) != Type::I256)
            {
                return false;
            }
            continue;
        }
        for value in data.collect_values() {
            if derived.contains_key(&value) {
                let Some(uses) = address_uses.get_mut(&value) else {
                    return false;
                };
                if *uses == 0 {
                    return false;
                }
                *uses -= 1;
            }
        }
    }
    // A pointer serialized into readable memory observes its numeric address;
    // even an otherwise dead earlier malloc could change that address.
    if pointer_stores.iter().any(|target| live.contains(target)) {
        return false;
    }
    let dead: FxHashSet<_> = sizes
        .keys()
        .copied()
        .filter(|base| !live.contains(base))
        .collect();
    if dead.is_empty() {
        return false;
    }
    // Collect the closed dead set, including derived address arithmetic.
    let mut remove: FxHashSet<_> = stores
        .into_iter()
        .filter_map(|(inst, base)| dead.contains(&base).then_some(inst))
        .collect();
    remove.extend(dead.iter().copied());
    for &inst in &insts {
        if func.dfg.inst_results(inst).iter().any(|value| {
            derived
                .get(value)
                .is_some_and(|(base, _)| dead.contains(base))
        }) {
            remove.insert(inst);
        }
    }
    let remove: Vec<_> = insts
        .into_iter()
        .filter(|inst| remove.contains(inst))
        .collect();
    for &inst in &remove {
        func.layout.remove_inst(inst);
    }
    // Textual block order need not follow dominance. Untrack the entire closed
    // dead set before deleting definitions, regardless of where its users occur.
    func.erase_insts(&remove);
    true
}

#[cfg(test)]
mod tests {
    use sonatina_ir::ir_writer::FuncWriter;
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module};

    use super::eliminate_dead_mallocs;

    const GRAPH: &str = "
        v1.*i8 = evm_malloc 32.i256;
        v2.i256 = ptr_to_int v1 i256;
        mstore v2 17.i256 i256;
        v3.*i8 = evm_malloc 64.i256;
        v4.i256 = ptr_to_int v3 i256;
        mstore v4 v2 i256;
        v5.i256 = add v4 32.i256;
        mstore v5 0.i256 i256;
    ";

    fn optimize(body: &str) -> (bool, String) {
        let body = body.replace(';', ";\n").replace(": ", ":\n");
        let source = format!(
            "target = \"evm-ethereum-osaka\"\ndeclare external %callee();\nfunc public %f(v0.i256) {{\nblock0:\n{body}\n}}"
        );
        let module = parse_module(&source).expect("parse").module;
        let config = VerifierConfig::for_level(VerificationLevel::Full);
        let before = verify_module(&module, &config);
        assert!(!before.has_errors(), "{before}");
        let f = module
            .funcs()
            .into_iter()
            .find(|&f| module.ctx.func_sig(f, |sig| sig.name() == "f"))
            .unwrap();
        let changed = module.func_store.modify(f, eliminate_dead_mallocs);
        let after = verify_module(&module, &config);
        assert!(!after.has_errors(), "{after}");
        let dumped = module
            .func_store
            .view(f, |func| FuncWriter::new(f, func).dump_string());
        (changed, dumped)
    }

    #[test]
    fn removes_write_only_graph_but_keeps_return_payload() {
        let (changed, dumped) = optimize(&format!(
            "{GRAPH}
            v6.*i8 = evm_malloc 32.i256;
            mstore v6 42.i256 i256;
            evm_return v6 32.i256;"
        ));
        assert!(changed);
        assert_eq!(dumped.matches("evm_malloc").count(), 1, "{dumped}");
        assert_eq!(dumped.matches("mstore").count(), 1, "{dumped}");
        assert!(dumped.contains("42.i256"));
    }

    #[test]
    fn removes_dead_graph_in_non_topological_block_layout() {
        let (changed, dumped) = optimize(
            "v6.i1 = eq v0 0.i256;
            br v6 block2 block3;
            block1:
                v2.i256 = ptr_to_int v1 i256;
                mstore v2 42.i256 i256;
                evm_stop;
            block2:
                v1.*i8 = evm_malloc 32.i256;
                br v6 block1 block3;
            block3:
                evm_stop;",
        );
        assert!(changed);
        for operation in ["evm_malloc", "ptr_to_int", "mstore"] {
            assert!(!dumped.contains(operation), "{dumped}");
        }
    }

    #[test]
    fn unrelated_large_subtraction_does_not_observe_dead_allocations() {
        let (changed, dumped) = optimize(&format!(
            "{GRAPH}
            v6.i256 = sub v0 -9223372036854775808.i256;
            v7.*i8 = evm_malloc 32.i256;
            mstore v7 v6 i256;
            evm_return v7 32.i256;"
        ));
        assert!(changed);
        assert_eq!(dumped.matches("evm_malloc").count(), 1, "{dumped}");
        assert!(
            dumped.contains("sub v0 -9223372036854775808.i256"),
            "{dumped}"
        );
    }

    #[test]
    fn keeps_address_and_allocator_observers() {
        for observer in [
            "v6.i256 = evm_msize; evm_sstore 0.i256 v6; evm_stop;",
            "v6.i256 = mload 64.i256 i256; evm_sstore 0.i256 v6; evm_stop;",
            "v6.i256 = mload v0 i256; evm_sstore 0.i256 v6; evm_stop;",
            "mstore 64.i256 0.i256 i256; evm_stop;",
            "evm_sstore 0.i256 v2; evm_stop;",
            "evm_return v4 32.i256;",
            "call %callee; evm_stop;",
            "return;",
            "v6.i256 = mload v4 i256; v7.i256 = mload v6 i256; evm_sstore 0.i256 v7; evm_stop;",
            "v6.*i8 = evm_malloc 32.i256; v7.i256 = ptr_to_int v6 i256; mstore v6 v7 i256; evm_return v6 32.i256;",
            "v6.i256 = add v4 64.i256; mstore v6 1.i256 i256; evm_stop;",
            "v6.*i8 = evm_malloc v0; evm_return v6 32.i256;",
        ] {
            let (changed, dumped) = optimize(&format!("{GRAPH}{observer}"));
            assert!(!changed, "unexpected removal with {observer}:\n{dumped}");
            assert!(dumped.contains("mstore v4 v2"), "{dumped}");
        }
    }

    #[test]
    fn keeps_read_home_and_removes_dead_record() {
        let (changed, dumped) = optimize(&format!(
            "{GRAPH}
            v6.i256 = mload v2 i256;
            evm_sstore 0.i256 v6;
            evm_stop;"
        ));
        assert!(changed);
        assert_eq!(dumped.matches("evm_malloc").count(), 1, "{dumped}");
        assert!(dumped.contains("mload v2"), "{dumped}");
        assert!(dumped.contains("mstore v2 17"), "{dumped}");
    }

    #[test]
    fn keeps_reads_on_any_successor() {
        let (changed, dumped) = optimize(&format!(
            "{GRAPH}
            v6.i1 = eq v0 0.i256;
            br v6 block1 block2;
            block1: evm_return v4 32.i256;
            block2: evm_stop;"
        ));
        assert!(!changed, "{dumped}");
    }
}
