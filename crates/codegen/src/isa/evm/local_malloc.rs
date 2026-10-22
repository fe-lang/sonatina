use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, Module, Type, Value, ValueId,
    cfg::ControlFlowGraph,
    inst::{cast::Bitcast, data::Alloca, evm::inst_set::EvmInstKind},
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use crate::cfg_scc::CfgSccAnalysis;

use super::{
    EvmBackend, malloc_plan::compute_malloc_escape_kinds_for_function,
    prepare::function_free_ptr_slot_facts, private_malloc::PrivateMallocUseAnalysis,
    ptr_escape::PtrEscapeSummaries, ptr_provenance::compute_provenance,
};

/// The largest malloc moved into the frame, so frames stay small.
const MAX_LOCAL_MALLOC_BYTES: u32 = 256;

/// Moves each small constant-size malloc that cannot escape its function,
/// whose address only addresses its own bytes (so no address bits are
/// observable), and that runs at most once per call (it lies in no CFG cycle)
/// into a frame slot. Return and revert payloads keep their fixed terminal
/// buffers. Memory planning places the slot in the static arena, so the
/// buffer needs neither the free pointer nor heap memory above every frame.
/// A cycle could keep an earlier visit's buffer alive through a local
/// container, which one frame slot cannot represent, so mallocs in cycles stay
/// on the heap. A moved malloc no longer advances the free pointer, so a
/// section whose code accesses the free-pointer slot keeps every malloc.
pub(crate) fn promote_local_mallocs(
    module: &Module,
    funcs: &[FuncRef],
    backend: &EvmBackend,
    ptr_escape: &PtrEscapeSummaries,
) -> bool {
    if funcs.iter().any(|&func| {
        module.func_store.view(func, |function| {
            function_free_ptr_slot_facts(function, backend).touches
        })
    }) {
        return false;
    }
    let mut promoted = false;
    for &func in funcs {
        promoted |= module.func_store.modify(func, |function| {
            promote_function_mallocs(function, &module.ctx, &backend.isa, ptr_escape)
        });
    }
    promoted
}

fn promote_function_mallocs(
    function: &mut Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &PtrEscapeSummaries,
) -> bool {
    let candidates: Vec<(InstId, BlockId, u32, ValueId)> = function
        .layout
        .iter_block()
        .flat_map(|block| {
            function
                .layout
                .iter_inst(block)
                .map(move |inst| (block, inst))
        })
        .filter_map(|(block, inst)| {
            let EvmInstKind::EvmMalloc(malloc) =
                isa.inst_set().resolve_inst(function.dfg.inst(inst))
            else {
                return None;
            };
            let size = function.dfg.value_imm(*malloc.size())?.as_i256().to_u256();
            let size = u32::try_from(size).ok()?;
            (size != 0 && size <= MAX_LOCAL_MALLOC_BYTES).then_some((
                inst,
                block,
                size,
                *malloc.size(),
            ))
        })
        .collect();
    if candidates.is_empty() {
        return false;
    }

    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);
    let mut sccs = CfgSccAnalysis::new();
    sccs.compute(&cfg);
    let prov = compute_provenance(function, module, isa, ptr_escape);
    let escape_kinds =
        compute_malloc_escape_kinds_for_function(function, module, isa, ptr_escape, &prov);

    let mut changed = false;
    for (inst, block, size, size_value) in candidates {
        if sccs
            .scc_of(block)
            .is_some_and(|scc| sccs.scc_data(scc).is_cycle)
            || escape_kinds.get(&inst).is_some_and(|kinds| kinds.escapes())
        {
            continue;
        }
        let uses = PrivateMallocUseAnalysis::new(function, module, isa, inst);
        // Terminal payloads already get fixed buffers from memory planning.
        let feeds_exit = function.layout.iter_all_insts().any(|user| {
            uses.inst_uses_derived_value(user)
                && matches!(
                    isa.inst_set().resolve_inst(function.dfg.inst(user)),
                    EvmInstKind::EvmReturn(_) | EvmInstKind::EvmRevert(_)
                )
        });
        if feeds_exit
            || uses
                .analyze_bounded_private_address_uses(size_value, false)
                .is_none()
        {
            continue;
        }
        let result = function
            .dfg
            .inst_result(inst)
            .expect("evm_malloc has a result");
        let ptr_ty = function.dfg.value_ty(result);
        let words_ty = function
            .ctx()
            .with_ty_store_mut(|s| s.make_array(Type::I256, size.div_ceil(32) as usize));
        let slot_ty = words_ty.to_ptr(function.ctx());
        let slot = insert_before(
            function,
            inst,
            Alloca::new(isa.inst_set(), words_ty),
            slot_ty,
        );
        let ptr = insert_before(
            function,
            inst,
            Bitcast::new(isa.inst_set(), slot, ptr_ty),
            ptr_ty,
        );
        function.dfg.change_to_alias(result, ptr);
        function.layout.remove_inst(inst);
        function.erase_inst(inst);
        changed = true;
    }
    changed
}

fn insert_before<I: sonatina_ir::Inst>(
    function: &mut Function,
    before: InstId,
    data: I,
    ty: Type,
) -> ValueId {
    let inst = function.dfg.make_inst(data);
    function.propagate_inst_attribution(inst, before);
    function.layout.insert_inst_before(inst, before);
    let value = function.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty,
    });
    function.dfg.append_result(inst, value);
    value
}

#[cfg(test)]
mod tests {
    use sonatina_parser::parse_module;

    use super::{super::test_util::osaka_backend, *};
    use crate::isa::evm::compute_ptr_escape_summaries;

    /// The mallocs left in `%run` after promotion. `%run` writes a 32-byte
    /// buffer and reads it back, so only its control flow and the section's
    /// other functions decide whether the buffer moves into the frame.
    fn mallocs_left_after_promotion(run: &str, others: &str) -> usize {
        let module = parse_module(&format!(
            r#"
target = "evm-ethereum-osaka"
{others}
func public %run() {{
{run}
}}
"#
        ))
        .expect("module parses")
        .module;
        let backend = osaka_backend();
        let funcs = module.funcs();
        let summaries = compute_ptr_escape_summaries(&module, &funcs, &backend.isa);
        promote_local_mallocs(&module, &funcs, &backend, &summaries);
        let run = funcs
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == "run"))
            .expect("run exists");
        module.func_store.view(run, |function| {
            function
                .layout
                .iter_all_insts()
                .filter(|&inst| {
                    matches!(
                        backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                        EvmInstKind::EvmMalloc(_)
                    )
                })
                .count()
        })
    }

    const BUFFER: &str = "v1.*i8 = evm_malloc 32.i256;
    v2.i256 = ptr_to_int v1 i256;
    mstore v2 7.i256 i256;
    v3.i256 = mload v2 i256;
    evm_sstore 0.i256 v3;";

    #[test]
    fn promotes_a_buffer_that_runs_once() {
        let run = format!("block0:\n    {BUFFER}\n    evm_stop;");
        assert_eq!(mallocs_left_after_promotion(&run, ""), 0);
    }

    #[test]
    fn promotes_a_buffer_live_across_an_allocating_call() {
        let run = "block0:\n    v1.*i8 = evm_malloc 32.i256;\n    v2.i256 = ptr_to_int v1 i256;\n    mstore v2 7.i256 i256;\n    v3.i256 = call %allocate;\n    v4.i256 = mload v2 i256;\n    evm_sstore 0.i256 v4;\n    evm_sstore 1.i256 v3;\n    evm_stop;";
        let allocate = "func private %allocate() -> i256 {\nblock0:\n    v0.*i8 = evm_malloc 32.i256;\n    v1.i256 = ptr_to_int v0 i256;\n    return v1;\n}";
        assert_eq!(mallocs_left_after_promotion(run, allocate), 0);
    }

    #[test]
    fn only_escaping_unknown_local_pointers_keep_buffers() {
        let allocate = "func private %allocate() -> i256 {\nblock0:\n    v0.*i8 = evm_malloc 32.i256;\n    v1.i256 = ptr_to_int v0 i256;\n    return v1;\n}";
        // A callee's heap object is not the buffer, so storing its address
        // anywhere leaves the buffer private. An address made from an integer
        // could name the buffer.
        for (escaping, left) in [
            ("v5.i256 = call %allocate;", 0),
            (
                "v4.i256 = evm_calldata_load 0.i256;\n    v6.*i8 = int_to_ptr v4 *i8;\n    v5.i256 = ptr_to_int v6 i256;",
                1,
            ),
        ] {
            let run = format!(
                "block0:\n    {BUFFER}\n    {escaping}\n    mstore 512.i256 v5 i256;\n    evm_stop;"
            );
            assert_eq!(
                mallocs_left_after_promotion(&run, allocate),
                left,
                "{escaping}"
            );
        }
    }

    #[test]
    fn keeps_buffers_in_cycles() {
        let natural = format!(
            "block0:\n    jump block1;\nblock1:\n    {BUFFER}\n    v4.i256 = evm_sload 1.i256;\n    v5.i1 = ne v4 0.i256;\n    br v5 block1 block2;\nblock2:\n    evm_stop;"
        );
        // Both blocks of the cycle are entered from `block0`, so no block
        // dominates the other and the cycle is not a natural loop.
        let irreducible = format!(
            "block0:\n    v0.i256 = evm_calldata_load 0.i256;\n    v6.i1 = ne v0 0.i256;\n    br v6 block1 block2;\nblock1:\n    {BUFFER}\n    v4.i256 = evm_sload 1.i256;\n    v5.i1 = ne v4 0.i256;\n    br v5 block2 block3;\nblock2:\n    v7.i256 = evm_sload 2.i256;\n    v8.i1 = ne v7 0.i256;\n    br v8 block1 block3;\nblock3:\n    evm_stop;"
        );
        assert_eq!(mallocs_left_after_promotion(&natural, ""), 1);
        assert_eq!(mallocs_left_after_promotion(&irreducible, ""), 1);
    }

    #[test]
    fn keeps_buffers_when_the_section_accesses_the_free_pointer() {
        let run = format!("block0:\n    {BUFFER}\n    evm_stop;");
        for others in [
            "func private %peek() -> i256 {\nblock0:\n    v0.i256 = mload 64.i256 i256;\n    return v0;\n}",
            "func private %size() -> i256 {\nblock0:\n    v0.i256 = evm_msize;\n    return v0;\n}",
        ] {
            assert_eq!(mallocs_left_after_promotion(&run, others), 1, "{others}");
        }
    }
}
