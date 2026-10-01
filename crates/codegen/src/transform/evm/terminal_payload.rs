use sonatina_ir::{
    Function, I256, Type,
    inst::{
        data::Mstore,
        downcast,
        evm::{EvmMalloc, EvmReturn, EvmRevert},
    },
    isa::{Isa, evm::Evm},
};

use crate::analysis::memory_access::MemoryAccessAnalysis;

/// A final word store followed immediately by returning that word needs no
/// surviving allocation. Reuse low memory after the value has been computed;
/// the existing terminal-payload and fixed-write rules protect backend spills.
pub(crate) fn reuse_terminal_word_buffers(function: &mut Function) -> bool {
    let is = Evm::new(function.ctx().triple).inst_set();
    let mut analysis = MemoryAccessAnalysis::new();
    let blocks: Vec<_> = function.layout.iter_block().collect();
    let mut changed = false;
    for block in blocks {
        let Some(terminal) = function.layout.last_inst_of(block) else {
            continue;
        };
        let data = function.dfg.inst(terminal);
        let (addr, len, revert) = if let Some(ret) = downcast::<&EvmReturn>(is, data) {
            (*ret.addr(), *ret.len(), false)
        } else if let Some(ret) = downcast::<&EvmRevert>(is, data) {
            (*ret.addr(), *ret.len(), true)
        } else {
            continue;
        };
        if function.dfg.value_imm(len).map(|imm| imm.as_i256()) != Some(I256::from(32)) {
            continue;
        }
        let Some(store) = function.layout.prev_inst_of(terminal) else {
            continue;
        };
        let Some(write) = downcast::<&Mstore>(is, function.dfg.inst(store)) else {
            continue;
        };
        if *write.ty() != Type::I256 || *write.addr() != addr {
            continue;
        }
        let value = *write.value();
        let Some((malloc, 0)) = analysis.exact_malloc_addr(function, addr) else {
            continue;
        };
        let Some(allocation) = downcast::<&EvmMalloc>(is, function.dfg.inst(malloc)) else {
            continue;
        };
        if function
            .dfg
            .value_imm(*allocation.size())
            .map(|imm| imm.as_i256())
            != Some(I256::from(32))
        {
            continue;
        }
        let zero = function.dfg.make_imm_value(I256::zero());
        function
            .dfg
            .replace_inst(store, Box::new(Mstore::new(is, zero, value, Type::I256)));
        if revert {
            function
                .dfg
                .replace_inst(terminal, Box::new(EvmRevert::new(is, zero, len)));
        } else {
            function
                .dfg
                .replace_inst(terminal, Box::new(EvmReturn::new(is, zero, len)));
        }
        changed = true;
    }
    changed
}

#[cfg(test)]
mod tests {
    use sonatina_ir::ir_writer::FuncWriter;
    use sonatina_parser::parse_module;
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module_or_panic};

    use super::reuse_terminal_word_buffers;

    #[test]
    fn terminal_word_buffers_require_an_exact_fully_written_allocation() {
        for (allocation, body, changed) in [
            ("32", "mstore v1 v0 i256; evm_return v1 32.i256;", true),
            ("32", "mstore v1 v0 i256; evm_revert v1 32.i256;", true),
            ("64", "mstore v1 v0 i256; evm_return v1 64.i256;", false),
            (
                "32",
                "v2.i8 = trunc v0 i8; mstore v1 v2 i8; evm_return v1 32.i256;",
                false,
            ),
            (
                "64",
                "mstore v1 v0 i256; v2.i256 = add v1 32.i256; evm_return v2 32.i256;",
                false,
            ),
            (
                "32",
                "mstore v1 v0 i256; v2.i256 = mload 0.i256 i256; mstore 64.i256 v2 i256; evm_return v1 32.i256;",
                false,
            ),
            ("32", "mstore v0 7.i256 i256; evm_return v0 32.i256;", false),
        ] {
            let body = body.replace("; ", ";\n");
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %entry(v0.i256) {{\nblock0:\nv9.*i8 = evm_malloc {allocation}.i256;\nv1.i256 = ptr_to_int v9 i256;\n{body}\n}}"
            );
            let module = parse_module(&source).expect("parse").module;
            let config = VerifierConfig::for_level(VerificationLevel::Full);
            verify_module_or_panic(&module, &config);
            let func = module.funcs()[0];
            module.func_store.modify(func, |function| {
                let before = FuncWriter::new(func, function).dump_string();
                assert_eq!(reuse_terminal_word_buffers(function), changed, "{source}");
                let after = FuncWriter::new(func, function).dump_string();
                if changed {
                    assert!(after.contains("mstore 0.i256 v0 i256;"), "{after}");
                } else {
                    assert_eq!(before, after);
                }
            });
            verify_module_or_panic(&module, &config);
        }
    }
}
