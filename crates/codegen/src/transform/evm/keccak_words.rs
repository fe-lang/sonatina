use sonatina_ir::{
    Function, I256, Immediate, Type,
    inst::{
        cast::PtrToInt,
        data::Mstore,
        downcast,
        evm::{EvmKeccak256, EvmKeccak256Words, EvmMalloc},
    },
    isa::{Isa, evm::Evm},
};

use super::const_data::{add_i256, imm_i256, insert_before_no_result, insert_before_one};

/// Lowers each `evm_keccak256_words` to the memory hash the EVM executes: the
/// words are stored in order into a fresh allocation that only those stores
/// and the hash beside them use, so memory planning gives it transient
/// scratch. Hashing no words folds to the empty digest.
pub(crate) fn lower_keccak256_words(function: &mut Function) -> bool {
    let is = Evm::new(function.ctx().triple).inst_set();
    let hashes: Vec<_> = function
        .layout
        .iter_block()
        .flat_map(|block| function.layout.iter_inst(block))
        .filter(|inst| downcast::<&EvmKeccak256Words>(is, function.dfg.inst(*inst)).is_some())
        .collect();
    for inst in &hashes {
        // Read now: lowering an earlier hash renames its digest in the words
        // of any later hash that takes it.
        let words = downcast::<&EvmKeccak256Words>(is, function.dfg.inst(*inst))
            .expect("collected as a word hash")
            .words()
            .clone();
        let digest = if words.is_empty() {
            let digest = EvmKeccak256Words::digest([]);
            function
                .dfg
                .make_imm_value(Immediate::from_i256(I256::from(digest), Type::I256))
        } else {
            let len = imm_i256(
                function,
                u32::try_from(32 * words.len()).expect("too many hashed words"),
            );
            let ptr_ty = Type::I8.to_ptr(function.ctx());
            let ptr = insert_before_one(function, *inst, EvmMalloc::new(is, len), ptr_ty);
            let base = insert_before_one(
                function,
                *inst,
                PtrToInt::new(is, ptr, Type::I256),
                Type::I256,
            );
            for (offset, &word) in (0..).step_by(32).zip(&words) {
                let addr = if offset == 0 {
                    base
                } else {
                    let offset = imm_i256(function, offset);
                    add_i256(function, *inst, base, offset)
                };
                insert_before_no_result(function, *inst, Mstore::new(is, addr, word, Type::I256));
            }
            insert_before_one(
                function,
                *inst,
                EvmKeccak256::new(is, base, len),
                Type::I256,
            )
        };
        let result = function
            .dfg
            .inst_result(*inst)
            .expect("evm_keccak256_words has a result");
        function.dfg.change_to_alias(result, digest);
        function.layout.remove_inst(*inst);
        function.erase_inst(*inst);
    }
    !hashes.is_empty()
}
