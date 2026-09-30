use sonatina_ir::{
    Function, I256, Immediate, InstId, InstSetExt, Type, ValueId,
    inst::evm::{EvmMcopy, machine_inst_set::EvmMachineInstKind},
    isa::{Isa, evm::EvmMachine},
};

use crate::isa::evm::{WORD_BYTES, immediate_u32};

/// Combine closed, disjoint runs of full-word copies after absolute memory
/// placement. No other instruction may observe the intermediate stores, and
/// every loaded value must be consumed only by its corresponding store.
pub(crate) fn coalesce_machine_copies(func: &mut Function) -> bool {
    let isa = EvmMachine::new(func.dfg.ctx.triple);
    let blocks: Vec<_> = func.layout.iter_block().collect();
    let mut changed = false;
    for block in blocks {
        let insts: Vec<_> = func.layout.iter_inst(block).collect();
        let mut start = 0;
        while start < insts.len() {
            if let Some((count, source, dest, len)) = copy_run(func, &isa, &insts[start..]) {
                let run = &insts[start..start + count];
                let last = *run.last().unwrap();
                let len = func
                    .dfg
                    .make_imm_value(Immediate::from_i256(I256::from(len), Type::I256));
                func.dfg.replace_inst(
                    last,
                    Box::new(EvmMcopy::new(isa.inst_set(), dest, source, len)),
                );
                // Stores follow their loads, so erase users before definitions.
                for &inst in run[..run.len() - 1].iter().rev() {
                    func.layout.remove_inst(inst);
                    func.erase_inst(inst);
                }
                start += count;
                changed = true;
            } else {
                start += 1;
            }
        }
    }
    changed
}

fn copy_run(
    func: &Function,
    isa: &EvmMachine,
    insts: &[InstId],
) -> Option<(usize, ValueId, ValueId, u32)> {
    let EvmMachineInstKind::EvmMload(first) = isa.inst_set().resolve_inst(func.dfg.inst(insts[0]))
    else {
        return None;
    };
    let source = *first.addr();
    let source_base = immediate_u32(func.dfg.value_imm(source)?)?;
    let mut loads = Vec::new();
    let mut stores = 0;
    let mut dest = None;
    let mut best = None;
    for (index, &inst) in insts.iter().enumerate() {
        match isa.inst_set().resolve_inst(func.dfg.inst(inst)) {
            EvmMachineInstKind::EvmMload(load) => {
                let addr = func.dfg.value_imm(*load.addr()).and_then(immediate_u32);
                let offset = u32::try_from(loads.len()).ok()?.checked_mul(WORD_BYTES)?;
                let result = func.dfg.inst_result(inst)?;
                if addr != source_base.checked_add(offset) || func.dfg.users_num(result) != 1 {
                    break;
                }
                loads.push(result);
            }
            EvmMachineInstKind::EvmMstore(store) => {
                if loads.get(stores) != Some(store.value()) {
                    break;
                }
                let Some(addr) = func.dfg.value_imm(*store.addr()).and_then(immediate_u32) else {
                    break;
                };
                let (dest_value, dest_base) = *dest.get_or_insert((*store.addr(), addr));
                let offset = u32::try_from(stores).ok()?.checked_mul(WORD_BYTES)?;
                if Some(addr) != dest_base.checked_add(offset) {
                    break;
                }
                stores += 1;
                let len = offset.checked_add(WORD_BYTES)?;
                let source_end = source_base.checked_add(len)?;
                let dest_end = dest_base.checked_add(len)?;
                if stores >= 2
                    && stores == loads.len()
                    && (source_end <= dest_base || dest_end <= source_base)
                {
                    best = Some((index + 1, source, dest_value, len));
                }
            }
            _ => break,
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::isa::evm::machine::verify::verify_machine_function;
    use sonatina_parser::parse_module;

    #[test]
    fn machine_copy_runs_require_closed_disjoint_full_words() {
        let copy = "v0.i256 = evm_mload 256.i256;\n\
                    v1.i256 = evm_mload 288.i256;\n\
                    evm_mstore 512.i256 v0;\n\
                    evm_mstore 544.i256 v1;";
        let interleaved = "v0.i256 = evm_mload 256.i256;\n\
                           evm_mstore 512.i256 v0;\n\
                           v1.i256 = evm_mload 288.i256;\n\
                           evm_mstore 544.i256 v1;";
        for (body, expected) in [
            (copy.to_owned(), true),
            (interleaved.to_owned(), true),
            // MCOPY has snapshot semantics; interleaved overlapping copies do not.
            (
                interleaved
                    .replace("512.i256", "288.i256")
                    .replace("544.i256", "320.i256"),
                false,
            ),
            (
                copy.replace("512.i256", "240.i256")
                    .replace("544.i256", "272.i256"),
                false,
            ),
            (copy.replace("544.i256", "576.i256"), false),
            (copy.replace("288.i256", "320.i256"), false),
            (
                copy.replace("evm_mstore 544.i256 v1", "evm_mstore8 544.i256 v1"),
                false,
            ),
            (
                copy.replace(
                    "evm_mstore 512",
                    "evm_mstore 768.i256 99.i256;\n evm_mstore 512",
                ),
                false,
            ),
            (format!("{copy}\nevm_mstore 768.i256 v0;"), false),
            (copy.replace("288.i256", "4294967296.i256"), false),
            (
                copy.replace("256.i256", "4294967264.i256")
                    .replace("288.i256", "4294967296.i256"),
                false,
            ),
            (
                copy.replace("512.i256", "4294967232.i256")
                    .replace("544.i256", "4294967264.i256"),
                false,
            ),
            (
                copy.replace("256.i256", "257.i256")
                    .replace("288.i256", "289.i256"),
                true,
            ),
        ] {
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %entry() {{\nblock0:\n{body}\nreturn;\n}}"
            );
            let module = parse_module(&source).unwrap().module;
            let func_ref = module.funcs()[0];
            module.func_store.modify(func_ref, |func| {
                assert_eq!(coalesce_machine_copies(func), expected, "{body}");
                verify_machine_function(func_ref, func).unwrap();
                assert!(
                    !coalesce_machine_copies(func),
                    "copy rewrite must be idempotent"
                );
                let isa = EvmMachine::new(func.dfg.ctx.triple);
                let copies = func
                    .layout
                    .iter_block()
                    .flat_map(|block| func.layout.iter_inst(block))
                    .filter(|&inst| {
                        matches!(
                            isa.inst_set().resolve_inst(func.dfg.inst(inst)),
                            EvmMachineInstKind::EvmMcopy(_)
                        )
                    })
                    .count();
                assert_eq!(copies, usize::from(expected));
            });
        }
    }
}
