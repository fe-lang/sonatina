use sonatina_ir::{
    Function, I256, Immediate, InstId, InstSetExt, Type, U256, ValueId,
    inst::evm::{EvmMcopy, machine_inst_set::EvmMachineInstKind},
    isa::{Isa, evm::EvmMachine},
};

use crate::isa::evm::WORD_BYTES;

/// Combine closed runs of full-word copies after memory placement. Grouped
/// loads have MCOPY snapshot semantics even if their ranges overlap. Interleaved
/// copies require proven-disjoint absolute ranges. Only pure address arithmetic
/// may intervene, and each loaded value must be consumed by its matching store.
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
                    let result = func.dfg.inst_result(inst);
                    if result.is_none_or(|value| func.dfg.users_num(value) == 0) {
                        func.layout.remove_inst(inst);
                        func.erase_inst(inst);
                    }
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

#[derive(Clone, Copy)]
struct Address {
    base: Option<ValueId>,
    offset: U256,
}

impl Address {
    fn at_offset(self, other: Self, bytes: u32) -> bool {
        self.base == other.base && self.offset == other.offset.overflowing_add(bytes.into()).0
    }

    fn absolute_range(self, len: u32) -> Option<(u32, u32)> {
        if self.base.is_some() || self.offset > u32::MAX.into() {
            return None;
        }
        let start = self.offset.low_u32();
        Some((start, start.checked_add(len)?))
    }
}

fn address(func: &Function, isa: &EvmMachine, mut value: ValueId) -> Address {
    let mut offset = U256::zero();
    loop {
        if let Some(imm) = func.dfg.value_imm(value) {
            return Address {
                base: None,
                offset: offset.overflowing_add(imm.as_i256().to_u256()).0,
            };
        }
        let next = func.dfg.value_inst(value).and_then(|inst| {
            match isa.inst_set().resolve_inst(func.dfg.inst(inst)) {
                EvmMachineInstKind::Add(add) => {
                    for (base, constant) in [(*add.lhs(), *add.rhs()), (*add.rhs(), *add.lhs())] {
                        if let Some(imm) = func.dfg.value_imm(constant) {
                            return Some((base, imm.as_i256().to_u256()));
                        }
                    }
                    None
                }
                EvmMachineInstKind::Sub(sub) => {
                    let imm = func.dfg.value_imm(*sub.rhs())?;
                    Some((
                        *sub.lhs(),
                        U256::zero().overflowing_sub(imm.as_i256().to_u256()).0,
                    ))
                }
                _ => None,
            }
        });
        let Some((base, constant)) = next else {
            return Address {
                base: Some(value),
                offset,
            };
        };
        value = base;
        offset = offset.overflowing_add(constant).0;
    }
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
    let source_addr = address(func, isa, source);
    let mut loads = Vec::new();
    let mut stores = 0;
    let mut dest = None;
    let mut snapshot = true;
    let mut best = None;
    for (index, &inst) in insts.iter().enumerate() {
        match isa.inst_set().resolve_inst(func.dfg.inst(inst)) {
            EvmMachineInstKind::EvmMload(load) => {
                let addr = address(func, isa, *load.addr());
                let offset = u32::try_from(loads.len()).ok()?.checked_mul(WORD_BYTES)?;
                let result = func.dfg.inst_result(inst)?;
                if !addr.at_offset(source_addr, offset) || func.dfg.users_num(result) != 1 {
                    break;
                }
                snapshot &= stores == 0;
                loads.push(result);
            }
            EvmMachineInstKind::EvmMstore(store) => {
                if loads.get(stores) != Some(store.value()) {
                    break;
                }
                let addr = address(func, isa, *store.addr());
                let (dest_value, dest_addr) = *dest.get_or_insert((*store.addr(), addr));
                let offset = u32::try_from(stores).ok()?.checked_mul(WORD_BYTES)?;
                if !addr.at_offset(dest_addr, offset) {
                    break;
                }
                stores += 1;
                let len = offset.checked_add(WORD_BYTES)?;
                let source_range = source_addr.absolute_range(len);
                let dest_range = dest_addr.absolute_range(len);
                // Preserve the fixed-range representation used by spill protection.
                let bounded_constants = (source_addr.base.is_some() || source_range.is_some())
                    && (dest_addr.base.is_some() || dest_range.is_some());
                let disjoint = matches!((source_range, dest_range),
                    (Some((src, src_end)), Some((dst, dst_end))) if src_end <= dst || dst_end <= src);
                // Offsets are modulo 2^256, as in the original ADD/SUB. If a
                // contiguous range wraps, its first scalar access already needs
                // unpayable memory expansion; MCOPY also fails on that range.
                if stores >= 2
                    && stores == loads.len()
                    && bounded_constants
                    && (snapshot || disjoint)
                {
                    best = Some((index + 1, source, dest_value, len));
                }
            }
            EvmMachineInstKind::Add(_) | EvmMachineInstKind::Sub(_) => {}
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
    use sonatina_verifier::{VerificationLevel, VerifierConfig, verify_module_or_panic};

    #[test]
    fn machine_copy_snapshots_match_affine_addresses_and_keep_live_arithmetic() {
        let copy = "v2.i256 = evm_mload v0;\n\
                    v3.i256 = add v0 32.i256;\n\
                    v4.i256 = evm_mload v3;\n\
                    v5.i256 = add v1 32.i256;\n\
                    evm_mstore v1 v2;\n\
                    evm_mstore v5 v4;";
        let interleaved = "v2.i256 = evm_mload v0;\n\
                           evm_mstore v1 v2;\n\
                           v3.i256 = add v0 32.i256;\n\
                           v4.i256 = evm_mload v3;\n\
                           v5.i256 = add v1 32.i256;\n\
                           evm_mstore v5 v4;";
        for (body, expected) in [
            (copy.to_owned(), true),
            (interleaved.to_owned(), false),
            (copy.replace("add v0 32.i256", "add 32.i256 v0"), true),
            (copy.replace("add v0 32.i256", "sub v0 -32.i256"), true),
            (
                copy.replace(
                    "v3.i256 = add v0 32.i256;",
                    "v6.i256 = sub v0 64.i256;\nv3.i256 = add v6 96.i256;",
                ),
                true,
            ),
            (copy.replace("add v0 32.i256", "add v0 64.i256"), false),
            (copy.replace("add v0 32.i256", "add v1 32.i256"), false),
            (
                copy.replace("v3.i256", "v7.i256 = evm_msize;\nv3.i256"),
                false,
            ),
            (
                copy.replace("v3.i256", "v7.i256 = evm_mload 768.i256;\nv3.i256"),
                false,
            ),
            (format!("{copy}\nevm_mstore 768.i256 v2;"), false),
            (
                copy.replace("evm_mstore v1 v2;", "evm_mstore v1 v4;")
                    .replace("evm_mstore v5 v4;", "evm_mstore v5 v2;"),
                false,
            ),
        ] {
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %entry(v0.i256, v1.i256) -> i256 {{\nblock0:\n{body}\nreturn v5;\n}}"
            );
            let module = parse_module(&source).unwrap().module;
            let func_ref = module.funcs()[0];
            module.func_store.modify(func_ref, |func| {
                assert_eq!(coalesce_machine_copies(func), expected, "{body}");
                verify_machine_function(func_ref, func).unwrap();
                assert!(!coalesce_machine_copies(func));
            });
            verify_module_or_panic(&module, &VerifierConfig::for_level(VerificationLevel::Full));
        }
    }

    #[test]
    fn machine_copy_runs_require_closed_full_words() {
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
                true,
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
