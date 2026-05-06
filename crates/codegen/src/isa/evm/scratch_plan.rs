use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    Function, Immediate, InstId, InstSetExt, U256, ValueId,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
};

use crate::{bitset::BitSet, liveness::InstLiveness};

use super::{
    memory_plan::WORD_BYTES,
    provenance::{Provenance, compute_value_provenance},
    ptr_escape::PtrEscapeSummary,
};

pub(crate) const SCRATCH_SPILL_SLOTS: u32 = 2;

const SCRATCH_END_BYTES: u32 = SCRATCH_SPILL_SLOTS * WORD_BYTES;

fn imm_lt_u32(imm: Immediate, bound: u32) -> bool {
    match imm {
        Immediate::I1(val) => (val as u32) < bound,
        Immediate::I8(val) => val >= 0 && (val as u32) < bound,
        Immediate::I16(val) => val >= 0 && (val as u32) < bound,
        Immediate::I32(val) => val >= 0 && (val as u32) < bound,
        Immediate::I64(val) => val >= 0 && (val as u64) < bound as u64,
        Immediate::I128(val) => val >= 0 && (val as u128) < bound as u128,
        Immediate::I256(val) => !val.is_negative() && val.to_u256() < U256::from(bound),
        Immediate::EnumTag { value, .. } => {
            !value.is_negative() && value.to_u256() < U256::from(bound)
        }
    }
}

fn addr_may_overlap_scratch(
    function: &Function,
    addr: ValueId,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> bool {
    if function.dfg.value_is_imm(addr) {
        let imm = function
            .dfg
            .value_imm(addr)
            .expect("imm value missing payload");
        return imm_lt_u32(imm, SCRATCH_END_BYTES);
    }

    prov[addr].is_unknown_ptr() || prov[addr].has_no_known_bases() || prov[addr].has_any_arg()
}

pub(crate) fn inst_is_scratch_clobber(
    function: &Function,
    isa: &Evm,
    inst: InstId,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> bool {
    match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
        EvmInstKind::Mstore(mstore) => addr_may_overlap_scratch(function, *mstore.addr(), prov),
        EvmInstKind::EvmMstore8(mstore8) => {
            addr_may_overlap_scratch(function, *mstore8.addr(), prov)
        }
        EvmInstKind::EvmCalldataCopy(copy) => {
            addr_may_overlap_scratch(function, *copy.dst_addr(), prov)
        }
        EvmInstKind::EvmCodeCopy(copy) => {
            addr_may_overlap_scratch(function, *copy.dst_addr(), prov)
        }
        EvmInstKind::EvmExtCodeCopy(copy) => {
            addr_may_overlap_scratch(function, *copy.dst_addr(), prov)
        }
        EvmInstKind::EvmReturnDataCopy(copy) => {
            addr_may_overlap_scratch(function, *copy.dst_addr(), prov)
        }
        EvmInstKind::EvmMcopy(copy) => addr_may_overlap_scratch(function, *copy.dest(), prov),
        EvmInstKind::EvmCall(call) => addr_may_overlap_scratch(function, *call.ret_addr(), prov),
        EvmInstKind::EvmCallCode(call) => {
            addr_may_overlap_scratch(function, *call.ret_addr(), prov)
        }
        EvmInstKind::EvmDelegateCall(call) => {
            addr_may_overlap_scratch(function, *call.ret_addr(), prov)
        }
        EvmInstKind::EvmStaticCall(call) => {
            addr_may_overlap_scratch(function, *call.ret_addr(), prov)
        }
        _ => false,
    }
}

pub(crate) fn compute_scratch_live_values(
    function: &Function,
    module: &ModuleCtx,
    isa: &Evm,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    scratch_effects: Option<&FxHashSet<FuncRef>>,
    inst_liveness: &InstLiveness,
) -> BitSet<ValueId> {
    let prov = compute_value_provenance(function, module, isa, |callee| {
        PtrEscapeSummary::get_or_conservative(ptr_escape, module, callee)
    });

    let mut scratch_live_values: BitSet<ValueId> = BitSet::default();

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let is_barrier = if let Some(call) = function.dfg.call_info(inst) {
                let callee = call.callee();
                scratch_effects.is_none_or(|effects| effects.contains(&callee))
            } else {
                inst_is_scratch_clobber(function, isa, inst, &prov)
            };

            if is_barrier {
                scratch_live_values.union_with(inst_liveness.live_out(inst));
                for def in function.dfg.inst_results(inst) {
                    scratch_live_values.remove(*def);
                }
            }
        }
    }

    scratch_live_values
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{InstSetExt, isa::Isa};
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use super::{super::ptr_escape::compute_ptr_escape_summaries, *};

    fn first_mstore_clobbers_scratch(src: &str, func_name: &str) -> bool {
        let parsed = parse_module(src).expect("module parses");
        let funcs = parsed.module.funcs();
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
            .expect("function exists");

        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let summaries = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        parsed.module.func_store.view(func_ref, |function| {
            let prov = compute_value_provenance(function, &parsed.module.ctx, &isa, |callee| {
                PtrEscapeSummary::get_or_conservative(&summaries, &parsed.module.ctx, callee)
            });
            let mstore = function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .find(|&inst| {
                    matches!(
                        isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                        EvmInstKind::Mstore(_)
                    )
                })
                .expect("mstore exists");

            inst_is_scratch_clobber(function, &isa, mstore, &prov)
        })
    }

    #[test]
    fn allocator_managed_address_with_i256_offset_is_not_scratch_clobber() {
        let clobbers = first_mstore_clobbers_scratch(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) {
block0:
    v1.*i8 = evm_malloc 96.i256;
    v2.i256 = ptr_to_int v1 i256;
    v3.i256 = add v2 v0;
    mstore v3 1.i256 i256;
    return;
}
"#,
            "f",
        );

        assert!(!clobbers);
    }

    #[test]
    fn plain_i256_address_remains_scratch_clobber() {
        let clobbers = first_mstore_clobbers_scratch(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) {
block0:
    mstore v0 1.i256 i256;
    return;
}
"#,
            "f",
        );

        assert!(clobbers);
    }
}
