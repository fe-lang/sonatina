use rustc_hash::FxHashSet;
use sonatina_ir::{
    Function, Immediate, InstId, InstSetExt, U256, ValueId,
    inst::evm::machine_inst_set::EvmMachineInstKind,
    isa::{Isa, evm::EvmMachine},
    module::FuncRef,
};

use crate::{bitset::BitSet, liveness::InstLiveness};

use super::memory_plan::WORD_BYTES;

pub(crate) const FIXED_SPILL_SLOTS: u32 = 2;

const FIXED_SLOTS_END_BYTES: u32 = FIXED_SPILL_SLOTS * WORD_BYTES;

pub(crate) struct MachineSpillClobberLiveness {
    fixed_slot_live_values: BitSet<ValueId>,
    stable_final_spill_values: BitSet<ValueId>,
}

impl MachineSpillClobberLiveness {
    pub(crate) fn compute(
        function: &Function,
        isa: &EvmMachine,
        fixed_slot_effects: &FxHashSet<FuncRef>,
        scratch_arena_effects: &FxHashSet<FuncRef>,
        inst_liveness: &InstLiveness,
    ) -> Self {
        let mut liveness = Self {
            fixed_slot_live_values: BitSet::default(),
            stable_final_spill_values: BitSet::default(),
        };

        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                if let Some(call) = function.dfg.call_info(inst) {
                    let clobbers_fixed_slots = fixed_slot_effects.contains(&call.callee());
                    if clobbers_fixed_slots {
                        liveness.record_fixed_slot_clobber(function, inst_liveness, inst);
                    }
                    // Fixed slots occupy bytes 0..64; final scratch spills live in the
                    // shared arena. A callee can overwrite the latter without touching
                    // either fixed slot, including through private static mallocs.
                    if clobbers_fixed_slots || scratch_arena_effects.contains(&call.callee()) {
                        liveness.record_stable_final_spill_clobber(function, inst_liveness, inst);
                    }
                } else if machine_inst_is_fixed_slot_clobber(function, isa, inst) {
                    liveness.record_fixed_slot_clobber(function, inst_liveness, inst);
                }
            }
        }

        liveness
    }

    pub(crate) fn into_parts(self) -> (BitSet<ValueId>, BitSet<ValueId>) {
        (self.fixed_slot_live_values, self.stable_final_spill_values)
    }

    fn record_fixed_slot_clobber(
        &mut self,
        function: &Function,
        inst_liveness: &InstLiveness,
        inst: InstId,
    ) {
        Self::record_live_out_minus_defs(
            &mut self.fixed_slot_live_values,
            function,
            inst_liveness,
            inst,
        );
    }

    fn record_stable_final_spill_clobber(
        &mut self,
        function: &Function,
        inst_liveness: &InstLiveness,
        inst: InstId,
    ) {
        Self::record_live_out_minus_defs(
            &mut self.stable_final_spill_values,
            function,
            inst_liveness,
            inst,
        );
    }

    fn record_live_out_minus_defs(
        values: &mut BitSet<ValueId>,
        function: &Function,
        inst_liveness: &InstLiveness,
        inst: InstId,
    ) {
        // Exclude this instruction's results before adding its live-across set.
        // Removing them from the accumulated set would erase liveness across
        // other clobbers when block layout visits a use before its definition.
        let defs = function.dfg.inst_results(inst);
        for value in inst_liveness.live_out(inst).iter() {
            if !defs.contains(&value) {
                values.insert(value);
            }
        }
    }
}

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

fn machine_addr_may_overlap_fixed_slots(function: &Function, addr: ValueId) -> bool {
    if function.dfg.value_is_imm(addr) {
        let imm = function
            .dfg
            .value_imm(addr)
            .expect("imm value missing payload");
        imm_lt_u32(imm, FIXED_SLOTS_END_BYTES)
    } else {
        true
    }
}

pub(crate) fn machine_inst_is_fixed_slot_clobber(
    function: &Function,
    isa: &EvmMachine,
    inst: InstId,
) -> bool {
    match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
        EvmMachineInstKind::EvmMstore(mstore) => {
            machine_addr_may_overlap_fixed_slots(function, *mstore.addr())
        }
        EvmMachineInstKind::EvmMstore8(mstore8) => {
            machine_addr_may_overlap_fixed_slots(function, *mstore8.addr())
        }
        EvmMachineInstKind::EvmCalldataCopy(copy) => {
            machine_addr_may_overlap_fixed_slots(function, *copy.dst_addr())
        }
        EvmMachineInstKind::EvmCodeCopy(copy) => {
            machine_addr_may_overlap_fixed_slots(function, *copy.dst_addr())
        }
        EvmMachineInstKind::EvmExtCodeCopy(copy) => {
            machine_addr_may_overlap_fixed_slots(function, *copy.dst_addr())
        }
        EvmMachineInstKind::EvmReturnDataCopy(copy) => {
            machine_addr_may_overlap_fixed_slots(function, *copy.dst_addr())
        }
        EvmMachineInstKind::EvmMcopy(copy) => {
            machine_addr_may_overlap_fixed_slots(function, *copy.dest())
        }
        EvmMachineInstKind::EvmCall(call) => {
            machine_addr_may_overlap_fixed_slots(function, *call.ret_addr())
        }
        EvmMachineInstKind::EvmCallCode(call) => {
            machine_addr_may_overlap_fixed_slots(function, *call.ret_addr())
        }
        EvmMachineInstKind::EvmDelegateCall(call) => {
            machine_addr_may_overlap_fixed_slots(function, *call.ret_addr())
        }
        EvmMachineInstKind::EvmStaticCall(call) => {
            machine_addr_may_overlap_fixed_slots(function, *call.ret_addr())
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashSet;
    use smallvec::smallvec;
    use sonatina_ir::{
        I256, Immediate, InstSetBase, Linkage, Module, Signature, Type,
        builder::{FunctionBuilder, ModuleBuilder},
        cfg::ControlFlowGraph,
        func_cursor::InstInserter,
        inst::{
            control_flow::{Call, Return},
            evm::EvmMstore,
        },
        isa::{Isa, evm::EvmMachine},
        module::{FuncRef, ModuleCtx},
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use crate::liveness::Liveness;

    use super::*;

    fn evm_triple() -> TargetTriple {
        TargetTriple::new(
            Architecture::Evm,
            Vendor::Ethereum,
            OperatingSystem::Evm(EvmVersion::Osaka),
        )
    }

    fn machine_builder() -> ModuleBuilder {
        ModuleBuilder::new(ModuleCtx::new(&EvmMachine::new(evm_triple())))
    }

    fn i256(builder: &mut FunctionBuilder<InstInserter>, val: i64) -> ValueId {
        builder.make_imm_value(Immediate::from_i256(I256::from(val), Type::I256))
    }

    fn define_unit_callee(builder: &ModuleBuilder, name: &str) -> FuncRef {
        let func = builder
            .declare_function(Signature::new_unit(name, Linkage::Private, &[]))
            .expect("callee declaration succeeds");
        let machine = EvmMachine::new(builder.triple());
        let is = machine.inst_set();
        let mut func_builder = builder.func_builder::<InstInserter>(func);
        let entry = func_builder.append_block();
        func_builder.switch_to_block(entry);
        func_builder.insert_inst_no_result(Return::new_unit(is));
        func_builder.seal_all();
        func_builder.finish();
        func
    }

    fn define_calling_return_arg(builder: &ModuleBuilder, name: &str, callee: FuncRef) -> FuncRef {
        let func = builder
            .declare_function(Signature::new_single(
                name,
                Linkage::Public,
                &[Type::I256],
                Type::I256,
            ))
            .expect("caller declaration succeeds");
        let machine = EvmMachine::new(builder.triple());
        let is = machine.inst_set();
        let mut func_builder = builder.func_builder::<InstInserter>(func);
        let entry = func_builder.append_block();
        func_builder.switch_to_block(entry);
        let arg = func_builder.func.arg_values[0];
        func_builder.insert_inst_no_result(Call::new(
            is.has_call().expect("machine ISA supports calls"),
            callee,
            smallvec![],
        ));
        func_builder.insert_inst_no_result(Return::new_single(is, arg));
        func_builder.seal_all();
        func_builder.finish();
        func
    }

    fn define_local_scratch_clobber_return_arg(builder: &ModuleBuilder, name: &str) -> FuncRef {
        let func = builder
            .declare_function(Signature::new_single(
                name,
                Linkage::Public,
                &[Type::I256],
                Type::I256,
            ))
            .expect("caller declaration succeeds");
        let machine = EvmMachine::new(builder.triple());
        let is = machine.inst_set();
        let mut func_builder = builder.func_builder::<InstInserter>(func);
        let entry = func_builder.append_block();
        func_builder.switch_to_block(entry);
        let arg = func_builder.func.arg_values[0];
        let addr = i256(&mut func_builder, 0);
        let val = i256(&mut func_builder, 7);
        func_builder.insert_inst_no_result(EvmMstore::new(is, addr, val));
        func_builder.insert_inst_no_result(Return::new_single(is, arg));
        func_builder.seal_all();
        func_builder.finish();
        func
    }

    fn analyze(
        module: &Module,
        func: FuncRef,
        fixed_slot_effects: &FxHashSet<FuncRef>,
        scratch_arena_effects: &FxHashSet<FuncRef>,
    ) -> (ValueId, BitSet<ValueId>, BitSet<ValueId>) {
        let machine = EvmMachine::new(module.ctx.triple);
        module.func_store.view(func, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);

            let mut liveness = Liveness::new();
            liveness.compute(function, &cfg);

            let mut inst_liveness = InstLiveness::new();
            inst_liveness.compute(function, &cfg, &liveness);

            let scratch_liveness = MachineSpillClobberLiveness::compute(
                function,
                &machine,
                fixed_slot_effects,
                scratch_arena_effects,
                &inst_liveness,
            );
            let (fixed_scratch, stable_final) = scratch_liveness.into_parts();
            (function.arg_values[0], fixed_scratch, stable_final)
        })
    }

    #[test]
    fn call_result_liveness_is_independent_of_block_layout_order() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"
func private %produce() -> i256 {
block0:
    return 42.i256;
}
func private %clobber() {
block0:
    return;
}
func public %caller(v0.i256) -> i256 {
block0:
    jump block2;
block1:
    call %clobber;
    return v1;
block2:
    v1.i256 = call %produce;
    jump block1;
}
"#,
        )
        .unwrap();
        let funcs = parsed.module.funcs();
        let [produce, clobber, caller] = funcs.as_slice() else {
            panic!("three functions");
        };
        let result = parsed.module.func_store.view(*caller, |function| {
            function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .find_map(|inst| {
                    function
                        .dfg
                        .call_info(inst)
                        .filter(|call| call.callee() == *produce)
                        .map(|_| function.dfg.inst_results(inst)[0])
                })
                .unwrap()
        });
        for later_clobber in [false, true] {
            let mut effects = FxHashSet::from_iter([*produce]);
            if later_clobber {
                effects.insert(*clobber);
            }
            let (_, fixed, stable) = analyze(&parsed.module, *caller, &effects, &effects);
            assert_eq!(fixed.contains(result), later_clobber);
            assert_eq!(stable.contains(result), later_clobber);
        }
    }

    #[test]
    fn scratch_clean_call_does_not_require_stable_final_spill() {
        let builder = machine_builder();
        let callee = define_unit_callee(&builder, "callee");
        let caller = define_calling_return_arg(&builder, "caller", callee);
        let module = builder.build();
        let fixed_slot_effects = FxHashSet::default();
        let (arg, fixed_scratch, stable_final) =
            analyze(&module, caller, &fixed_slot_effects, &FxHashSet::default());

        assert!(!fixed_scratch.contains(arg));
        assert!(!stable_final.contains(arg));
    }

    #[test]
    fn arena_clobbering_call_requires_stable_spills_but_preserves_fixed_slots() {
        let builder = machine_builder();
        let callee = define_unit_callee(&builder, "callee");
        let caller = define_calling_return_arg(&builder, "caller", callee);
        let module = builder.build();
        let scratch_arena_effects = FxHashSet::from_iter([callee]);
        let (arg, fixed_scratch, stable_final) = analyze(
            &module,
            caller,
            &FxHashSet::default(),
            &scratch_arena_effects,
        );

        assert!(!fixed_scratch.contains(arg));
        assert!(stable_final.contains(arg));
    }

    #[test]
    fn scratch_clobbering_call_requires_stable_final_spill() {
        let builder = machine_builder();
        let callee = define_unit_callee(&builder, "callee");
        let caller = define_calling_return_arg(&builder, "caller", callee);
        let module = builder.build();
        let mut fixed_slot_effects = FxHashSet::default();
        fixed_slot_effects.insert(callee);
        let (arg, fixed_scratch, stable_final) =
            analyze(&module, caller, &fixed_slot_effects, &FxHashSet::default());

        assert!(fixed_scratch.contains(arg));
        assert!(stable_final.contains(arg));
    }

    #[test]
    fn local_scratch_clobber_does_not_require_stable_final_spill() {
        let builder = machine_builder();
        let caller = define_local_scratch_clobber_return_arg(&builder, "caller");
        let module = builder.build();
        let fixed_slot_effects = FxHashSet::default();
        let (arg, fixed_scratch, stable_final) =
            analyze(&module, caller, &fixed_slot_effects, &FxHashSet::default());

        assert!(fixed_scratch.contains(arg));
        assert!(!stable_final.contains(arg));
    }
}
