use std::iter;

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, AccessLoc, BlockId, ControlFlowGraph, Function, Immediate, InstId, InstSetExt,
    MemoryAccess, Module, U256, ValueId,
    inst::{
        data::{GetFunctionPtr, SymAddr, SymbolRef},
        evm::machine_inst_set::EvmMachineInstKind,
    },
    isa::{
        Isa,
        evm::{EvmMachine, space::MEMORY},
    },
    module::FuncRef,
};

use crate::{bitset::BitSet, liveness::InstLiveness, module_analysis::CallGraphSchedule};

use super::{emit::immediate_u32, memory_plan::WORD_BYTES};

// The fixed spill slots are memory `[0, 64)`, which the IR may also use. A value
// may take a slot only if neither side can change what the other reads: it is
// not live across an IR write or call that may touch the slots
// (`MachineSpillClobberLiveness`), and its spill store never runs while IR data
// in the slots is live (`values_stored_over_ir_slot_data`).

pub(crate) const FIXED_SPILL_SLOTS: u32 = 2;

pub(crate) const FIXED_SLOTS_END_BYTES: u32 = FIXED_SPILL_SLOTS * WORD_BYTES;

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

/// Bytes of the fixed slots `[0, 64)` as a mask: bit `i` is byte `i`.
type SlotBytes = u64;

const ALL_SLOT_BYTES: SlotBytes = SlotBytes::MAX;

const _: () = assert!(FIXED_SLOTS_END_BYTES == SlotBytes::BITS);

/// The bytes of `[start, start + len)` in the fixed slots. An unknown `len`
/// reaches the end of the slots.
fn slot_range_bytes(start: u32, len: Option<u32>) -> SlotBytes {
    let end = len
        .and_then(|len| start.checked_add(len))
        .map_or(FIXED_SLOTS_END_BYTES, |end| end.min(FIXED_SLOTS_END_BYTES));
    if end <= start {
        return 0;
    }
    ALL_SLOT_BYTES >> (SlotBytes::BITS - (end - start)) << start
}

/// The IR-owned fixed-slot bytes `access` may touch, and those it must write.
/// An immediate address beyond `u32` touches none, like in
/// [`machine_inst_is_fixed_slot_clobber`]; a computed address may touch any.
fn access_slot_bytes(
    function: &Function,
    access: &MemoryAccess,
    ir_bytes: SlotBytes,
) -> (SlotBytes, SlotBytes) {
    if access.space != MEMORY {
        return (0, 0);
    }
    let imm_u32 = |imm: Immediate| immediate_u32(imm).unwrap_or(u32::MAX);
    let value_u32 = |value: ValueId| function.dfg.value_imm(value).map(imm_u32);
    let (start, len) = match &access.loc {
        AccessLoc::LinearExact { addr, bytes, .. } => (value_u32(*addr), Some(*bytes)),
        AccessLoc::LinearExactImm { addr, bytes, .. } => (Some(imm_u32(*addr)), Some(*bytes)),
        AccessLoc::LinearRange { addr, len } => (value_u32(*addr), value_u32(*len)),
        AccessLoc::KeyedExact { .. } => return (0, 0),
        AccessLoc::WholeSpace | AccessLoc::Unknown => (None, None),
    };
    let Some(start) = start else {
        return (ir_bytes, 0);
    };
    let touched = slot_range_bytes(start, len) & ir_bytes;
    let written = if access.kind == AccessKind::Write && access.must_happen && len.is_some() {
        touched
    } else {
        0
    };
    (touched, written)
}

/// Interprocedural facts for [`IrSlotDataLiveness`].
pub(crate) struct IrSlotDataSummaries {
    /// The fixed-slot bytes below the static arena. The arena holds compiler
    /// memory, not IR data, and lies at or above the fixed slots in any
    /// placement that uses them: [`choose_arena_base`] reserves the slots once
    /// a function needs them, and placement repeats until it does (see
    /// `prepare_machine_section_after_pipeline`). So all of `[0, 64)` is IR
    /// data whenever a fixed-slot spill is kept, and an arena below 64 can only
    /// make a placement iteration that will be discarded spill speculatively.
    ///
    /// [`choose_arena_base`]: super::prepare::choose_arena_base
    ir_bytes: SlotBytes,
    /// The fixed-slot bytes a call may read before writing them.
    entry_reads: FxHashMap<FuncRef, SlotBytes>,
    /// The fixed-slot bytes whose IR data may be read after the function returns.
    live_at_return: FxHashMap<FuncRef, SlotBytes>,
}

impl IrSlotDataSummaries {
    /// Callers outside the section, and functions whose address is taken, may
    /// read any byte after a return.
    pub(crate) fn compute(module: &Module, schedule: &CallGraphSchedule, arena_base: u32) -> Self {
        let cfgs: FxHashMap<FuncRef, ControlFlowGraph> = schedule
            .funcs()
            .iter()
            .map(|&func| {
                let cfg = module.func_store.view(func, |function| {
                    let mut cfg = ControlFlowGraph::new();
                    cfg.compute(function);
                    cfg
                });
                (func, cfg)
            })
            .collect();
        let mut summaries = Self {
            ir_bytes: slot_range_bytes(0, Some(arena_base)),
            entry_reads: FxHashMap::default(),
            live_at_return: FxHashMap::default(),
        };

        // Least fixed point, callees first; a call within an SCC starts from no reads.
        for &scc in schedule.topo.iter().rev() {
            let members = schedule.members(scc);
            for &func in members {
                summaries.entry_reads.insert(func, 0);
            }
            let mut changed = true;
            while changed {
                changed = false;
                for &func in members {
                    let reads = module.func_store.view(func, |function| {
                        let liveness =
                            IrSlotDataLiveness::compute(function, &cfgs[&func], &summaries, 0);
                        cfgs[&func]
                            .entry()
                            .map_or(0, |entry| liveness.live_in[entry])
                    });
                    changed |= summaries.entry_reads.insert(func, reads) != Some(reads);
                }
            }
        }

        let mut called = FxHashSet::default();
        let mut escaped = FxHashSet::default();
        for &func in schedule.funcs() {
            module.func_store.view(func, |function| {
                for inst in function
                    .layout
                    .iter_block()
                    .flat_map(|b| function.layout.iter_inst(b))
                {
                    if let Some(call) = function.dfg.call_info(inst) {
                        called.insert(call.callee());
                    } else if let Some(ptr) = function.dfg.downcast::<&GetFunctionPtr>(inst) {
                        escaped.insert(*ptr.func());
                    } else if let Some(sym) = function.dfg.downcast::<&SymAddr>(inst)
                        && let SymbolRef::Func(func) = sym.sym()
                    {
                        escaped.insert(*func);
                    }
                }
            });
        }
        for &func in schedule.funcs() {
            let live = if called.contains(&func) && !escaped.contains(&func) {
                0
            } else {
                ALL_SLOT_BYTES
            };
            summaries.live_at_return.insert(func, live);
        }

        // Least fixed point, callers first: a callee's returns see what is live
        // after each call to it.
        let mut changed = true;
        while changed {
            changed = false;
            for &scc in &schedule.topo {
                for &func in schedule.members(scc) {
                    let live_at_return = summaries.live_at_return[&func];
                    let mut after_calls = Vec::new();
                    module.func_store.view(func, |function| {
                        let cfg = &cfgs[&func];
                        let liveness =
                            IrSlotDataLiveness::compute(function, cfg, &summaries, live_at_return);
                        for block in cfg.post_order() {
                            liveness.walk_block(function, block, &summaries, |inst, live_after| {
                                if let Some(call) = function.dfg.call_info(inst) {
                                    after_calls.push((call.callee(), live_after));
                                }
                            });
                        }
                    });
                    for (callee, live_after) in after_calls {
                        if let Some(live) = summaries.live_at_return.get_mut(&callee)
                            && *live | live_after != *live
                        {
                            *live |= live_after;
                            changed = true;
                        }
                    }
                }
            }
        }

        summaries
    }

    fn entry_reads(&self, callee: FuncRef) -> SlotBytes {
        self.entry_reads
            .get(&callee)
            .copied()
            .unwrap_or(ALL_SLOT_BYTES)
    }
}

/// Backward liveness of IR data in the fixed slots: the bytes of `[0, 64)` the
/// IR may still read, whether it wrote them or they are fresh memory. A read is any memory
/// read the effects model reports (including `return`/`revert`/log/call/create
/// input ranges and `msize`), a callee's [`IrSlotDataSummaries::entry_reads`],
/// or a caller's read after a return. Only a write that must happen at an
/// immediate address and length kills bytes.
struct IrSlotDataLiveness {
    live_in: SecondaryMap<BlockId, SlotBytes>,
    live_out: SecondaryMap<BlockId, SlotBytes>,
    live_at_return: SlotBytes,
}

impl IrSlotDataLiveness {
    fn compute(
        function: &Function,
        cfg: &ControlFlowGraph,
        summaries: &IrSlotDataSummaries,
        live_at_return: SlotBytes,
    ) -> Self {
        let mut liveness = Self {
            live_in: SecondaryMap::new(),
            live_out: SecondaryMap::new(),
            live_at_return,
        };
        let blocks: Vec<BlockId> = cfg.post_order().collect();
        let mut changed = true;
        while changed {
            changed = false;
            for &block in &blocks {
                let live_out = cfg
                    .succs_of(block)
                    .fold(0, |live, &succ| live | liveness.live_in[succ]);
                liveness.live_out[block] = live_out;
                let live_in = liveness.walk_block(function, block, summaries, |_, _| {});
                if liveness.live_in[block] != live_in {
                    liveness.live_in[block] = live_in;
                    changed = true;
                }
            }
        }
        liveness
    }

    /// Visits `block`'s instructions backward with the bytes live after each,
    /// returning the bytes live at the block's entry.
    fn walk_block(
        &self,
        function: &Function,
        block: BlockId,
        summaries: &IrSlotDataSummaries,
        mut visit: impl FnMut(InstId, SlotBytes),
    ) -> SlotBytes {
        let mut live = self.live_out[block];
        let insts = iter::successors(function.layout.last_inst_of(block), |&inst| {
            function.layout.prev_inst_of(inst)
        });
        for inst in insts {
            if function.dfg.is_return(inst) {
                live |= self.live_at_return;
            }
            visit(inst, live);
            if let Some(call) = function.dfg.call_info(inst) {
                live |= summaries.entry_reads(call.callee());
                continue;
            }
            let (mut read, mut written) = (0, 0);
            for access in &function.dfg.effects(inst).accesses {
                let (touched, must_write) = access_slot_bytes(function, access, summaries.ir_bytes);
                match access.kind {
                    AccessKind::Read => read |= touched,
                    AccessKind::Write => written |= must_write,
                }
            }
            live = (live & !written) | read;
        }
        live
    }
}

/// The values a fixed-slot spill store could overwrite live IR data with: a
/// spilled value is stored after its definition, on the incoming edges of its
/// phi, or at function entry for an argument, and any IR data in `[0, 64)`
/// live there may be read after the store.
pub(crate) fn values_stored_over_ir_slot_data(
    function: &Function,
    cfg: &ControlFlowGraph,
    func: FuncRef,
    summaries: &IrSlotDataSummaries,
) -> BitSet<ValueId> {
    let liveness =
        IrSlotDataLiveness::compute(function, cfg, summaries, summaries.live_at_return[&func]);
    let mut values = BitSet::default();
    if let Some(entry) = cfg.entry()
        && liveness.live_in[entry] != 0
    {
        for &arg in &function.arg_values {
            values.insert(arg);
        }
    }
    for block in cfg.post_order() {
        let phi_store_live = liveness.live_in[block] != 0
            || cfg
                .preds_of(block)
                .any(|&pred| liveness.live_out[pred] != 0);
        liveness.walk_block(function, block, summaries, |inst, live_after| {
            let store_live = if function.dfg.is_phi(inst) {
                phi_store_live
            } else {
                live_after != 0
            };
            if store_live {
                for &result in function.dfg.inst_results(inst) {
                    values.insert(result);
                }
            }
        });
    }
    values
}

#[cfg(test)]
mod tests {
    use crate::isa::evm::test_util::osaka_triple;
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

    use crate::liveness::Liveness;

    use super::*;

    fn machine_builder() -> ModuleBuilder {
        ModuleBuilder::new(ModuleCtx::new(&EvmMachine::new(osaka_triple())))
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
                .iter_all_insts()
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
