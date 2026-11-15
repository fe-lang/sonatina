use std::iter;

use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    AccessKind, AccessLoc, BlockId, ControlFlowGraph, Function, Immediate, InstId, MemoryAccess,
    Module, ValueId,
    inst::{
        control_flow::Call,
        data::{GetFunctionPtr, SymAddr, SymbolRef},
        evm::EvmMsize,
    },
    isa::evm::space::MEMORY,
    module::FuncRef,
};
use tracing::debug_span;

use crate::{
    bitset::BitSet, liveness::InstLiveness, module_analysis::CallGraphSchedule,
    stackalloc::StackifyAlloc,
};

use super::{
    emit::immediate_u32,
    machine::module::FuncMachineMap,
    memory_plan::{FuncPreAnalysis, WORD_BYTES},
};

// The fixed spill slots are memory `[0, 64)`, which the IR may also use. A value
// may take a slot only if neither side can change what the other reads
// (`FixedSlotConflicts`): the value is not live across an IR write or a call
// that may write the slot, and its spill store never runs while IR data in the
// slot is live.
//
// Both rules ask which slot bytes an IR access may touch. An immediate address
// says exactly. A computed address touches none if it names an allocation on
// every path (`allocation_addresses`): allocations lie in the static arena, a
// dynamic frame or the heap, never below the arena base, and an address computed
// from an allocation's stays inside the allocation (`ptr_provenance`), as arena
// placement assumes of the same addresses. Any other computed address may touch
// every byte.

pub(crate) const FIXED_SPILL_SLOTS: u32 = 2;

pub(crate) const FIXED_SLOTS_END_BYTES: u32 = FIXED_SPILL_SLOTS * WORD_BYTES;

/// Bytes of the fixed slots `[0, 64)` as a mask: bit `i` is byte `i`.
pub(crate) type SlotBytes = u64;

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

/// The source values of each function that name an allocation on every path
/// ([`Provenance::names_allocation`]). An argument does if every call passes
/// such a value. The section entry and a function whose address is taken have
/// callers this cannot see.
///
/// [`Provenance::names_allocation`]: super::ptr_provenance::Provenance::names_allocation
pub(crate) fn allocation_addresses(
    module: &Module,
    funcs: &[FuncRef],
    entry: FuncRef,
    analyses: &FxHashMap<FuncRef, FuncPreAnalysis>,
) -> FxHashMap<FuncRef, BitSet<ValueId>> {
    let mut calls: Vec<(FuncRef, FuncRef, SmallVec<[ValueId; 8]>)> = Vec::new();
    let mut unseen_callers = FxHashSet::from_iter([entry]);
    for &func in funcs {
        module.func_store.view(func, |function| {
            for inst in function.layout.iter_all_insts() {
                if let Some(call) = function.dfg.downcast::<&Call>(inst) {
                    calls.push((func, *call.callee(), call.args().iter().copied().collect()));
                } else if let Some(taken) = func_address_taken(function, inst) {
                    unseen_callers.insert(taken);
                }
            }
        });
    }

    // Greatest fixed point: an argument names an allocation until a call passes
    // something else.
    let mut arg_allocations: FxHashMap<FuncRef, Vec<bool>> = calls
        .iter()
        .filter(|(_, callee, _)| !unseen_callers.contains(callee))
        .map(|(_, callee, args)| (*callee, vec![true; args.len()]))
        .collect();
    let names_allocation =
        |arg_allocations: &FxHashMap<FuncRef, Vec<bool>>, func: FuncRef, value: ValueId| {
            analyses[&func].prov.value[value].names_allocation(|arg| {
                arg_allocations
                    .get(&func)
                    .is_some_and(|args| args[arg as usize])
            })
        };
    let mut changed = true;
    while changed {
        changed = false;
        for (caller, callee, args) in &calls {
            for (arg, &value) in args.iter().enumerate() {
                if arg_allocations.get(callee).is_some_and(|args| args[arg])
                    && !names_allocation(&arg_allocations, *caller, value)
                {
                    arg_allocations.get_mut(callee).expect("checked above")[arg] = false;
                    changed = true;
                }
            }
        }
    }

    funcs
        .iter()
        .map(|&func| {
            let values = module.func_store.view(func, |function| {
                function
                    .dfg
                    .value_ids()
                    .filter(|&value| names_allocation(&arg_allocations, func, value))
                    .collect()
            });
            (func, values)
        })
        .collect()
}

/// The machine values of `function` that address only allocations: those
/// lowered from the source values in `source_addrs` and from no other source
/// value, and phis of them, which machine passes create when they merge
/// blocks.
pub(crate) fn machine_allocation_addresses(
    function: &Function,
    map: &FuncMachineMap,
    source_addrs: &BitSet<ValueId>,
) -> BitSet<ValueId> {
    let mut addrs = BitSet::default();
    let mut others = BitSet::default();
    for (source, &machine) in map.values.iter() {
        if let Some(machine) = machine {
            if source_addrs.contains(source) {
                addrs.insert(machine);
            } else {
                others.insert(machine);
            }
        }
    }
    addrs.difference_with(&others);
    let mut changed = true;
    while changed {
        changed = false;
        for inst in function.layout.iter_all_insts() {
            if function.dfg.is_phi(inst)
                && let &[result] = function.dfg.inst_results(inst)
                && !addrs.contains(result)
                && function
                    .dfg
                    .inst(inst)
                    .collect_values()
                    .into_iter()
                    .all(|value| addrs.contains(value))
            {
                addrs.insert(result);
                changed = true;
            }
        }
    }
    addrs
}

fn func_address_taken(function: &Function, inst: InstId) -> Option<FuncRef> {
    if let Some(ptr) = function.dfg.downcast::<&GetFunctionPtr>(inst) {
        return Some(*ptr.func());
    }
    match function.dfg.downcast::<&SymAddr>(inst)?.sym() {
        SymbolRef::Func(func) => Some(*func),
        _ => None,
    }
}

/// What an instruction may do to the IR's bytes of the fixed slots.
#[derive(Clone, Copy)]
enum SlotEffect {
    /// Memory accesses: the bytes they may read, may write, and must write.
    Access {
        read: SlotBytes,
        write: SlotBytes,
        kill: SlotBytes,
    },
    Call(FuncRef),
    Return,
}

impl SlotEffect {
    /// `MSIZE` reads how far memory extends, not what the slots hold, and every
    /// spill placement extends memory, so it is no read of slot data.
    fn of(
        function: &Function,
        inst: InstId,
        ir_bytes: SlotBytes,
        allocation_addrs: &BitSet<ValueId>,
    ) -> Option<Self> {
        if let Some(call) = function.dfg.call_info(inst) {
            return Some(Self::Call(call.callee()));
        }
        if function.dfg.is_return(inst) {
            return Some(Self::Return);
        }
        if function.dfg.downcast::<&EvmMsize>(inst).is_some() {
            return None;
        }
        let (mut read, mut write, mut kill) = (0, 0, 0);
        for access in &function.dfg.effects(inst).accesses {
            let (touched, exact) = access_slot_bytes(function, access, ir_bytes, allocation_addrs);
            match access.kind {
                AccessKind::Read => read |= touched,
                AccessKind::Write => {
                    write |= touched;
                    if access.must_happen && exact {
                        kill |= touched;
                    }
                }
            }
        }
        (read | write != 0).then_some(Self::Access { read, write, kill })
    }

    /// The bytes live after the instruction, given those live at the next one.
    fn live_after(self, live: SlotBytes, live_at_return: SlotBytes) -> SlotBytes {
        match self {
            Self::Return => live | live_at_return,
            Self::Access { .. } | Self::Call(_) => live,
        }
    }

    /// The bytes live before the instruction, given those live after it. Only
    /// a write that must happen at an immediate address and length kills bytes.
    fn live_before(
        self,
        live_after: SlotBytes,
        entry_reads: &FxHashMap<FuncRef, SlotBytes>,
    ) -> SlotBytes {
        match self {
            Self::Access { read, kill, .. } => (live_after & !kill) | read,
            Self::Call(callee) => {
                live_after | entry_reads.get(&callee).copied().unwrap_or(ALL_SLOT_BYTES)
            }
            Self::Return => live_after,
        }
    }
}

/// The IR-owned fixed-slot bytes `access` may touch, and whether it touches
/// exactly those: its address and length are immediates. An immediate beyond
/// `u32` is past the slots.
fn access_slot_bytes(
    function: &Function,
    access: &MemoryAccess,
    ir_bytes: SlotBytes,
    allocation_addrs: &BitSet<ValueId>,
) -> (SlotBytes, bool) {
    if access.space != MEMORY {
        return (0, false);
    }
    let imm_u32 = |imm: Immediate| immediate_u32(imm).unwrap_or(u32::MAX);
    let value_u32 = |value: ValueId| function.dfg.value_imm(value).map(imm_u32);
    let (addr, start, len) = match &access.loc {
        AccessLoc::LinearExact { addr, bytes, .. } => (*addr, value_u32(*addr), Some(*bytes)),
        AccessLoc::LinearExactImm { addr, bytes, .. } => {
            return (
                slot_range_bytes(imm_u32(*addr), Some(*bytes)) & ir_bytes,
                true,
            );
        }
        AccessLoc::LinearRange { addr, len } => (*addr, value_u32(*addr), value_u32(*len)),
        AccessLoc::KeyedExact { .. } => return (0, false),
        AccessLoc::WholeSpace | AccessLoc::Unknown => return (ir_bytes, false),
    };
    match start {
        _ if len == Some(0) => (0, false),
        Some(start) => (slot_range_bytes(start, len) & ir_bytes, len.is_some()),
        None if allocation_addrs.contains(addr) => (0, false),
        None => (ir_bytes, false),
    }
}

/// A function's instructions with a [`SlotEffect`], by block in layout order.
struct FuncSlotEffects {
    blocks: SecondaryMap<BlockId, Vec<(InstId, SlotEffect)>>,
    cfg: ControlFlowGraph,
    address_taken: Vec<FuncRef>,
}

impl FuncSlotEffects {
    fn compute(
        function: &Function,
        ir_bytes: SlotBytes,
        allocation_addrs: &BitSet<ValueId>,
    ) -> Self {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);
        let mut effects = Self {
            blocks: SecondaryMap::new(),
            cfg,
            address_taken: Vec::new(),
        };
        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                if let Some(effect) = SlotEffect::of(function, inst, ir_bytes, allocation_addrs) {
                    effects.blocks[block].push((inst, effect));
                } else if let Some(taken) = func_address_taken(function, inst) {
                    effects.address_taken.push(taken);
                }
            }
        }
        effects
    }
}

/// Section-wide facts for [`FixedSlotConflicts`].
pub(crate) struct FixedSlotSummaries {
    effects: FxHashMap<FuncRef, FuncSlotEffects>,
    /// The fixed-slot bytes a call may read before writing them.
    entry_reads: FxHashMap<FuncRef, SlotBytes>,
    /// The fixed-slot bytes whose IR data may be read after the function returns.
    live_at_return: FxHashMap<FuncRef, SlotBytes>,
}

impl FixedSlotSummaries {
    /// `allocation_addrs` holds each function's machine values that name an
    /// allocation on every path.
    ///
    /// Only the slot bytes below the static arena are the IR's. The arena holds
    /// compiler memory and lies at or above the fixed slots in any placement
    /// that uses them: [`choose_arena_base`] reserves the slots once a function
    /// needs them, and placement repeats until it does (see
    /// `prepare_machine_section_after_pipeline`). So all of `[0, 64)` is IR
    /// data whenever a fixed-slot spill is kept, and an arena below 64 can only
    /// make a placement iteration that will be discarded spill speculatively.
    ///
    /// Callers outside the section, and functions whose address is taken, may
    /// read any byte after a return.
    ///
    /// [`choose_arena_base`]: super::prepare::choose_arena_base
    pub(crate) fn compute(
        module: &Module,
        schedule: &CallGraphSchedule,
        arena_base: u32,
        allocation_addrs: &FxHashMap<FuncRef, BitSet<ValueId>>,
    ) -> Self {
        let _span = debug_span!("sonatina.codegen.evm.machine.fixed_slot_summaries").entered();
        let ir_bytes = slot_range_bytes(0, Some(arena_base));
        let effects: FxHashMap<FuncRef, FuncSlotEffects> =
            sonatina_ir::parallel::map(&module.func_store, schedule.funcs(), |&func| {
                let effects = module.func_store.view(func, |function| {
                    FuncSlotEffects::compute(function, ir_bytes, &allocation_addrs[&func])
                });
                (func, effects)
            })
            .into_iter()
            .collect();
        let mut summaries = Self {
            effects,
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
                    let effects = &summaries.effects[&func];
                    let liveness = IrSlotDataLiveness::compute(
                        effects,
                        &effects.cfg,
                        &summaries.entry_reads,
                        0,
                    );
                    let reads = effects
                        .cfg
                        .entry()
                        .map_or(0, |entry| liveness.live_in[entry]);
                    changed |= summaries.entry_reads.insert(func, reads) != Some(reads);
                }
            }
        }

        let mut called = FxHashSet::default();
        let mut escaped = FxHashSet::default();
        for effects in summaries.effects.values() {
            escaped.extend(effects.address_taken.iter().copied());
            called.extend(effects.blocks.values().flatten().filter_map(
                |&(_, effect)| match effect {
                    SlotEffect::Call(callee) => Some(callee),
                    SlotEffect::Access { .. } | SlotEffect::Return => None,
                },
            ));
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
                    let effects = &summaries.effects[&func];
                    let live_at_return = summaries.live_at_return[&func];
                    let liveness = IrSlotDataLiveness::compute(
                        effects,
                        &effects.cfg,
                        &summaries.entry_reads,
                        live_at_return,
                    );
                    let mut after_calls = Vec::new();
                    for block in effects.cfg.post_order() {
                        let mut live = liveness.live_out[block];
                        for &(_, effect) in effects.blocks[block].iter().rev() {
                            live = effect.live_after(live, live_at_return);
                            if let SlotEffect::Call(callee) = effect {
                                after_calls.push((callee, live));
                            }
                            live = effect.live_before(live, &summaries.entry_reads);
                        }
                    }
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

    /// The fixed-slot bytes `func` itself may write: IR writes and its
    /// fixed-slot spills.
    pub(crate) fn local_writes(&self, func: FuncRef, alloc: &StackifyAlloc) -> SlotBytes {
        let ir_writes = self.effects[&func]
            .blocks
            .values()
            .flatten()
            .map(|&(_, effect)| match effect {
                SlotEffect::Access { write, .. } => write,
                SlotEffect::Call(_) | SlotEffect::Return => 0,
            });
        alloc
            .scratch_slots()
            .map(slot_bytes)
            .chain(ir_writes)
            .fold(0, |writes, bytes| writes | bytes)
    }
}

fn slot_bytes(slot: u32) -> SlotBytes {
    slot_range_bytes(slot * WORD_BYTES, Some(WORD_BYTES))
}

/// Backward liveness of IR data in the fixed slots: the bytes of `[0, 64)` the
/// IR may still read, whether it wrote them or they are fresh memory. A read is
/// any memory read the effects model reports (including
/// `return`/`revert`/log/call/create input ranges), a callee's
/// [`FixedSlotSummaries::entry_reads`], or a caller's read after a return.
struct IrSlotDataLiveness {
    live_in: SecondaryMap<BlockId, SlotBytes>,
    live_out: SecondaryMap<BlockId, SlotBytes>,
}

impl IrSlotDataLiveness {
    /// `cfg` may have blocks split off after `effects` was computed; a split
    /// block holds only its jump.
    fn compute(
        effects: &FuncSlotEffects,
        cfg: &ControlFlowGraph,
        entry_reads: &FxHashMap<FuncRef, SlotBytes>,
        live_at_return: SlotBytes,
    ) -> Self {
        let mut liveness = Self {
            live_in: SecondaryMap::new(),
            live_out: SecondaryMap::new(),
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
                let live_in =
                    effects.blocks[block]
                        .iter()
                        .rev()
                        .fold(live_out, |live, &(_, effect)| {
                            effect.live_before(effect.live_after(live, live_at_return), entry_reads)
                        });
                if liveness.live_in[block] != live_in {
                    liveness.live_in[block] = live_in;
                    changed = true;
                }
            }
        }
        liveness
    }
}

/// The values each fixed slot cannot hold, and the values whose final spill
/// must survive a call.
pub(crate) struct FixedSlotConflicts {
    pub(crate) barred: Vec<BitSet<ValueId>>,
    pub(crate) stable_final_spill_values: BitSet<ValueId>,
}

impl FixedSlotConflicts {
    /// `slot_writes` gives the fixed-slot bytes a call to each analyzed function
    /// may write; a callee not in it, as within a call cycle, may write all.
    /// `cfg` and `inst_liveness` are those stackify plans against.
    pub(crate) fn compute(
        function: &Function,
        cfg: &ControlFlowGraph,
        func: FuncRef,
        summaries: &FixedSlotSummaries,
        slot_writes: &FxHashMap<FuncRef, SlotBytes>,
        scratch_arena_effects: &FxHashSet<FuncRef>,
        inst_liveness: &InstLiveness,
    ) -> Self {
        let effects = &summaries.effects[&func];
        let mut conflicts = Self {
            barred: vec![BitSet::default(); FIXED_SPILL_SLOTS as usize],
            stable_final_spill_values: BitSet::default(),
        };

        // A slot cannot hold a value live across a write of the slot. Fixed
        // slots occupy bytes 0..64; final scratch spills live in the shared
        // arena. A callee can overwrite the latter without touching either
        // fixed slot, including through private static mallocs.
        for &(inst, effect) in effects.blocks.values().flatten() {
            let (write, clobbers_final_spills) = match effect {
                SlotEffect::Access { write, .. } => (write, false),
                SlotEffect::Call(callee) => {
                    let write = slot_writes.get(&callee).copied().unwrap_or(ALL_SLOT_BYTES);
                    (write, write != 0 || scratch_arena_effects.contains(&callee))
                }
                SlotEffect::Return => continue,
            };
            if write == 0 && !clobbers_final_spills {
                continue;
            }
            // The instruction's own results are stored after it.
            let defs = function.dfg.inst_results(inst);
            for value in inst_liveness.live_out(inst).iter() {
                if !defs.contains(&value) {
                    conflicts.bar(write, value);
                    if clobbers_final_spills {
                        conflicts.stable_final_spill_values.insert(value);
                    }
                }
            }
        }

        // A slot cannot hold a value whose spill store may overwrite live IR
        // data: a spilled value is stored after its definition, on the incoming
        // edges of its phi, or at function entry for an argument, and IR data
        // live there may be read after the store.
        let live_at_return = summaries.live_at_return[&func];
        let liveness =
            IrSlotDataLiveness::compute(effects, cfg, &summaries.entry_reads, live_at_return);
        if let Some(entry) = cfg.entry() {
            for &arg in &function.arg_values {
                conflicts.bar(liveness.live_in[entry], arg);
            }
        }
        for block in cfg.post_order() {
            let phi_live = cfg
                .preds_of(block)
                .fold(liveness.live_in[block], |live, &pred| {
                    live | liveness.live_out[pred]
                });
            let mut live = liveness.live_out[block];
            let mut events = effects.blocks[block].iter().rev().peekable();
            if live | phi_live == 0
                && events.clone().all(|&(_, effect)| {
                    let live_after = effect.live_after(0, live_at_return);
                    effect.live_before(live_after, &summaries.entry_reads) == 0
                })
            {
                continue;
            }
            let insts = iter::successors(function.layout.last_inst_of(block), |&inst| {
                function.layout.prev_inst_of(inst)
            });
            for inst in insts {
                let effect = events
                    .next_if(|&&(event, _)| event == inst)
                    .map(|&(_, effect)| effect);
                if let Some(effect) = effect {
                    live = effect.live_after(live, live_at_return);
                }
                let store_live = if function.dfg.is_phi(inst) {
                    phi_live
                } else {
                    live
                };
                for &result in function.dfg.inst_results(inst) {
                    conflicts.bar(store_live, result);
                }
                if let Some(effect) = effect {
                    live = effect.live_before(live, &summaries.entry_reads);
                }
            }
        }

        conflicts
    }

    /// Bars `value` from every slot with a byte in `bytes`.
    fn bar(&mut self, bytes: SlotBytes, value: ValueId) {
        for (slot, barred) in self.barred.iter_mut().enumerate() {
            if bytes & slot_bytes(slot as u32) != 0 {
                barred.insert(value);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::Module;
    use sonatina_parser::{ParsedModule, parse_module};

    use crate::liveness::Liveness;

    use super::*;

    /// The fixed-slot conflicts of `%f` in a module whose `%root` calls it and
    /// halts, so that no IR data is live when `%f` returns.
    struct Analysis {
        parsed: ParsedModule,
        func: FuncRef,
        conflicts: FixedSlotConflicts,
    }

    impl Analysis {
        /// A call to a function in `slot_writers` may write both slots, and one
        /// to a function in `arena_writers` the scratch arena. The values in
        /// `allocation_addrs` name an allocation.
        fn of(
            funcs: &str,
            slot_writers: &[&str],
            arena_writers: &[&str],
            allocation_addrs: &[&str],
        ) -> Self {
            let parsed = parse_module(&format!(
                r#"
target = "evm-ethereum-osaka"
{funcs}
func public %root() {{
block0:
    v0.i256 = call %f 1.i256;
    evm_stop;
}}
"#
            ))
            .unwrap();
            let module = &parsed.module;
            let named = |name: &str| {
                module
                    .funcs()
                    .into_iter()
                    .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == name))
                    .unwrap()
            };
            let func = named("f");
            let schedule = CallGraphSchedule::compute(module, &module.funcs());
            let allocation_addrs = module
                .funcs()
                .into_iter()
                .map(|other| {
                    let values = allocation_addrs
                        .iter()
                        .filter(|_| other == func)
                        .map(|name| parsed.debug.value(func, name).unwrap())
                        .collect();
                    (other, values)
                })
                .collect();
            let summaries = FixedSlotSummaries::compute(
                module,
                &schedule,
                FIXED_SLOTS_END_BYTES,
                &allocation_addrs,
            );
            let slot_writes = module
                .funcs()
                .into_iter()
                .filter(|&other| other != func)
                .map(|other| {
                    let writes = if slot_writers.iter().any(|name| named(name) == other) {
                        ALL_SLOT_BYTES
                    } else {
                        summaries.local_writes(other, &StackifyAlloc::default())
                    };
                    (other, writes)
                })
                .collect();
            let arena_writers = arena_writers.iter().map(|name| named(name)).collect();
            let conflicts = module.func_store.view(func, |function| {
                let mut cfg = ControlFlowGraph::new();
                cfg.compute(function);
                let mut liveness = Liveness::new();
                liveness.compute(function, &cfg);
                let mut inst_liveness = InstLiveness::new();
                inst_liveness.compute(function, &cfg, &liveness);
                FixedSlotConflicts::compute(
                    function,
                    &cfg,
                    func,
                    &summaries,
                    &slot_writes,
                    &arena_writers,
                    &inst_liveness,
                )
            });
            Self {
                parsed,
                func,
                conflicts,
            }
        }

        /// Whether slot 0 and slot 1 bar the value.
        fn barred(&self, name: &str) -> [bool; 2] {
            let value = self.parsed.debug.value(self.func, name).unwrap();
            [0, 1].map(|slot| self.conflicts.barred[slot].contains(value))
        }

        fn needs_stable_final_spill(&self, name: &str) -> bool {
            let value = self.parsed.debug.value(self.func, name).unwrap();
            self.conflicts.stable_final_spill_values.contains(value)
        }
    }

    const CALLS_CALLEE: &str = r#"
func private %callee() {
block0:
    return;
}
func private %f(v0.i256) -> i256 {
block0:
    call %callee;
    return v0;
}
"#;

    #[test]
    fn call_result_liveness_is_independent_of_block_layout_order() {
        const FUNCS: &str = r#"
func private %produce() -> i256 {
block0:
    return 42.i256;
}
func private %clobber() {
block0:
    return;
}
func private %f(v0.i256) -> i256 {
block0:
    jump block2;
block1:
    call %clobber;
    return v1;
block2:
    v1.i256 = call %produce;
    jump block1;
}
"#;
        for (writers, live_across) in [(&["produce"][..], false), (&["produce", "clobber"], true)] {
            let analysis = Analysis::of(FUNCS, writers, writers, &[]);
            assert_eq!(analysis.barred("v1"), [live_across; 2]);
            assert_eq!(analysis.needs_stable_final_spill("v1"), live_across);
        }
    }

    #[test]
    fn value_live_across_a_call_follows_what_the_callee_writes() {
        let clean = Analysis::of(CALLS_CALLEE, &[], &[], &[]);
        assert_eq!(clean.barred("v0"), [false; 2]);
        assert!(!clean.needs_stable_final_spill("v0"));

        let arena = Analysis::of(CALLS_CALLEE, &[], &["callee"], &[]);
        assert_eq!(arena.barred("v0"), [false; 2]);
        assert!(arena.needs_stable_final_spill("v0"));

        let slots = Analysis::of(CALLS_CALLEE, &["callee"], &[], &[]);
        assert_eq!(slots.barred("v0"), [true; 2]);
        assert!(slots.needs_stable_final_spill("v0"));
    }

    #[test]
    fn callee_ir_write_bars_only_the_slot_it_writes() {
        let analysis = Analysis::of(
            r#"
func private %callee() {
block0:
    mstore 32.i256 7.i256 i256;
    return;
}
func private %f(v0.i256) -> i256 {
block0:
    call %callee;
    return v0;
}
"#,
            &[],
            &[],
            &[],
        );
        assert_eq!(analysis.barred("v0"), [false, true]);
    }

    #[test]
    fn local_write_bars_only_the_slots_it_touches() {
        for (addr, barred) in [(0, [true, false]), (16, [true, true]), (63, [false, true])] {
            let analysis = Analysis::of(
                &format!(
                    r#"
func private %f(v0.i256) -> i256 {{
block0:
    mstore {addr}.i256 7.i256 i256;
    return v0;
}}
"#
                ),
                &[],
                &[],
                &[],
            );
            assert_eq!(analysis.barred("v0"), barred, "write at {addr}");
            assert!(!analysis.needs_stable_final_spill("v0"));
        }
    }

    #[test]
    fn store_over_live_ir_data_bars_only_the_slot_holding_it() {
        // `v1` is stored while the word at 32 is read later; `v3` after the read.
        let analysis = Analysis::of(
            r#"
func private %f(v0.i256) -> i256 {
block0:
    mstore 32.i256 5.i256 i256;
    v1.i256 = add v0 1.i256;
    v2.i256 = mload 32.i256 i256;
    v3.i256 = add v1 v2;
    return v3;
}
"#,
            &[],
            &[],
            &[],
        );
        assert_eq!(analysis.barred("v1"), [false, true]);
        assert_eq!(analysis.barred("v3"), [false; 2]);
    }

    #[test]
    fn computed_address_touches_the_slots_unless_it_names_an_allocation() {
        const FUNCS: &str = r#"
func private %f(v0.i256) -> i256 {
block0:
    v1.i256 = evm_calldata_load 0.i256;
    v2.i256 = add v0 1.i256;
    v3.i256 = mload v1 i256;
    mstore v1 v2 i256;
    v4.i256 = add v3 v2;
    return v4;
}
"#;
        // `v2` is stored before the read and is live across the write.
        assert_eq!(Analysis::of(FUNCS, &[], &[], &[]).barred("v2"), [true; 2]);
        assert_eq!(
            Analysis::of(FUNCS, &[], &[], &["v1"]).barred("v2"),
            [false; 2]
        );
    }

    #[test]
    fn machine_phi_of_allocation_addresses_is_one() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"
func private %f(v0.i256, v1.i256, v2.i256) -> i256 {
block0:
    v3.i1 = lt v0 v1;
    br v3 block1 block2;
block1:
    jump block3;
block2:
    jump block3;
block3:
    v4.i256 = phi (v1 block1) (v2 block2);
    v5.i256 = phi (v1 block1) (v0 block2);
    v6.i256 = add v4 v5;
    return v6;
}
"#,
        )
        .unwrap();
        let func = parsed.module.funcs()[0];
        let value = |name: &str| parsed.debug.value(func, name).unwrap();
        let [v0, v1, v2, v3, v4, v5] = ["v0", "v1", "v2", "v3", "v4", "v5"].map(value);
        // The function stands for its own lowering: every value is its own image.
        let mut map = FuncMachineMap::new();
        for machine in [v0, v1, v2] {
            map.values[machine] = Some(machine);
        }
        let source_addrs = BitSet::from([v1, v2]);
        parsed.module.func_store.view(func, |function| {
            let addrs = machine_allocation_addresses(function, &map, &source_addrs);
            assert_eq!(addrs, BitSet::from([v1, v2, v4]));

            // `v2` is also the image of a source value that names no allocation.
            map.values[v3] = Some(v2);
            let addrs = machine_allocation_addresses(function, &map, &source_addrs);
            assert_eq!(addrs, BitSet::from([v1]));
            assert!(!addrs.contains(v5));
        });
    }

    #[test]
    fn msize_reads_no_slot_data() {
        let analysis = Analysis::of(
            r#"
func private %f(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 1.i256;
    v2.i256 = evm_msize;
    v3.i256 = add v1 v2;
    return v3;
}
"#,
            &[],
            &[],
            &[],
        );
        assert_eq!(analysis.barred("v1"), [false; 2]);
    }

    #[test]
    fn data_read_after_the_return_is_live_at_every_store() {
        // `%root` reads the word at 0 after the call.
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"
func private %f(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 1.i256;
    return v1;
}
func public %root() {
block0:
    v0.i256 = call %f 1.i256;
    evm_return 0.i256 32.i256;
}
"#,
        )
        .unwrap();
        let module: &Module = &parsed.module;
        let [func, _] = module.funcs()[..] else {
            panic!("two functions");
        };
        let schedule = CallGraphSchedule::compute(module, &module.funcs());
        let allocation_addrs = module
            .funcs()
            .into_iter()
            .map(|func| (func, BitSet::default()))
            .collect();
        let summaries = FixedSlotSummaries::compute(
            module,
            &schedule,
            FIXED_SLOTS_END_BYTES,
            &allocation_addrs,
        );
        assert_eq!(summaries.live_at_return[&func], slot_bytes(0));
    }
}
