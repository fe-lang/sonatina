use cranelift_entity::SecondaryMap;
use rayon::prelude::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::{debug, debug_span, info_span, trace_span};

use crate::{
    analysis::func_behavior,
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    liveness::{InstLiveness, Liveness},
    machinst::lower::{SectionMembership, SectionWorkModule},
    module_analysis::{CallGraphSchedule, SccRef},
    stackalloc::StackifyAlloc,
};
use sonatina_ir::{
    AccessKind, AccessLoc, Function, GlobalVariableRef, InstId, InstSetExt, MemoryAccess, Module,
    ValueId,
    cfg::ControlFlowGraph,
    inst::evm::{inst_set::EvmInstKind, machine_inst_set::EvmMachineInstKind},
    isa::{
        Isa,
        evm::{EvmMachine, space::MEMORY},
    },
    module::{FuncRef, ModuleCtx},
    object::EmbedSymbol,
};

use super::{
    EvmBackend, LateCleanupProfile,
    dyn_sp::{FuncDynSpPlan, compute_machine_dyn_sp_plan},
    emit::{
        FinalAlloc, LateBlockAliasPlan, compute_function_entry_jump_targets,
        compute_late_block_alias_plan, immediate_u32, rewrite_evm_local_fallthrough_layout,
    },
    fixed_slots,
    machine::{
        final_spills::{
            FinalSpillAllocationInput, FinalSpillChoiceCtx, FinalSpillObjects,
            FixedMemoryWriteRange, MachineFinalSpillInput, OptionalFinalSpillPlacement,
            allocate_final_spills,
        },
        lazy_frame::{FrameSummary, compute_frame_summary, compute_machine_frame_roots},
        lower::lower_section_to_machine,
        module::FuncMachineMap,
        pipeline::run_machine_opt_pipeline,
        placement::{MemoryPlacementSection, compute_semantic_memory_placement},
        prepare::prepare_machine_stackify_analyses,
    },
    malloc_plan,
    memory_plan::{
        self, BackendSpillReserve, DYN_SP_SLOT, FREE_PTR_SLOT, FuncMemPlan, ProgramMemoryPlan,
        STATIC_BASE, WORD_BYTES, compute_abs_clobber_words_with_extra,
    },
    pipeline::EvmPipeline,
    ptr_escape::PtrEscapeSummary,
    ptr_provenance::{Provenance, compute_value_provenance},
};

const FREE_PTR_SLOT_START: u32 = FREE_PTR_SLOT as u32;
const FREE_PTR_SLOT_END: u32 = FREE_PTR_SLOT_START + WORD_BYTES;
const DYN_SP_SLOT_START: u32 = DYN_SP_SLOT as u32;
const MAX_FINAL_SPILL_RESERVE_ITERS: usize = 64;

pub struct EvmPreparedSection {
    work: SectionWorkModule,
    funcs: Vec<FuncRef>,
    globals: Vec<GlobalVariableRef>,
    used_embed_symbols: FxHashSet<EmbedSymbol>,
    section_plan: EvmSectionPlan,
    function_plans: FxHashMap<FuncRef, EvmFunctionPlan>,
}

impl EvmPreparedSection {
    pub fn module(&self) -> &Module {
        self.work.module()
    }

    pub fn funcs(&self) -> &[FuncRef] {
        &self.funcs
    }

    pub fn globals(&self) -> &[GlobalVariableRef] {
        &self.globals
    }

    pub fn used_embed_symbols(&self) -> &FxHashSet<EmbedSymbol> {
        &self.used_embed_symbols
    }

    pub(crate) fn function_plan(&self, func: FuncRef) -> Option<&EvmFunctionPlan> {
        self.function_plans.get(&func)
    }

    pub fn stackify_trace(&self, func: FuncRef) -> Option<&str> {
        self.function_plans
            .get(&func)
            .and_then(|plan| plan.stackify_trace.as_deref())
    }

    pub(crate) fn section_plan(&self) -> &EvmSectionPlan {
        &self.section_plan
    }
}

#[derive(Clone)]
pub(crate) struct EvmSectionPlan {
    pub(crate) arena_base: u32,
    pub(crate) dyn_base: u32,
    pub(crate) scratch_peak_words: u32,
    pub(crate) stable_chain_peak_words: u32,
}

#[derive(Clone)]
pub(crate) struct EvmFunctionPlan {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) emitted_block_order: Vec<sonatina_ir::BlockId>,
    pub(crate) block_aliases: FxHashMap<sonatina_ir::BlockId, sonatina_ir::BlockId>,
    pub(crate) mem_plan: FuncMemPlan,
    pub(crate) frame_summary: FrameSummary,
    pub(crate) dyn_sp_plan: FuncDynSpPlan,
    pub(crate) function_entry_jumpdest: bool,
    pub(crate) stackify_trace: Option<String>,
}

#[derive(Clone, Copy)]
enum MemoryAccessLen {
    Known(u32),
    Value(ValueId),
}

impl MemoryAccessLen {
    fn is_zero(self, function: &Function) -> bool {
        match self {
            MemoryAccessLen::Known(len) => len == 0,
            MemoryAccessLen::Value(len) => value_imm_u32(function, len) == Some(0),
        }
    }

    fn as_u32(self, function: &Function) -> Option<u32> {
        match self {
            MemoryAccessLen::Known(len) => Some(len),
            MemoryAccessLen::Value(len) => value_imm_u32(function, len),
        }
    }
}

pub(crate) fn value_imm_u32(function: &Function, value: ValueId) -> Option<u32> {
    function.dfg.value_imm(value).and_then(immediate_u32)
}

fn byte_ranges_overlap(lhs_start: u32, lhs_len: u32, rhs_start: u32, rhs_end: u32) -> bool {
    if lhs_len == 0 {
        return false;
    }

    lhs_start
        .checked_add(lhs_len)
        .is_none_or(|lhs_end| lhs_start < rhs_end && rhs_start < lhs_end)
}

fn addr_is_allocator_managed(prov: &Provenance) -> bool {
    !prov.is_empty() && !prov.is_unknown_ptr() && !prov.has_any_arg()
}

fn memory_access_may_touch_range(
    function: &Function,
    addr: ValueId,
    len: MemoryAccessLen,
    range_start: u32,
    range_end: u32,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> bool {
    if len.is_zero(function) {
        return false;
    }

    if function.dfg.value_is_imm(addr) {
        let Some(addr) = value_imm_u32(function, addr) else {
            return false;
        };
        return len.as_u32(function).map_or(addr < range_end, |len| {
            byte_ranges_overlap(addr, len, range_start, range_end)
        });
    }

    let prov = &prov[addr];
    !addr_is_allocator_managed(prov)
}

fn memory_access_may_touch_range_from_effect(
    function: &Function,
    access: &sonatina_ir::MemoryAccess,
    range_start: u32,
    range_end: u32,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> bool {
    if access.space != MEMORY {
        return false;
    }

    match &access.loc {
        AccessLoc::LinearExact { addr, bytes, .. } => memory_access_may_touch_range(
            function,
            *addr,
            MemoryAccessLen::Known(*bytes),
            range_start,
            range_end,
            prov,
        ),
        AccessLoc::LinearExactImm { addr, bytes, .. } => immediate_u32(*addr)
            .is_some_and(|addr| byte_ranges_overlap(addr, *bytes, range_start, range_end)),
        AccessLoc::LinearRange { addr, len } => memory_access_may_touch_range(
            function,
            *addr,
            MemoryAccessLen::Value(*len),
            range_start,
            range_end,
            prov,
        ),
        AccessLoc::WholeSpace | AccessLoc::Unknown => true,
        AccessLoc::KeyedExact { .. } => false,
    }
}

pub(crate) fn memory_access_may_touch_free_ptr_slot(
    function: &Function,
    access: &sonatina_ir::MemoryAccess,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> bool {
    memory_access_may_touch_range_from_effect(
        function,
        access,
        FREE_PTR_SLOT_START,
        FREE_PTR_SLOT_END,
        prov,
    )
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct FreePtrSlotFacts {
    pub(crate) touches: bool,
    pub(crate) writes: bool,
}

pub(crate) fn function_free_ptr_slot_facts(
    function: &Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) -> FreePtrSlotFacts {
    let prov = compute_value_provenance(function, module, &backend.isa, |callee| {
        ptr_escape
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| PtrEscapeSummary::conservative_unknown_ctx(module, callee))
    });

    let mut facts = FreePtrSlotFacts::default();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            // Section callees are scanned directly; call summaries only expose whole-space writes.
            if matches!(
                backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::Call(_) | EvmInstKind::EvmMalloc(_)
            ) {
                continue;
            }

            for access in &function.dfg.effects(inst).accesses {
                if memory_access_may_touch_free_ptr_slot(function, access, &prov) {
                    facts.touches = true;
                    facts.writes |= access.kind == AccessKind::Write;
                    if facts.writes {
                        return facts;
                    }
                }
            }
        }
    }
    facts
}

#[derive(Clone, Copy)]
pub(crate) enum MemoryLayoutReservation {
    None,
    Reserve { start: u32, len: u32 },
    ConservativeFloor,
}

#[derive(Default)]
struct SectionMemoryLayout {
    max_reserved_end: u32,
    conservative_floor: bool,
}

impl SectionMemoryLayout {
    fn reserve_len(&mut self, start: u32, len: u32) {
        if len != 0 {
            match start.checked_add(len) {
                Some(end) => self.max_reserved_end = self.max_reserved_end.max(end),
                None => self.conservative_floor = true,
            }
        }
    }

    fn apply(&mut self, reservation: MemoryLayoutReservation) {
        match reservation {
            MemoryLayoutReservation::None => {}
            MemoryLayoutReservation::Reserve { start, len } => self.reserve_len(start, len),
            MemoryLayoutReservation::ConservativeFloor => self.conservative_floor = true,
        }
    }

    fn arena_base(&self) -> u32 {
        let base = align_to_word(self.max_reserved_end).unwrap_or(STATIC_BASE);
        if self.conservative_floor {
            base.max(STATIC_BASE)
        } else {
            base
        }
    }
}

fn align_to_word(bytes: u32) -> Option<u32> {
    let rem = bytes % WORD_BYTES;
    if rem == 0 {
        Some(bytes)
    } else {
        bytes.checked_add(WORD_BYTES - rem)
    }
}

fn memory_layout_reservation_for_addr_len(
    function: &Function,
    addr: ValueId,
    len: MemoryAccessLen,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> MemoryLayoutReservation {
    if len.is_zero(function) {
        return MemoryLayoutReservation::None;
    }

    if function.dfg.value_is_imm(addr) {
        return match (value_imm_u32(function, addr), len.as_u32(function)) {
            (Some(start), Some(len)) => MemoryLayoutReservation::Reserve { start, len },
            _ => MemoryLayoutReservation::ConservativeFloor,
        };
    }

    if addr_is_allocator_managed(&prov[addr]) {
        MemoryLayoutReservation::None
    } else {
        MemoryLayoutReservation::ConservativeFloor
    }
}

fn memory_layout_reservation_from_effect(
    function: &Function,
    access: &MemoryAccess,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> MemoryLayoutReservation {
    if access.space != MEMORY {
        return MemoryLayoutReservation::None;
    }

    match &access.loc {
        AccessLoc::LinearExact { addr, bytes, .. } => memory_layout_reservation_for_addr_len(
            function,
            *addr,
            MemoryAccessLen::Known(*bytes),
            prov,
        ),
        AccessLoc::LinearExactImm { addr, bytes, .. } => immediate_u32(*addr)
            .map_or(MemoryLayoutReservation::ConservativeFloor, |start| {
                MemoryLayoutReservation::Reserve { start, len: *bytes }
            }),
        AccessLoc::LinearRange { addr, len } => memory_layout_reservation_for_addr_len(
            function,
            *addr,
            MemoryAccessLen::Value(*len),
            prov,
        ),
        AccessLoc::WholeSpace | AccessLoc::Unknown => MemoryLayoutReservation::ConservativeFloor,
        AccessLoc::KeyedExact { .. } => MemoryLayoutReservation::None,
    }
}

fn immediate_memory_access_range(function: &Function, access: &MemoryAccess) -> Option<(u32, u32)> {
    let (start, len) = match &access.loc {
        AccessLoc::LinearExact { addr, bytes, .. } => (value_imm_u32(function, *addr)?, *bytes),
        AccessLoc::LinearExactImm { addr, bytes, .. } => (immediate_u32(*addr)?, *bytes),
        AccessLoc::LinearRange { addr, len } => (
            value_imm_u32(function, *addr)?,
            value_imm_u32(function, *len)?,
        ),
        AccessLoc::WholeSpace | AccessLoc::Unknown | AccessLoc::KeyedExact { .. } => return None,
    };

    let end = start.checked_add(len)?;
    Some((start, end))
}

fn terminal_payload_range(
    function: &Function,
    backend: &EvmBackend,
    inst: InstId,
) -> Option<(u32, u32)> {
    match backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
        EvmInstKind::EvmReturn(ret) => {
            let start = value_imm_u32(function, *ret.addr())?;
            let len = value_imm_u32(function, *ret.len())?;
            Some((start, start.checked_add(len)?))
        }
        EvmInstKind::EvmRevert(revert) => {
            let start = value_imm_u32(function, *revert.addr())?;
            let len = value_imm_u32(function, *revert.len())?;
            Some((start, start.checked_add(len)?))
        }
        _ => None,
    }
}

fn access_is_terminal_payload_write(
    function: &Function,
    access: &MemoryAccess,
    payload_start: u32,
    payload_end: u32,
) -> Option<(u32, u32)> {
    if access.space != MEMORY || access.kind != AccessKind::Write {
        return None;
    }

    let (start, end) = immediate_memory_access_range(function, access)?;
    (payload_start <= start && end <= payload_end).then_some((start, end))
}

fn ranges_cover(range_start: u32, range_end: u32, ranges: &mut [(u32, u32)]) -> bool {
    if range_start == range_end {
        return true;
    }

    ranges.sort_unstable();
    let mut covered_until = range_start;
    for &(start, end) in ranges.iter() {
        if end <= covered_until {
            continue;
        }
        if covered_until < start {
            return false;
        }
        covered_until = end;
        if range_end <= covered_until {
            return true;
        }
    }
    false
}

fn terminal_payload_scratch_insts(function: &Function, backend: &EvmBackend) -> FxHashSet<InstId> {
    let mut out = FxHashSet::default();
    for block in function.layout.iter_block() {
        let insts: Vec<_> = function.layout.iter_inst(block).collect();
        let Some(&terminal) = insts.last() else {
            continue;
        };
        let Some((payload_start, payload_end)) =
            terminal_payload_range(function, backend, terminal)
        else {
            continue;
        };

        let mut suffix_insts = Vec::new();
        let mut write_ranges = Vec::new();
        for &inst in insts.iter().rev() {
            let effects = function.dfg.effects(inst);
            if inst == terminal {
                suffix_insts.push(inst);
                continue;
            }
            if effects.accesses.is_empty() && effects.other.is_empty() {
                continue;
            }

            let mut inst_write_ranges = Vec::new();
            for access in &effects.accesses {
                let Some(range) =
                    access_is_terminal_payload_write(function, access, payload_start, payload_end)
                else {
                    break;
                };
                inst_write_ranges.push(range);
            }
            if inst_write_ranges.len() != effects.accesses.len() || !effects.other.is_empty() {
                break;
            }

            suffix_insts.push(inst);
            write_ranges.extend(inst_write_ranges);
        }

        if ranges_cover(payload_start, payload_end, &mut write_ranges) {
            out.extend(suffix_insts);
        }
    }
    out
}

fn reserve_function_memory_layout(
    layout: &mut SectionMemoryLayout,
    function: &Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) {
    let prov = compute_value_provenance(function, module, &backend.isa, |callee| {
        ptr_escape
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| PtrEscapeSummary::conservative_unknown_ctx(module, callee))
    });
    let terminal_payload_scratch = terminal_payload_scratch_insts(function, backend);

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if terminal_payload_scratch.contains(&inst) {
                continue;
            }
            if matches!(
                backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::Call(_) | EvmInstKind::EvmMalloc(_) | EvmInstKind::EvmMsize(_)
            ) {
                continue;
            }

            for access in &function.dfg.effects(inst).accesses {
                layout.apply(memory_layout_reservation_from_effect(
                    function, access, &prov,
                ));
            }
        }
    }
}

fn machine_fixed_memory_write_ranges(
    function: &Function,
    isa: &EvmMachine,
) -> Vec<FixedMemoryWriteRange> {
    let mut ranges = Vec::new();
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            if let Some(range) = machine_fixed_memory_write_range(function, isa, inst) {
                ranges.push(range);
            }
        }
    }
    ranges.sort_unstable_by_key(|range| (range.start_byte, range.end_byte, range.inst.as_u32()));
    ranges
}

fn machine_fixed_memory_write_range(
    function: &Function,
    isa: &EvmMachine,
    inst: InstId,
) -> Option<FixedMemoryWriteRange> {
    match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
        EvmMachineInstKind::EvmMstore(mstore) => {
            fixed_write_range(function, inst, *mstore.addr(), WORD_BYTES)
        }
        EvmMachineInstKind::EvmMstore8(mstore8) => {
            fixed_write_range(function, inst, *mstore8.addr(), 1)
        }
        EvmMachineInstKind::EvmCalldataCopy(copy) => {
            fixed_write_range_from_len_value(function, inst, *copy.dst_addr(), *copy.len())
        }
        EvmMachineInstKind::EvmCodeCopy(copy) => {
            fixed_write_range_from_len_value(function, inst, *copy.dst_addr(), *copy.len())
        }
        EvmMachineInstKind::EvmExtCodeCopy(copy) => {
            fixed_write_range_from_len_value(function, inst, *copy.dst_addr(), *copy.len())
        }
        EvmMachineInstKind::EvmReturnDataCopy(copy) => {
            fixed_write_range_from_len_value(function, inst, *copy.dst_addr(), *copy.len())
        }
        EvmMachineInstKind::EvmMcopy(copy) => {
            fixed_write_range_from_len_value(function, inst, *copy.dest(), *copy.len())
        }
        EvmMachineInstKind::EvmCall(call) => {
            fixed_write_range_from_len_value(function, inst, *call.ret_addr(), *call.ret_len())
        }
        EvmMachineInstKind::EvmCallCode(call) => {
            fixed_write_range_from_len_value(function, inst, *call.ret_addr(), *call.ret_len())
        }
        EvmMachineInstKind::EvmDelegateCall(call) => {
            fixed_write_range_from_len_value(function, inst, *call.ret_addr(), *call.ret_len())
        }
        EvmMachineInstKind::EvmStaticCall(call) => {
            fixed_write_range_from_len_value(function, inst, *call.ret_addr(), *call.ret_len())
        }
        _ => None,
    }
}

fn fixed_write_range_from_len_value(
    function: &Function,
    inst: InstId,
    addr: ValueId,
    len: ValueId,
) -> Option<FixedMemoryWriteRange> {
    fixed_write_range(function, inst, addr, value_imm_u32(function, len)?)
}

fn fixed_write_range(
    function: &Function,
    inst: InstId,
    addr: ValueId,
    len: u32,
) -> Option<FixedMemoryWriteRange> {
    if len == 0 {
        return None;
    }
    let start_byte = value_imm_u32(function, addr)?;
    let end_byte = start_byte.checked_add(len)?;
    Some(FixedMemoryWriteRange {
        inst,
        start_byte,
        end_byte,
    })
}

pub(crate) struct ArenaBaseFacts {
    pub(crate) has_dynamic_frames: bool,
    pub(crate) has_stackify_fixed_slot_spills: bool,
    pub(crate) backend_spill_scratch_reserve_words: u32,
    pub(crate) has_persistent_mallocs: bool,
}

pub(crate) fn choose_arena_base(
    module: &Module,
    funcs: &[FuncRef],
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    facts: ArenaBaseFacts,
) -> u32 {
    let mut layout = SectionMemoryLayout::default();

    let spill_reserve_words = if facts.has_stackify_fixed_slot_spills {
        facts
            .backend_spill_scratch_reserve_words
            .max(fixed_slots::FIXED_SPILL_SLOTS)
    } else {
        facts.backend_spill_scratch_reserve_words
    };
    layout.reserve_len(0, spill_reserve_words * WORD_BYTES);
    if facts.has_stackify_fixed_slot_spills {
        layout.reserve_len(0, fixed_slots::FIXED_SPILL_SLOTS * WORD_BYTES);
    }
    if facts.has_persistent_mallocs {
        layout.reserve_len(FREE_PTR_SLOT_START, WORD_BYTES);
    }
    if facts.has_dynamic_frames {
        layout.reserve_len(FREE_PTR_SLOT_START, WORD_BYTES);
        layout.reserve_len(DYN_SP_SLOT_START, WORD_BYTES);
    }

    for &func in funcs {
        module.func_store.view(func, |function| {
            reserve_function_memory_layout(&mut layout, function, &module.ctx, backend, ptr_escape);
        });
    }

    layout.arena_base()
}

pub(crate) fn prepare_section(
    backend: &EvmBackend,
    work: SectionWorkModule,
) -> Result<EvmPreparedSection, String> {
    let module = work.module();
    let pipeline = EvmPipeline::new(backend);
    let _span = info_span!(
        "sonatina.codegen.evm.prepare_section",
        funcs = module.funcs().len()
    )
    .entered();
    let pipeline = pipeline.run(&work)?;
    let funcs = pipeline.funcs;
    let ptr_escape = pipeline.ptr_escape;
    let membership = work.membership();

    {
        let _span = debug_span!("sonatina.codegen.evm.func_behavior").entered();
        func_behavior::analyze_module(module);
    }

    prepare_machine_section_after_pipeline(backend, work, funcs, ptr_escape, membership)
}

fn prepare_machine_section_after_pipeline(
    backend: &EvmBackend,
    work: SectionWorkModule,
    funcs: Vec<FuncRef>,
    ptr_escape: FxHashMap<FuncRef, PtrEscapeSummary>,
    membership: SectionMembership,
) -> Result<EvmPreparedSection, String> {
    let source_module = work.module();
    let pre_analyses = compute_high_evm_pre_analyses(source_module, &funcs, backend);
    let schedule = CallGraphSchedule::compute(source_module, &funcs);
    let mut fixed_slot_effects = FxHashSet::default();
    let mut backend_spill_reserves: FxHashMap<FuncRef, BackendSpillReserve> = FxHashMap::default();
    let mut last_convergence_error = None;

    for iteration in 0..MAX_FINAL_SPILL_RESERVE_ITERS {
        let placement = compute_semantic_memory_placement(
            source_module,
            MemoryPlacementSection {
                schedule: &schedule,
                funcs: &funcs,
                entry: work.entry(),
                includes: work.includes(),
            },
            &pre_analyses,
            &ptr_escape,
            &fixed_slot_effects,
            backend,
            &backend_spill_reserves,
        );

        let machine = lower_section_to_machine(&work, &funcs, &placement, backend)?;
        run_machine_opt_pipeline(
            machine.work.module(),
            &funcs,
            backend.late_cleanup_profile == LateCleanupProfile::Size,
        )?;

        let machine_isa = EvmMachine::new(machine.work.module().ctx.triple);
        let machine_schedule = CallGraphSchedule::compute(machine.work.module(), &funcs);
        let machine_analyses = prepare_machine_stackify_analyses(
            machine.work.module(),
            &machine_schedule,
            backend,
            &machine_isa,
        )?;
        // Recompute fixed-slot effects from the current machine allocation. Final spills selected
        // for fixed slots are added below, after optional spill placement has been chosen.
        let mut actual_fixed_slot_effects: FxHashSet<FuncRef> = machine_analyses
            .iter()
            .filter_map(|(&func, analysis)| analysis.alloc.uses_scratch_spills().then_some(func))
            .collect();
        let function_entry_jump_targets =
            compute_function_entry_jump_targets(machine.work.module(), &funcs);

        let mut machine_final_spill_inputs: Vec<_> = machine_analyses
            .into_iter()
            .map(|(func, analysis)| {
                let func_placement = placement
                    .funcs
                    .get(&func)
                    .unwrap_or_else(|| panic!("missing placement for func {}", func.as_u32()));
                let mut mem_plan = func_placement.mem_plan.clone();
                let func_map = machine
                    .source_to_machine
                    .funcs
                    .get(&func)
                    .unwrap_or_else(|| panic!("missing source map for func {}", func.as_u32()));
                remap_machine_mem_plan_call_preserve(&mut mem_plan, func_map);
                let fixed_writes =
                    machine
                        .work
                        .module()
                        .func_store
                        .view(func, |machine_function| {
                            machine_fixed_memory_write_ranges(machine_function, &machine_isa)
                        });
                let reserve = backend_spill_reserves
                    .get(&func)
                    .copied()
                    .unwrap_or_default();
                let spills = FinalSpillObjects::compute(
                    &analysis.alloc,
                    &analysis.stable_final_spill_values,
                );
                MachineFinalSpillInput {
                    func,
                    analysis,
                    mem_plan,
                    final_scratch_reserve: func_placement.final_scratch_reserve,
                    reserve,
                    fixed_writes,
                    spills,
                }
            })
            .collect();
        machine_final_spill_inputs.sort_unstable_by_key(|input| input.func.as_u32());

        let optional_final_spill_placements = FinalSpillChoiceCtx {
            source_module,
            schedule: &schedule,
            funcs: &funcs,
            section_entry: work.entry(),
            section_includes: work.includes(),
            pre_analyses: &pre_analyses,
            ptr_escape: &ptr_escape,
            backend,
            base_fixed_slot_effects: &actual_fixed_slot_effects,
            inputs: &machine_final_spill_inputs,
        }
        .choose_optional_placements();

        let section_plan = EvmSectionPlan {
            arena_base: placement.arena_base,
            dyn_base: placement.global_dyn_base,
            scratch_peak_words: placement.scratch_peak_words,
            stable_chain_peak_words: placement.stable_chain_peak_words,
        };

        let mut actual_spill_reserves: FxHashMap<FuncRef, BackendSpillReserve> =
            FxHashMap::default();
        let mut function_plans = FxHashMap::default();
        let results: Vec<_> = machine_final_spill_inputs
            .into_par_iter()
            .map(|input| {
                let MachineFinalSpillInput {
                    func,
                    analysis,
                    mem_plan,
                    final_scratch_reserve,
                    reserve,
                    fixed_writes,
                    spills,
                    ..
                } = input;
                let func_placement = placement
                    .funcs
                    .get(&func)
                    .unwrap_or_else(|| panic!("missing placement for func {}", func.as_u32()));
                let func_map = machine
                    .source_to_machine
                    .funcs
                    .get(&func)
                    .unwrap_or_else(|| panic!("missing source map for func {}", func.as_u32()));
                let alloc = analysis.alloc;
                let block_order = analysis.block_order;
                let mut stackify_trace = analysis.trace;
                let optional_placement = optional_final_spill_placements
                    .get(&func)
                    .copied()
                    .unwrap_or(OptionalFinalSpillPlacement::Scratch);
                let final_spills = allocate_final_spills(FinalSpillAllocationInput {
                    func,
                    alloc,
                    mem_plan,
                    final_scratch_reserve,
                    reserve,
                    fixed_writes,
                    spills,
                    optional_placement,
                })?;
                if let Some(trace) = &mut stackify_trace {
                    trace.remap_stack_objects(&final_spills.stack_obj_remap);
                }
                let frame_roots = machine
                    .work
                    .module()
                    .func_store
                    .view(func, |machine_function| {
                        source_module.func_store.view(func, |source_function| {
                            compute_machine_frame_roots(
                                source_function,
                                machine_function,
                                func_map,
                                &func_placement.alloca_loc,
                                &backend.isa,
                            )
                        })
                    });
                let frame_summary = machine.work.module().func_store.view(func, |function| {
                    let final_alloc =
                        FinalAlloc::new(final_spills.alloc.clone(), final_spills.mem_plan.clone());
                    compute_frame_summary(
                        function,
                        &final_alloc,
                        &final_spills.mem_plan,
                        &frame_roots,
                    )
                });
                let alias_plan = machine.work.module().func_store.view(func, |function| {
                    compute_late_block_alias_plan(
                        function,
                        &final_spills.alloc,
                        &frame_summary,
                        &block_order,
                    )
                });
                let LateBlockAliasPlan {
                    aliases: block_aliases,
                    emitted_block_order,
                } = alias_plan;
                let emitted_block_order = if backend.late_cleanup_profile != LateCleanupProfile::Off
                {
                    machine.work.module().func_store.view(func, |function| {
                        rewrite_evm_local_fallthrough_layout(
                            function,
                            &block_aliases,
                            emitted_block_order,
                            backend.late_cleanup_profile == LateCleanupProfile::Speed,
                        )
                    })
                } else {
                    emitted_block_order
                };
                let stackify_trace = stackify_trace.map(|trace| {
                    machine
                        .work
                        .module()
                        .func_store
                        .view(func, |function| trace.render(function, &final_spills.alloc))
                });
                Ok::<_, String>((
                    func,
                    final_spills.required_reserve,
                    final_spills.used_fallback,
                    EvmFunctionPlan {
                        alloc: final_spills.alloc,
                        emitted_block_order,
                        block_aliases,
                        mem_plan: final_spills.mem_plan,
                        frame_summary,
                        dyn_sp_plan: FuncDynSpPlan::default(),
                        function_entry_jumpdest: function_entry_jump_targets.contains(&func),
                        stackify_trace,
                    },
                ))
            })
            .collect();
        let mut results = results.into_iter().collect::<Result<Vec<_>, _>>()?;
        results.sort_unstable_by_key(|(func, ..)| func.as_u32());
        let mut final_spill_fallback_funcs = Vec::new();
        for (func, required_reserve, used_fallback, plan) in results {
            if required_reserve.scratch_words != 0 {
                actual_fixed_slot_effects.insert(func);
            }
            actual_spill_reserves.insert(func, required_reserve);
            if used_fallback {
                final_spill_fallback_funcs.push(func);
            }
            function_plans.insert(func, plan);
        }

        let mem_plans: FxHashMap<FuncRef, FuncMemPlan> = function_plans
            .iter()
            .map(|(&func, plan)| (func, plan.mem_plan.clone()))
            .collect();
        let frame_summaries: FxHashMap<FuncRef, FrameSummary> = function_plans
            .iter()
            .map(|(&func, plan)| (func, plan.frame_summary.clone()))
            .collect();
        let dyn_sp_plans = compute_machine_dyn_sp_plan(
            machine.work.module(),
            &machine_schedule,
            machine.work.entry(),
            &mem_plans,
            &frame_summaries,
        );
        for (func, dyn_sp_plan) in dyn_sp_plans {
            function_plans
                .get_mut(&func)
                .unwrap_or_else(|| panic!("missing function plan for {}", func.as_u32()))
                .dyn_sp_plan = dyn_sp_plan;
        }

        let reserve_peak = backend_spill_reserves
            .values()
            .map(|reserve| reserve.max_words())
            .max()
            .unwrap_or(0);
        let actual_peak = actual_spill_reserves
            .values()
            .map(|reserve| reserve.max_words())
            .max()
            .unwrap_or(0);
        debug!(
            iteration,
            reserve_peak, actual_peak, "evm machine spill reserve iteration"
        );

        let fixed_slot_effects_satisfied = actual_fixed_slot_effects
            .iter()
            .all(|func| fixed_slot_effects.contains(func));
        let spill_reserve_satisfied = actual_spill_reserves.iter().all(|(func, actual)| {
            backend_spill_reserves
                .get(func)
                .copied()
                .unwrap_or_default()
                .satisfies(*actual)
        });
        let fallback_satisfied = final_spill_fallback_funcs.is_empty();
        last_convergence_error = Some(final_spill_convergence_error(
            iteration,
            &backend_spill_reserves,
            &actual_spill_reserves,
            &fixed_slot_effects,
            &actual_fixed_slot_effects,
            &final_spill_fallback_funcs,
            &section_plan,
        ));

        if spill_reserve_satisfied && fixed_slot_effects_satisfied && fallback_satisfied {
            validate_committed_final_spill_section(&section_plan, &function_plans)?;
            let mut globals: Vec<_> = membership.globals.iter().copied().collect();
            globals.sort_unstable();
            return Ok(EvmPreparedSection {
                work: machine.work,
                funcs,
                globals,
                used_embed_symbols: membership.used_embed_symbols,
                section_plan,
                function_plans,
            });
        }
        if spill_reserve_satisfied && fixed_slot_effects_satisfied && !fallback_satisfied {
            return Err(final_spill_fallback_with_satisfied_reserves_error(
                &final_spill_fallback_funcs,
                &section_plan,
            ));
        }

        backend_spill_reserves =
            pointwise_max_reserve_maps(&backend_spill_reserves, &actual_spill_reserves);
        fixed_slot_effects.extend(actual_fixed_slot_effects);
        debug!(
            iteration,
            actual_peak, "rerunning evm machine prepare with larger spill/scratch reserve"
        );
    }

    Err(last_convergence_error.unwrap_or_else(|| {
        format!(
            "EVM final-spill memory placement did not converge after {MAX_FINAL_SPILL_RESERVE_ITERS} iterations"
        )
    }))
}

fn pointwise_max_reserve_maps(
    old: &FxHashMap<FuncRef, BackendSpillReserve>,
    new: &FxHashMap<FuncRef, BackendSpillReserve>,
) -> FxHashMap<FuncRef, BackendSpillReserve> {
    let mut out = old.clone();
    for (&func, &reserve) in new {
        out.entry(func)
            .and_modify(|cur| *cur = cur.pointwise_max(reserve))
            .or_insert(reserve);
    }
    out
}

fn final_spill_convergence_error(
    iteration: usize,
    backend_spill_reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
    actual_spill_reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
    fixed_slot_effects: &FxHashSet<FuncRef>,
    actual_fixed_slot_effects: &FxHashSet<FuncRef>,
    final_spill_fallback_funcs: &[FuncRef],
    section_plan: &EvmSectionPlan,
) -> String {
    let mut reserve_deltas: Vec<_> = actual_spill_reserves
        .iter()
        .filter_map(|(&func, &actual)| {
            let current = backend_spill_reserves
                .get(&func)
                .copied()
                .unwrap_or_default();
            (!current.satisfies(actual)).then_some(format!(
                "func{} previous={:?} actual={:?}",
                func.as_u32(),
                current,
                actual
            ))
        })
        .collect();
    reserve_deltas.sort();

    let mut scratch_delta: Vec<_> = actual_fixed_slot_effects
        .iter()
        .filter(|func| !fixed_slot_effects.contains(func))
        .map(|func| format!("func{}", func.as_u32()))
        .collect();
    scratch_delta.sort();

    let mut fallback_funcs: Vec<_> = final_spill_fallback_funcs
        .iter()
        .map(|func| format!("func{}", func.as_u32()))
        .collect();
    fallback_funcs.sort();

    format!(
        "EVM final-spill memory placement did not converge after {MAX_FINAL_SPILL_RESERVE_ITERS} iterations; last_iteration={iteration}; arena_base=0x{:x}; scratch_peak_words={}; stable_chain_peak_words={}; reserve_delta=[{}]; scratch_effect_delta=[{}]; fallback_funcs=[{}]",
        section_plan.arena_base,
        section_plan.scratch_peak_words,
        section_plan.stable_chain_peak_words,
        reserve_deltas.join(", "),
        scratch_delta.join(", "),
        fallback_funcs.join(", ")
    )
}

fn final_spill_fallback_with_satisfied_reserves_error(
    final_spill_fallback_funcs: &[FuncRef],
    section_plan: &EvmSectionPlan,
) -> String {
    let mut funcs: Vec<_> = final_spill_fallback_funcs
        .iter()
        .map(|func| format!("func{}", func.as_u32()))
        .collect();
    funcs.sort();
    format!(
        "EVM final-spill placement used fallback despite satisfied reserves; this indicates incomplete reserve accounting: funcs=[{}]; arena_base=0x{:x}; scratch_peak_words={}; stable_chain_peak_words={}",
        funcs.join(", "),
        section_plan.arena_base,
        section_plan.scratch_peak_words,
        section_plan.stable_chain_peak_words,
    )
}

fn validate_committed_final_spill_section(
    section_plan: &EvmSectionPlan,
    function_plans: &FxHashMap<FuncRef, EvmFunctionPlan>,
) -> Result<(), String> {
    for (&func, plan) in function_plans {
        if plan.mem_plan.arena_base != section_plan.arena_base {
            return Err(format!(
                "EVM committed final-spill plan has inconsistent arena base: func{} plan=0x{:x} section=0x{:x}",
                func.as_u32(),
                plan.mem_plan.arena_base,
                section_plan.arena_base
            ));
        }
        if plan.mem_plan.scratch_words > section_plan.scratch_peak_words {
            return Err(format!(
                "EVM committed final-spill plan exceeds section scratch peak: func{} scratch_words={} scratch_peak_words={} arena_base=0x{:x}",
                func.as_u32(),
                plan.mem_plan.scratch_words,
                section_plan.scratch_peak_words,
                section_plan.arena_base
            ));
        }
        if let memory_plan::StableMode::StableAbs { base_word } = plan.mem_plan.stable_mode
            && plan.mem_plan.stable_words != 0
            && base_word < plan.mem_plan.scratch_words
        {
            return Err(format!(
                "EVM static stable frame starts inside scratch in committed final-spill plan: func{} stable_base_word={} scratch_words={} arena_base=0x{:x}; scratch_peak_words={}; stable_chain_peak_words={}",
                func.as_u32(),
                base_word,
                plan.mem_plan.scratch_words,
                section_plan.arena_base,
                section_plan.scratch_peak_words,
                section_plan.stable_chain_peak_words,
            ));
        }
        if let memory_plan::StableMode::StableAbs { base_word } = plan.mem_plan.stable_mode {
            let stable_end = base_word
                .checked_add(plan.mem_plan.stable_words)
                .ok_or_else(|| {
                    format!(
                        "EVM committed final-spill plan stable end overflow: func{} base_word={} stable_words={}",
                        func.as_u32(),
                        base_word,
                        plan.mem_plan.stable_words
                    )
                })?;
            let static_end = section_plan
                .scratch_peak_words
                .checked_add(section_plan.stable_chain_peak_words)
                .ok_or_else(|| {
                    format!(
                        "EVM committed final-spill section static end overflow: arena_base=0x{:x}; scratch_peak_words={}; stable_chain_peak_words={}",
                        section_plan.arena_base,
                        section_plan.scratch_peak_words,
                        section_plan.stable_chain_peak_words
                    )
                })?;
            if stable_end > static_end {
                return Err(format!(
                    "EVM committed final-spill plan exceeds section static memory: func{} stable_end={} static_end={} arena_base=0x{:x}; scratch_peak_words={}; stable_chain_peak_words={}",
                    func.as_u32(),
                    stable_end,
                    static_end,
                    section_plan.arena_base,
                    section_plan.scratch_peak_words,
                    section_plan.stable_chain_peak_words,
                ));
            }
        }
    }

    Ok(())
}

fn remap_machine_mem_plan_call_preserve(mem_plan: &mut FuncMemPlan, map: &FuncMachineMap) {
    let mut call_preserve = FxHashMap::default();
    for (source_inst, plan) in std::mem::take(&mut mem_plan.call_preserve) {
        if let Some(machine_inst) = map.insts[source_inst] {
            call_preserve.insert(machine_inst, plan);
        }
    }
    mem_plan.call_preserve = call_preserve;
}

pub(crate) fn compute_return_escape_caller_clamp_words(
    schedule: &CallGraphSchedule,
    plan: &ProgramMemoryPlan,
    extra_clobber_words: &FxHashMap<FuncRef, BackendSpillReserve>,
) -> FxHashMap<FuncRef, u32> {
    let abs_clobber_words =
        compute_abs_clobber_words_with_extra(schedule, plan, extra_clobber_words);
    let clobber = |func: FuncRef| {
        abs_clobber_words
            .get(&func)
            .copied()
            .or_else(|| plan.funcs.get(&func).map(FuncMemPlan::active_abs_words))
            .unwrap_or(0)
    };

    // clamp(f) = max over callers c of max(clobber(c), clamp(c)). One
    // forward-topo pass over the condensation; within a cyclic SCC every
    // member is transitively a caller of every other, so the SCC folds its
    // own members' clobber bounds.
    let mut incoming: FxHashMap<SccRef, u32> = FxHashMap::default();
    let mut clamp_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for &scc_ref in &schedule.topo {
        let members = schedule.members(scc_ref);
        let scc_max_clobber = members.iter().map(|&func| clobber(func)).max().unwrap_or(0);
        let mut clamp = incoming.get(&scc_ref).copied().unwrap_or(0);
        if schedule.sccs.scc_info(scc_ref).is_cycle {
            clamp = clamp.max(scc_max_clobber);
        }
        for &func in members {
            clamp_words.insert(func, clamp);
        }
        let push = clamp.max(scc_max_clobber);
        for callee_scc in schedule.scc_edges.get(&scc_ref).into_iter().flatten() {
            incoming
                .entry(*callee_scc)
                .and_modify(|cur| *cur = (*cur).max(push))
                .or_insert(push);
        }
    }

    clamp_words
}

pub(crate) fn prepare_free_ptr_restore(
    function: &mut Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) {
    let _span = trace_span!("sonatina.codegen.evm.prepare_free_ptr_restore").entered();
    let mut did_insert = false;
    loop {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);

        let mut splitter = CriticalEdgeSplitter::new();
        splitter.run(function, &mut cfg);

        let mut liveness = Liveness::new();
        liveness.compute(function, &cfg);

        let mut inst_liveness = InstLiveness::new();
        inst_liveness.compute(function, &cfg, &liveness);

        let transient_mallocs = malloc_plan::compute_transient_mallocs(
            function,
            module,
            &backend.isa,
            ptr_escape,
            None,
            &inst_liveness,
        );

        if !did_insert
            && malloc_plan::should_restore_free_ptr_on_internal_returns(
                function,
                module,
                &backend.isa,
                ptr_escape,
                &transient_mallocs,
            )
        {
            malloc_plan::insert_free_ptr_restore_on_internal_returns(function, &backend.isa);
            did_insert = true;
            continue;
        }

        break;
    }
}

fn prepare_high_evm_pre_analysis(
    function: &mut Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
) -> memory_plan::FuncPreAnalysis {
    let _span = trace_span!("sonatina.codegen.evm.prepare_high_evm_pre_analysis").entered();
    let mut cfg = ControlFlowGraph::new();
    {
        let _span = trace_span!("sonatina.codegen.evm.pre_analysis.compute_cfg").entered();
        cfg.compute(function);
    }

    {
        let _span = trace_span!("sonatina.codegen.evm.pre_analysis.split_critical_edges").entered();
        let mut splitter = CriticalEdgeSplitter::new();
        splitter.run(function, &mut cfg);
    }

    let block_order = {
        let _span = trace_span!("sonatina.codegen.evm.pre_analysis.compute_domtree").entered();
        let mut dom = DomTree::new();
        dom.compute(&cfg);
        dom.rpo().to_owned()
    };

    let inst_liveness = {
        let _span = trace_span!("sonatina.codegen.evm.pre_analysis.compute_liveness").entered();
        let mut liveness = Liveness::new();
        liveness.compute(function, &cfg);

        let mut inst_liveness = InstLiveness::new();
        inst_liveness.compute(function, &cfg, &liveness);
        inst_liveness
    };

    let value_aliases = {
        let _span = trace_span!("sonatina.codegen.evm.pre_analysis.canonicalize_aliases").entered();
        backend.compute_high_evm_value_aliases(function, module)
    };

    memory_plan::FuncPreAnalysis {
        inst_liveness,
        block_order,
        value_aliases,
    }
}

fn compute_high_evm_pre_analyses(
    module: &Module,
    funcs: &[FuncRef],
    backend: &EvmBackend,
) -> FxHashMap<FuncRef, memory_plan::FuncPreAnalysis> {
    let _span = debug_span!("sonatina.codegen.evm.compute_high_evm_pre_analyses").entered();
    let mut results: Vec<_> = funcs
        .par_iter()
        .copied()
        .map(|func| {
            let analysis = module.func_store.modify(func, |function| {
                prepare_high_evm_pre_analysis(function, &module.ctx, backend)
            });
            (func, analysis)
        })
        .collect();
    results.sort_unstable_by_key(|(func, _)| func.as_u32());

    let mut analyses = FxHashMap::default();
    for (func, analysis) in results {
        analyses.insert(func, analysis);
    }
    analyses
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        I256, Immediate, Linkage, Signature, Type,
        builder::{FunctionBuilder, ModuleBuilder},
        func_cursor::InstInserter,
        inst::{
            control_flow::Return,
            evm::{
                EvmCalldataCopy, EvmMstore, EvmMstore8, EvmStaticCall,
                machine_inst_set::EvmMachineInstSet,
            },
        },
        isa::{Isa, evm::EvmMachine},
        module::ModuleCtx,
    };
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use super::{FixedMemoryWriteRange, machine_fixed_memory_write_ranges};

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

    fn word(builder: &mut FunctionBuilder<InstInserter>, val: i64) -> sonatina_ir::ValueId {
        builder.make_imm_value(Immediate::from_i256(I256::from(val), Type::I256))
    }

    fn collect_machine_write_ranges(
        args: &[Type],
        insert: impl FnOnce(&mut FunctionBuilder<InstInserter>, &'static EvmMachineInstSet),
    ) -> Vec<FixedMemoryWriteRange> {
        let mb = machine_builder();
        let func_ref = mb
            .declare_function(Signature::new_unit("test_func", Linkage::Public, args))
            .expect("test function declaration succeeds");
        let machine = EvmMachine::new(mb.triple());
        let is = machine.inst_set();
        let mut builder = mb.func_builder::<InstInserter>(func_ref);

        let entry = builder.append_block();
        builder.switch_to_block(entry);
        insert(&mut builder, is);
        builder.insert_inst_no_result(Return::new_unit(is));
        builder.seal_all();
        builder.finish();

        let module = mb.build();
        module.func_store.view(func_ref, |function| {
            machine_fixed_memory_write_ranges(function, &machine)
        })
    }

    fn range_bytes(ranges: &[FixedMemoryWriteRange]) -> Vec<(u32, u32)> {
        ranges
            .iter()
            .map(|range| (range.start_byte, range.end_byte))
            .collect()
    }

    #[test]
    fn fixed_write_collector_records_word_and_byte_stores() {
        let ranges = collect_machine_write_ranges(&[], |builder, is| {
            let word_addr = word(builder, 0x80);
            let byte_addr = word(builder, 0x123);
            let value = word(builder, 7);
            builder.insert_inst_no_result(EvmMstore::new(is, word_addr, value));
            builder.insert_inst_no_result(EvmMstore8::new(is, byte_addr, value));
        });

        assert_eq!(range_bytes(&ranges), vec![(0x80, 0xa0), (0x123, 0x124)]);
    }

    #[test]
    fn fixed_write_collector_records_copy_ranges() {
        let ranges = collect_machine_write_ranges(&[], |builder, is| {
            let dst = word(builder, 0x140);
            let offset = word(builder, 0);
            let len = word(builder, 0x45);
            builder.insert_inst_no_result(EvmCalldataCopy::new(is, dst, offset, len));
        });

        assert_eq!(range_bytes(&ranges), vec![(0x140, 0x185)]);
    }

    #[test]
    fn fixed_write_collector_records_staticcall_return_ranges() {
        let ranges = collect_machine_write_ranges(&[], |builder, is| {
            let gas = word(builder, 100_000);
            let ext_addr = word(builder, 0xabc);
            let arg_addr = word(builder, 0x20);
            let arg_len = word(builder, 0x40);
            let ret_addr = word(builder, 0x180);
            let ret_len = word(builder, 0x60);
            builder.insert_inst_no_result(EvmStaticCall::new(
                is, gas, ext_addr, arg_addr, arg_len, ret_addr, ret_len,
            ));
        });

        assert_eq!(range_bytes(&ranges), vec![(0x180, 0x1e0)]);
    }

    #[test]
    fn fixed_write_collector_ignores_zero_length_writes() {
        let ranges = collect_machine_write_ranges(&[], |builder, is| {
            let zero = word(builder, 0);
            let dst = word(builder, 0x140);
            let gas = word(builder, 100_000);
            let ext_addr = word(builder, 0xabc);
            let arg_addr = word(builder, 0x20);
            let arg_len = word(builder, 0x40);
            let ret_addr = word(builder, 0x180);
            builder.insert_inst_no_result(EvmCalldataCopy::new(is, dst, zero, zero));
            builder.insert_inst_no_result(EvmStaticCall::new(
                is, gas, ext_addr, arg_addr, arg_len, ret_addr, zero,
            ));
        });

        assert!(ranges.is_empty());
    }

    #[test]
    fn fixed_write_collector_ignores_non_constant_ranges() {
        let ranges = collect_machine_write_ranges(&[Type::I256], |builder, is| {
            let dynamic = builder.args()[0];
            let dst = word(builder, 0x140);
            let offset = word(builder, 0);
            let value = word(builder, 7);
            builder.insert_inst_no_result(EvmMstore::new(is, dynamic, value));
            builder.insert_inst_no_result(EvmCalldataCopy::new(is, dst, offset, dynamic));
        });

        assert!(ranges.is_empty());
    }
}
