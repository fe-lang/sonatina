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
    stackalloc::StackifyAlloc,
};
use sonatina_ir::{
    AccessKind, AccessLoc, Function, GlobalVariableRef, InstSetExt, Module, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{
        Isa,
        evm::{EvmMachine, space::MEMORY},
    },
    module::{FuncRef, ModuleCtx},
    object::EmbedSymbol,
};

use super::{
    EvmBackend, LateCleanupProfile,
    dyn_sp::{DynSpInitKind, FuncDynSpPlan},
    emit::{
        LateBlockAliasPlan, compute_function_entry_jump_targets, compute_late_block_alias_plan,
        immediate_u32, rewrite_evm_local_fallthrough_layout,
    },
    machine::{
        final_spills::allocate_final_spills, lower::lower_section_to_machine,
        module::FuncMachineMap, pipeline::run_machine_opt_pipeline,
        placement::compute_semantic_memory_placement, prepare::prepare_machine_stackify_analyses,
    },
    malloc_plan,
    memory_plan::{
        self, DYN_SP_SLOT, FREE_PTR_SLOT, FuncMemPlan, ProgramMemoryPlan, STATIC_BASE, WORD_BYTES,
        compute_abs_clobber_words_with_extra,
    },
    pipeline::EvmPipeline,
    provenance::{Provenance, compute_value_provenance},
    ptr_escape::PtrEscapeSummary,
    scratch_plan,
};

const FREE_PTR_SLOT_START: u32 = FREE_PTR_SLOT as u32;
const FREE_PTR_SLOT_END: u32 = FREE_PTR_SLOT_START + WORD_BYTES;
const DYN_SP_SLOT_START: u32 = DYN_SP_SLOT as u32;

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

    pub(crate) fn section_plan(&self) -> &EvmSectionPlan {
        &self.section_plan
    }
}

#[derive(Clone)]
pub(crate) struct EvmSectionPlan {
    pub(crate) arena_base: u32,
    pub(crate) dyn_base: u32,
    pub(crate) scratch_peak_words: u32,
    pub(crate) static_chain_peak_words: u32,
}

#[derive(Clone)]
pub(crate) struct EvmFunctionPlan {
    pub(crate) alloc: StackifyAlloc,
    pub(crate) emitted_block_order: Vec<sonatina_ir::BlockId>,
    pub(crate) block_aliases: FxHashMap<sonatina_ir::BlockId, sonatina_ir::BlockId>,
    pub(crate) mem_plan: FuncMemPlan,
    pub(crate) dyn_sp_plan: FuncDynSpPlan,
    pub(crate) function_entry_jumpdest: bool,
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

fn function_memory_accesses_match(
    function: &Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    pred: impl Fn(&Function, &sonatina_ir::MemoryAccess, &SecondaryMap<ValueId, Provenance>) -> bool,
) -> bool {
    let prov = compute_value_provenance(function, module, &backend.isa, |callee| {
        ptr_escape
            .get(&callee)
            .cloned()
            .unwrap_or_else(|| PtrEscapeSummary::conservative_unknown_ctx(module, callee))
    });

    function.layout.iter_block().any(|block| {
        function.layout.iter_inst(block).any(|inst| {
            // Section callees are scanned directly; call summaries only expose whole-space writes.
            if matches!(
                backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::Call(_) | EvmInstKind::EvmMalloc(_)
            ) {
                return false;
            }

            function
                .dfg
                .effects(inst)
                .accesses
                .iter()
                .any(|access| pred(function, access, &prov))
        })
    })
}

pub(crate) fn function_may_touch_free_ptr_slot(
    function: &Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) -> bool {
    function_memory_accesses_match(
        function,
        module,
        backend,
        ptr_escape,
        memory_access_may_touch_free_ptr_slot,
    )
}

pub(crate) fn function_may_write_free_ptr_slot(
    function: &Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) -> bool {
    function_memory_accesses_match(
        function,
        module,
        backend,
        ptr_escape,
        |function, access, prov| {
            access.kind == AccessKind::Write
                && memory_access_may_touch_free_ptr_slot(function, access, prov)
        },
    )
}

#[derive(Clone, Copy)]
pub(crate) enum MemoryLayoutReservation {
    None,
    Reserve { start: u32, len: u32 },
    LegacyFloor,
}

#[derive(Default)]
struct SectionMemoryLayout {
    max_reserved_end: u32,
    legacy_floor: bool,
}

impl SectionMemoryLayout {
    fn reserve_len(&mut self, start: u32, len: u32) {
        if len != 0 {
            match start.checked_add(len) {
                Some(end) => self.max_reserved_end = self.max_reserved_end.max(end),
                None => self.legacy_floor = true,
            }
        }
    }

    fn apply(&mut self, reservation: MemoryLayoutReservation) {
        match reservation {
            MemoryLayoutReservation::None => {}
            MemoryLayoutReservation::Reserve { start, len } => self.reserve_len(start, len),
            MemoryLayoutReservation::LegacyFloor => self.legacy_floor = true,
        }
    }

    fn arena_base(&self) -> u32 {
        let base = align_to_word(self.max_reserved_end).unwrap_or(STATIC_BASE);
        if self.legacy_floor {
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
            _ => MemoryLayoutReservation::LegacyFloor,
        };
    }

    if addr_is_allocator_managed(&prov[addr]) {
        MemoryLayoutReservation::None
    } else {
        MemoryLayoutReservation::LegacyFloor
    }
}

fn memory_layout_reservation_from_effect(
    function: &Function,
    access: &sonatina_ir::MemoryAccess,
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
            .map_or(MemoryLayoutReservation::LegacyFloor, |start| {
                MemoryLayoutReservation::Reserve { start, len: *bytes }
            }),
        AccessLoc::LinearRange { addr, len } => memory_layout_reservation_for_addr_len(
            function,
            *addr,
            MemoryAccessLen::Value(*len),
            prov,
        ),
        AccessLoc::WholeSpace | AccessLoc::Unknown => MemoryLayoutReservation::LegacyFloor,
        AccessLoc::KeyedExact { .. } => MemoryLayoutReservation::None,
    }
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

    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
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

pub(crate) struct ArenaBaseFacts {
    pub(crate) has_dynamic_frames: bool,
    pub(crate) has_stackify_scratch_spills: bool,
    pub(crate) backend_spill_reserve_words: u32,
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

    let spill_reserve_words = if facts.has_stackify_scratch_spills {
        facts
            .backend_spill_reserve_words
            .max(scratch_plan::SCRATCH_SPILL_SLOTS)
    } else {
        facts.backend_spill_reserve_words
    };
    layout.reserve_len(0, spill_reserve_words * WORD_BYTES);
    if facts.has_stackify_scratch_spills {
        layout.reserve_len(0, scratch_plan::SCRATCH_SPILL_SLOTS * WORD_BYTES);
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
    let scratch_effects = FxHashSet::default();
    let mut backend_spill_reserve_words: FxHashMap<FuncRef, u32> = FxHashMap::default();

    for iteration in 0..4 {
        let placement = compute_semantic_memory_placement(
            source_module,
            &funcs,
            &pre_analyses,
            &ptr_escape,
            &scratch_effects,
            backend,
            &backend_spill_reserve_words,
        );

        let machine = lower_section_to_machine(&work, &funcs, &placement, backend)?;
        run_machine_opt_pipeline(machine.work.module(), &funcs)?;

        let machine_isa = EvmMachine::new(machine.work.module().ctx.triple);
        let machine_analyses = prepare_machine_stackify_analyses(
            machine.work.module(),
            &funcs,
            backend,
            &machine_isa,
        )?;
        let function_entry_jump_targets =
            compute_function_entry_jump_targets(machine.work.module(), &funcs);

        let section_plan = EvmSectionPlan {
            arena_base: placement.arena_base,
            dyn_base: placement.global_dyn_base,
            scratch_peak_words: placement.scratch_peak_words,
            static_chain_peak_words: placement.static_chain_peak_words,
        };

        let mut actual_spill_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
        let mut function_plans = FxHashMap::default();
        let mut results: Vec<_> = machine_analyses
            .into_par_iter()
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
                let final_spills = allocate_final_spills(analysis.alloc, mem_plan);
                let dyn_sp_plan = conservative_machine_dyn_sp_plan(&final_spills.mem_plan);
                let alias_plan = machine.work.module().func_store.view(func, |function| {
                    compute_late_block_alias_plan(
                        function,
                        &final_spills.alloc,
                        &analysis.block_order,
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
                        )
                    })
                } else {
                    emitted_block_order
                };
                (
                    func,
                    final_spills.peak_words,
                    EvmFunctionPlan {
                        alloc: final_spills.alloc,
                        emitted_block_order,
                        block_aliases,
                        mem_plan: final_spills.mem_plan,
                        dyn_sp_plan,
                        function_entry_jumpdest: function_entry_jump_targets.contains(&func),
                    },
                )
            })
            .collect();
        results.sort_unstable_by_key(|(func, ..)| func.as_u32());
        for (func, peak_words, plan) in results {
            actual_spill_words.insert(func, peak_words);
            function_plans.insert(func, plan);
        }

        let reserve_peak = backend_spill_reserve_words
            .values()
            .copied()
            .max()
            .unwrap_or(0);
        let actual_peak = actual_spill_words.values().copied().max().unwrap_or(0);
        debug!(
            iteration,
            reserve_peak, actual_peak, "evm machine spill reserve iteration"
        );

        let spill_reserve_satisfied = actual_spill_words.iter().all(|(func, actual)| {
            *actual <= backend_spill_reserve_words.get(func).copied().unwrap_or(0)
        });

        if spill_reserve_satisfied || iteration == 3 {
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

        backend_spill_reserve_words = actual_spill_words;
        debug!(
            iteration,
            actual_peak, "rerunning evm machine prepare with larger spill reserve"
        );
    }

    unreachable!("machine spill-reserve loop always returns by iteration cap")
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

fn conservative_machine_dyn_sp_plan(mem_plan: &FuncMemPlan) -> FuncDynSpPlan {
    if mem_plan.uses_dynamic_frame() {
        FuncDynSpPlan {
            entry_init: Some(DynSpInitKind::Checked),
            entry_live_frame: true,
        }
    } else {
        FuncDynSpPlan::default()
    }
}

pub(crate) fn compute_return_escape_caller_clamp_words(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
    extra_clobber_words: &FxHashMap<FuncRef, u32>,
) -> FxHashMap<FuncRef, u32> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let abs_clobber_words =
        compute_abs_clobber_words_with_extra(module, funcs, plan, extra_clobber_words);

    let mut callers: FxHashMap<FuncRef, FxHashSet<FuncRef>> = FxHashMap::default();
    let mut clamp_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for &func in funcs {
        clamp_words.insert(func, 0);
    }

    for &caller in funcs {
        module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(call) = function.dfg.call_info(inst) else {
                        continue;
                    };
                    let callee = call.callee();
                    if funcs_set.contains(&callee) {
                        callers.entry(callee).or_default().insert(caller);
                    }
                }
            }
        });
    }

    let mut changed = true;
    while changed {
        changed = false;

        for &func in funcs {
            let mut next = clamp_words.get(&func).copied().unwrap_or(0);
            for caller in callers.get(&func).into_iter().flatten() {
                let caller_clobber_words = abs_clobber_words
                    .get(caller)
                    .copied()
                    .or_else(|| plan.funcs.get(caller).map(FuncMemPlan::active_abs_words))
                    .unwrap_or(0);
                let caller_transitive_words = clamp_words.get(caller).copied().unwrap_or(0);
                next = next.max(caller_clobber_words.max(caller_transitive_words));
            }

            let cur = clamp_words.get(&func).copied().unwrap_or(0);
            if next > cur {
                clamp_words.insert(func, next);
                changed = true;
            }
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
        backend.compute_stackify_value_aliases(function, module)
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
