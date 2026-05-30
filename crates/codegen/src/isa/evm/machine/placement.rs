use cranelift_entity::SecondaryMap;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    AccessKind, BlockId, Function, InstId, InstSetExt, Module, Value, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{
        Isa,
        evm::{Evm, space::MEMORY},
    },
    module::{FuncRef, ModuleCtx},
};

use crate::{
    isa::evm::provenance::{Provenance, compute_value_provenance},
    module_analysis::CallGraph,
};

use super::{
    super::{
        EvmBackend, heap_plan, malloc_plan,
        mem_effects::compute_func_mem_effects,
        memory_plan::{self, BackendSpillReserve, FuncPreAnalysis, ObjLoc, StableMode, WORD_BYTES},
        prepare::{
            ArenaBaseFacts, choose_arena_base, compute_return_escape_caller_clamp_words,
            function_free_ptr_slot_facts, memory_access_may_touch_free_ptr_slot,
        },
        ptr_escape::PtrEscapeSummary,
    },
    free_ptr_floor::{
        ProgramFreePtrFloorInput, compute_free_ptr_write_summaries,
        compute_program_free_ptr_floor_before_malloc,
    },
};

#[derive(Clone, Debug)]
pub(crate) struct EvmMemoryPlacementPlan {
    pub(crate) arena_base: u32,
    pub(crate) global_dyn_base: u32,
    pub(crate) scratch_peak_words: u32,
    pub(crate) static_chain_peak_words: u32,
    pub(crate) funcs: FxHashMap<FuncRef, EvmFuncPlacementPlan>,
}

#[derive(Clone, Debug)]
pub(crate) struct EvmFuncPlacementPlan {
    pub(crate) arena_base: u32,
    pub(crate) stable_mode: StableMode,
    pub(crate) stable_words: u32,
    pub(crate) mem_plan: memory_plan::FuncMemPlan,
    pub(crate) alloca_loc: FxHashMap<InstId, ObjLoc>,
    pub(crate) malloc_placements: FxHashMap<InstId, MallocPlacement>,
    pub(crate) free_ptr_floor_before_malloc: FxHashMap<InstId, Option<u32>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MallocPlacement {
    Fixed {
        base: u32,
    },
    Heap {
        min_base: u32,
        needs_dyn_sp_clamp: bool,
        update_free_ptr: bool,
    },
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct MemoryPlacementSection<'a> {
    pub(crate) funcs: &'a [FuncRef],
    pub(crate) entry: FuncRef,
    pub(crate) includes: &'a [FuncRef],
}

pub(crate) fn compute_semantic_memory_placement(
    module: &Module,
    section: MemoryPlacementSection<'_>,
    analyses: &FxHashMap<FuncRef, FuncPreAnalysis>,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    scratch_effects: &FxHashSet<FuncRef>,
    backend: &EvmBackend,
    backend_spill_reserves: &FxHashMap<FuncRef, BackendSpillReserve>,
) -> EvmMemoryPlacementPlan {
    let funcs = section.funcs;
    let mut semantic_plan = memory_plan::compute_semantic_program_memory_plan(
        module,
        funcs,
        analyses,
        ptr_escape,
        &backend.isa,
        &backend.arena_cost_model,
    );
    semantic_plan.apply_backend_spill_reserves(module, funcs, backend_spill_reserves);

    let mem_effects =
        compute_func_mem_effects(module, funcs, &semantic_plan, scratch_effects, &backend.isa);
    let return_escape_caller_abs_words = compute_return_escape_caller_clamp_words(
        module,
        funcs,
        &semantic_plan,
        &FxHashMap::default(),
    );

    let mut annotations: Vec<_> = funcs
        .par_iter()
        .copied()
        .map(|func| {
            let analysis = analyses
                .get(&func)
                .unwrap_or_else(|| panic!("missing pre-analysis for func {}", func.as_u32()));
            let (malloc_escape_kinds, transient_mallocs) =
                module.func_store.view(func, |function| {
                    let escape_kinds = malloc_plan::compute_malloc_escape_kinds_for_function(
                        function,
                        &module.ctx,
                        &backend.isa,
                        ptr_escape,
                    );
                    let transient = malloc_plan::compute_transient_mallocs(
                        function,
                        &module.ctx,
                        &backend.isa,
                        ptr_escape,
                        Some(&mem_effects),
                        &analysis.inst_liveness,
                    );
                    (escape_kinds, transient)
                });
            (
                func,
                malloc_escape_kinds,
                transient_mallocs,
                return_escape_caller_abs_words
                    .get(&func)
                    .copied()
                    .unwrap_or(0),
            )
        })
        .collect();
    annotations.sort_unstable_by_key(|(func, ..)| func.as_u32());
    for (func, malloc_escape_kinds, transient_mallocs, return_escape_caller_abs_words) in
        annotations
    {
        if let Some(func_plan) = semantic_plan.funcs.get_mut(&func) {
            func_plan.malloc_escape_kinds = malloc_escape_kinds;
            func_plan.transient_mallocs = transient_mallocs;
            func_plan.return_escape_caller_abs_words = return_escape_caller_abs_words;
        }
    }
    let has_dynamic_frames = semantic_plan
        .funcs
        .values()
        .any(memory_plan::FuncMemPlan::uses_dynamic_frame);
    let backend_spill_scratch_reserve_peak = backend_spill_reserves
        .values()
        .map(|reserve| reserve.scratch_words)
        .max()
        .unwrap_or(0);
    let has_persistent_mallocs = funcs.iter().copied().any(|func| {
        let Some(func_plan) = semantic_plan.funcs.get(&func) else {
            return false;
        };
        module.func_store.view(func, |function| {
            function.layout.iter_block().any(|block| {
                function.layout.iter_inst(block).any(|inst| {
                    matches!(
                        backend.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                        EvmInstKind::EvmMalloc(_)
                    ) && !func_plan.transient_mallocs.contains(&inst)
                })
            })
        })
    });
    let entry_may_have_live_frame =
        compute_entry_may_have_live_frame(module, funcs, &semantic_plan);

    let arena_base = choose_arena_base(
        module,
        funcs,
        backend,
        ptr_escape,
        ArenaBaseFacts {
            has_dynamic_frames,
            has_stackify_scratch_spills: !scratch_effects.is_empty(),
            backend_spill_scratch_reserve_words: backend_spill_scratch_reserve_peak,
            has_persistent_mallocs,
        },
    );
    if has_dynamic_frames {
        semantic_plan.scratch_peak_words = semantic_plan
            .scratch_peak_words
            .max(backend_spill_scratch_reserve_peak);
    }
    semantic_plan.set_arena_base(arena_base);

    let mut malloc_bounds = heap_plan::compute_semantic_malloc_future_abs_words_with_extra(
        module,
        funcs,
        &semantic_plan,
        analyses,
        &backend.isa,
        &FxHashMap::default(),
    );
    for (&func, &reserve) in backend_spill_reserves {
        if let Some(bounds) = malloc_bounds.get_mut(&func)
            && let Some(func_plan) = semantic_plan.funcs.get(&func)
        {
            let reserve_abs_words = backend_spill_reserve_abs_words(func_plan, reserve);
            for bound in bounds.values_mut() {
                *bound = (*bound).max(reserve_abs_words);
            }
        }
    }
    for (func, bounds) in malloc_bounds {
        if let Some(func_plan) = semantic_plan.funcs.get_mut(&func) {
            func_plan.malloc_future_abs_words = bounds;
        }
    }

    let (free_ptr_slot_may_be_touched, free_ptr_write_summaries) =
        compute_program_free_ptr_slot_facts(module, funcs, backend, ptr_escape);
    let placement_ctx = MallocPlacementCtx {
        isa: &backend.isa,
        module: &module.ctx,
        ptr_escape,
        global_dyn_base: semantic_plan.global_dyn_base,
        backend_spill_reserve_peak: backend_spill_scratch_reserve_peak,
        entry_may_have_live_frame: &entry_may_have_live_frame,
        section_entry: section.entry,
        has_persistent_mallocs,
        free_ptr_slot_may_be_touched,
    };
    let malloc_placements: FxHashMap<_, _> = funcs
        .iter()
        .copied()
        .map(|func| {
            let func_plan = semantic_plan
                .funcs
                .get(&func)
                .unwrap_or_else(|| panic!("missing semantic plan for func {}", func.as_u32()));
            let malloc_placements = module.func_store.view(func, |function| {
                placement_ctx.compute_func_malloc_placements(function, func, func_plan)
            });
            (func, malloc_placements)
        })
        .collect();
    let free_ptr_floor_before_malloc =
        compute_program_free_ptr_floor_before_malloc(ProgramFreePtrFloorInput {
            module,
            funcs,
            section_entry: section.entry,
            section_includes: section.includes,
            backend,
            ptr_escape,
            source_is: backend.isa.inst_set(),
            malloc_placements: &malloc_placements,
            free_ptr_write_summaries: &free_ptr_write_summaries,
        });
    let func_placements = funcs
        .iter()
        .copied()
        .map(|func| {
            let func_plan = semantic_plan
                .funcs
                .get(&func)
                .unwrap_or_else(|| panic!("missing semantic plan for func {}", func.as_u32()));
            let malloc_placements = malloc_placements.get(&func).cloned().unwrap_or_default();
            let free_ptr_floor_before_malloc = free_ptr_floor_before_malloc
                .get(&func)
                .cloned()
                .unwrap_or_default();
            (
                func,
                EvmFuncPlacementPlan {
                    arena_base: func_plan.arena_base,
                    stable_mode: func_plan.stable_mode,
                    stable_words: func_plan.stable_words,
                    mem_plan: machine_mem_plan_from_semantic(func_plan),
                    alloca_loc: func_plan.alloca_loc.clone(),
                    malloc_placements,
                    free_ptr_floor_before_malloc,
                },
            )
        })
        .collect();

    EvmMemoryPlacementPlan {
        arena_base: semantic_plan.arena_base,
        global_dyn_base: semantic_plan.global_dyn_base,
        scratch_peak_words: semantic_plan.scratch_peak_words,
        static_chain_peak_words: semantic_plan.static_chain_peak_words,
        funcs: func_placements,
    }
}

struct MallocPlacementCtx<'a> {
    isa: &'a Evm,
    module: &'a ModuleCtx,
    ptr_escape: &'a FxHashMap<FuncRef, PtrEscapeSummary>,
    global_dyn_base: u32,
    backend_spill_reserve_peak: u32,
    entry_may_have_live_frame: &'a FxHashMap<FuncRef, bool>,
    section_entry: FuncRef,
    has_persistent_mallocs: bool,
    free_ptr_slot_may_be_touched: bool,
}

impl MallocPlacementCtx<'_> {
    fn compute_func_malloc_placements(
        &self,
        function: &Function,
        func: FuncRef,
        func_plan: &memory_plan::FuncMemPlan,
    ) -> FxHashMap<InstId, MallocPlacement> {
        let mut out = FxHashMap::default();
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);
        let needs_dyn_sp_clamp = func_plan.uses_dynamic_frame()
            || self
                .entry_may_have_live_frame
                .get(&func)
                .copied()
                .unwrap_or(false);
        let prov = compute_value_provenance(function, self.module, self.isa, |callee| {
            PtrEscapeSummary::get_or_conservative(self.ptr_escape, self.module, callee)
        });
        let exact_heap_base_before_malloc = ExactHeapBaseAnalysis {
            function,
            isa: self.isa,
            cfg: &cfg,
            func_plan,
            prov: &prov,
            entry_heap_base_is_exact: !needs_dyn_sp_clamp,
        }
        .compute();
        let terminal_private_mallocs = TerminalPrivateMallocAnalysis::new(
            function,
            self.isa,
            &cfg,
            &exact_heap_base_before_malloc,
        )
        .compute();
        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                if !matches!(
                    self.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                    EvmInstKind::EvmMalloc(_)
                ) {
                    continue;
                }

                let transient = func_plan.transient_mallocs.contains(&inst);
                let min_base = malloc_min_base(
                    func_plan,
                    self.global_dyn_base,
                    self.backend_spill_reserve_peak,
                    inst,
                );
                let exact_heap_base = exact_heap_base_before_malloc
                    .get(&inst)
                    .copied()
                    .unwrap_or(false);
                let placement = if transient
                    && (terminal_private_mallocs.contains(&inst)
                        || (exact_heap_base
                            && self.section_entry == func
                            && function.arg_values.is_empty()
                            && malloc_private_uses_are_compatible_with_fixed_base(
                                function,
                                self.isa,
                                inst,
                                exact_heap_base,
                            ))
                        || (!self.free_ptr_slot_may_be_touched
                            && !needs_dyn_sp_clamp
                            && !self.has_persistent_mallocs))
                {
                    MallocPlacement::Fixed { base: min_base }
                } else {
                    MallocPlacement::Heap {
                        min_base,
                        needs_dyn_sp_clamp,
                        update_free_ptr: !transient,
                    }
                };
                out.insert(inst, placement);
            }
        }
        out
    }
}

struct TerminalPrivateMallocAnalysis<'a> {
    function: &'a Function,
    isa: &'a Evm,
    cfg: &'a ControlFlowGraph,
    exact_heap_base_before_malloc: &'a FxHashMap<InstId, bool>,
    terminal_private_blocks: SecondaryMap<BlockId, bool>,
}

impl<'a> TerminalPrivateMallocAnalysis<'a> {
    fn new(
        function: &'a Function,
        isa: &'a Evm,
        cfg: &'a ControlFlowGraph,
        exact_heap_base_before_malloc: &'a FxHashMap<InstId, bool>,
    ) -> Self {
        let mut terminal_private_blocks = SecondaryMap::new();
        for block in function.layout.iter_block() {
            let _ = &mut terminal_private_blocks[block];
        }
        Self {
            function,
            isa,
            cfg,
            exact_heap_base_before_malloc,
            terminal_private_blocks,
        }
    }

    fn compute(mut self) -> FxHashSet<InstId> {
        self.compute_terminal_private_blocks();

        let mut out = FxHashSet::default();
        for block in self.function.layout.iter_block() {
            for inst in self.function.layout.iter_inst(block) {
                if matches!(self.resolve(inst), EvmInstKind::EvmMalloc(_))
                    && self
                        .suffix_is_terminal_private(block, self.function.layout.next_inst_of(inst))
                    && self.malloc_is_private(inst)
                {
                    out.insert(inst);
                }
            }
        }

        out
    }

    fn compute_terminal_private_blocks(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            for block in self.function.layout.iter_block() {
                let next = self.block_is_terminal_private(block);
                changed |= self.terminal_private_blocks[block] != next;
                self.terminal_private_blocks[block] = next;
            }
        }
    }

    fn block_is_terminal_private(&self, block: BlockId) -> bool {
        for inst in self.function.layout.iter_inst(block) {
            if self.inst_is_evm_terminal(inst) {
                return true;
            }
            if self.function.dfg.inst(inst).is_terminator() {
                return self.successors_are_terminal_private(block);
            }
            if !self.inst_allows_terminal_private_prefix(inst) {
                return false;
            }
        }

        self.successors_are_terminal_private(block)
    }

    fn successors_are_terminal_private(&self, block: BlockId) -> bool {
        let mut succs = self.cfg.succs_of(block);
        let Some(first) = succs.next() else {
            return false;
        };
        self.terminal_private_blocks[*first]
            && succs.all(|succ| self.terminal_private_blocks[*succ])
    }

    fn inst_is_evm_terminal(&self, inst: InstId) -> bool {
        matches!(
            self.resolve(inst),
            EvmInstKind::EvmReturn(_) | EvmInstKind::EvmRevert(_)
        )
    }

    fn inst_allows_terminal_private_prefix(&self, inst: InstId) -> bool {
        let effects = self.function.dfg.effects(inst);
        self.function.dfg.call_info(inst).is_none()
            && effects.other.is_empty()
            && effects
                .accesses
                .iter()
                .all(|access| access.kind == AccessKind::Write && access.space == MEMORY)
    }

    fn suffix_is_terminal_private(&self, block: BlockId, mut cursor: Option<InstId>) -> bool {
        while let Some(inst) = cursor {
            if self.inst_is_evm_terminal(inst) {
                return true;
            }
            if self.function.dfg.inst(inst).is_terminator() {
                return self.successors_are_terminal_private(block);
            }
            if !self.inst_allows_terminal_private_prefix(inst) {
                return false;
            }
            cursor = self.function.layout.next_inst_of(inst);
        }

        self.successors_are_terminal_private(block)
    }

    fn malloc_is_private(&self, inst: InstId) -> bool {
        malloc_private_uses_are_compatible_with_fixed_base(
            self.function,
            self.isa,
            inst,
            self.exact_heap_base_before_malloc
                .get(&inst)
                .copied()
                .unwrap_or(false),
        )
    }

    fn resolve(&self, inst: InstId) -> EvmInstKind<'_> {
        self.isa
            .inst_set()
            .resolve_inst(self.function.dfg.inst(inst))
    }
}

struct ExactHeapBaseAnalysis<'a> {
    function: &'a Function,
    isa: &'a Evm,
    cfg: &'a ControlFlowGraph,
    func_plan: &'a memory_plan::FuncMemPlan,
    prov: &'a SecondaryMap<ValueId, Provenance>,
    entry_heap_base_is_exact: bool,
}

impl<'a> ExactHeapBaseAnalysis<'a> {
    fn compute(&self) -> FxHashMap<InstId, bool> {
        let mut block_in = SecondaryMap::new();
        let mut block_out = SecondaryMap::new();
        for block in self.function.layout.iter_block() {
            block_in[block] = self.entry_heap_base_is_exact;
            block_out[block] = self.entry_heap_base_is_exact;
        }

        let mut changed = true;
        while changed {
            changed = false;
            for block in self.function.layout.iter_block() {
                let next_in = self.block_entry_is_exact(&block_out, block);
                let next_out = self.transfer_block(block, next_in, None);
                changed |= block_in[block] != next_in || block_out[block] != next_out;
                block_in[block] = next_in;
                block_out[block] = next_out;
            }
        }

        let mut exact_before_malloc = FxHashMap::default();
        for block in self.function.layout.iter_block() {
            self.transfer_block(block, block_in[block], Some(&mut exact_before_malloc));
        }
        exact_before_malloc
    }

    fn block_entry_is_exact(
        &self,
        block_out: &SecondaryMap<BlockId, bool>,
        block: BlockId,
    ) -> bool {
        let mut preds = self.cfg.preds_of(block);
        let Some(first) = preds.next() else {
            return self.entry_heap_base_is_exact;
        };
        block_out[*first] && preds.all(|pred| block_out[*pred])
    }

    fn transfer_block(
        &self,
        block: BlockId,
        mut exact: bool,
        mut exact_before_malloc: Option<&mut FxHashMap<InstId, bool>>,
    ) -> bool {
        for inst in self.function.layout.iter_inst(block) {
            match self.resolve(inst) {
                EvmInstKind::EvmMalloc(_) => {
                    if let Some(exact_before_malloc) = exact_before_malloc.as_deref_mut() {
                        exact_before_malloc.insert(inst, exact);
                    }
                    if !self.func_plan.transient_mallocs.contains(&inst) {
                        exact = false;
                    }
                }
                EvmInstKind::Call(_) => exact = false,
                _ if self.inst_writes_free_ptr_slot(inst) => exact = false,
                _ => {}
            }
        }
        exact
    }

    fn inst_writes_free_ptr_slot(&self, inst: InstId) -> bool {
        self.function
            .dfg
            .effects(inst)
            .accesses
            .iter()
            .any(|access| {
                access.kind == AccessKind::Write
                    && memory_access_may_touch_free_ptr_slot(self.function, access, self.prov)
            })
    }

    fn resolve(&self, inst: InstId) -> EvmInstKind<'_> {
        self.isa
            .inst_set()
            .resolve_inst(self.function.dfg.inst(inst))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PrivateMallocUseInfo {
    requires_exact_heap_base: bool,
}

struct PrivateMallocUseAnalysis<'a> {
    function: &'a Function,
    isa: &'a Evm,
    malloc: InstId,
    derived_values: FxHashSet<ValueId>,
}

impl<'a> PrivateMallocUseAnalysis<'a> {
    fn new(function: &'a Function, isa: &'a Evm, malloc: InstId) -> Self {
        let mut analysis = Self {
            function,
            isa,
            malloc,
            derived_values: function.dfg.inst_results(malloc).iter().copied().collect(),
        };
        analysis.compute_derived_values();
        analysis
    }

    fn analyze_private_address_uses(&self) -> Option<PrivateMallocUseInfo> {
        let mut requires_exact_heap_base = false;
        for block in self.function.layout.iter_block() {
            for inst in self.function.layout.iter_inst(block) {
                if inst != self.malloc && self.inst_uses_derived_value(inst) {
                    requires_exact_heap_base |= self.use_requires_exact_heap_base(inst)?;
                }
            }
        }

        Some(PrivateMallocUseInfo {
            requires_exact_heap_base,
        })
    }

    fn compute_derived_values(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            for block in self.function.layout.iter_block() {
                for inst in self.function.layout.iter_inst(block) {
                    if inst != self.malloc && self.inst_uses_derived_value(inst) {
                        changed |= self.add_address_derived_results(inst);
                    }
                }
            }
        }
    }

    fn add_address_derived_results(&mut self, inst: InstId) -> bool {
        match self.resolve(inst) {
            EvmInstKind::Bitcast(_)
            | EvmInstKind::IntToPtr(_)
            | EvmInstKind::PtrToInt(_)
            | EvmInstKind::Gep(_)
            | EvmInstKind::Add(_)
            | EvmInstKind::Sub(_)
            | EvmInstKind::Phi(_) => {
                let mut changed = false;
                for result in self.function.dfg.inst_results(inst) {
                    changed |= self.derived_values.insert(*result);
                }
                changed
            }
            EvmInstKind::Uaddo(_)
            | EvmInstKind::Saddo(_)
            | EvmInstKind::Usubo(_)
            | EvmInstKind::Ssubo(_) => self
                .function
                .dfg
                .inst_results(inst)
                .first()
                .is_some_and(|result| self.derived_values.insert(*result)),
            _ => false,
        }
    }

    fn use_requires_exact_heap_base(&self, inst: InstId) -> Option<bool> {
        if self.inst_derives_address(inst) {
            return self
                .checked_overflow_flag(inst)
                .map_or(Some(false), |flag| {
                    self.checked_overflow_flag_is_private_control(flag)
                });
        }

        match self.resolve(inst) {
            EvmInstKind::Lt(lt) => {
                self.address_overflow_predicate_requires_exact_heap_base(inst, *lt.lhs(), *lt.rhs())
            }
            EvmInstKind::Mstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                Some(false)
            }
            EvmInstKind::EvmMstore(mstore) if !self.derived_values.contains(mstore.value()) => {
                Some(false)
            }
            EvmInstKind::EvmMstore8(mstore) if !self.derived_values.contains(mstore.val()) => {
                Some(false)
            }
            EvmInstKind::EvmReturn(ret) if !self.derived_values.contains(ret.len()) => Some(false),
            EvmInstKind::EvmRevert(revert) if !self.derived_values.contains(revert.len()) => {
                Some(false)
            }
            _ => None,
        }
    }

    fn inst_derives_address(&self, inst: InstId) -> bool {
        matches!(
            self.resolve(inst),
            EvmInstKind::Bitcast(_)
                | EvmInstKind::IntToPtr(_)
                | EvmInstKind::PtrToInt(_)
                | EvmInstKind::Gep(_)
                | EvmInstKind::Add(_)
                | EvmInstKind::Sub(_)
                | EvmInstKind::Phi(_)
                | EvmInstKind::Uaddo(_)
                | EvmInstKind::Saddo(_)
                | EvmInstKind::Usubo(_)
                | EvmInstKind::Ssubo(_)
        )
    }

    fn checked_overflow_flag(&self, inst: InstId) -> Option<ValueId> {
        match self.resolve(inst) {
            EvmInstKind::Uaddo(_)
            | EvmInstKind::Saddo(_)
            | EvmInstKind::Usubo(_)
            | EvmInstKind::Ssubo(_) => self.function.dfg.inst_results(inst).get(1).copied(),
            _ => None,
        }
    }

    fn checked_overflow_flag_is_private_control(&self, flag: ValueId) -> Option<bool> {
        let mut used = false;
        for block in self.function.layout.iter_block() {
            for user in self.function.layout.iter_inst(block) {
                if !self.inst_uses_value(user, flag) {
                    continue;
                }

                used = true;
                let EvmInstKind::Br(br) = self.resolve(user) else {
                    return None;
                };
                if br.cond() != &flag
                    || self
                        .function
                        .dfg
                        .inst(user)
                        .collect_values()
                        .iter()
                        .any(|value| self.derived_values.contains(value))
                {
                    return None;
                }
            }
        }
        Some(used)
    }

    fn address_overflow_predicate_requires_exact_heap_base(
        &self,
        inst: InstId,
        lhs: ValueId,
        rhs: ValueId,
    ) -> Option<bool> {
        (self.value_is_add_of_base(lhs, rhs) && self.inst_result_uses_are_private_branches(inst))
            .then_some(true)
    }

    fn value_is_add_of_base(&self, value: ValueId, base: ValueId) -> bool {
        if !self.derived_values.contains(&value) || !self.derived_values.contains(&base) {
            return false;
        }

        let Some(Value::Inst { inst, .. }) = self.function.dfg.get_value(value) else {
            return false;
        };
        let EvmInstKind::Add(add) = self.resolve(*inst) else {
            return false;
        };

        (*add.lhs() == base && self.function.dfg.value_is_imm(*add.rhs()))
            || (*add.rhs() == base && self.function.dfg.value_is_imm(*add.lhs()))
    }

    fn inst_result_uses_are_private_branches(&self, inst: InstId) -> bool {
        let [result] = self.function.dfg.inst_results(inst) else {
            return false;
        };

        for block in self.function.layout.iter_block() {
            for user in self.function.layout.iter_inst(block) {
                if user == inst || !self.inst_uses_value(user, *result) {
                    continue;
                }

                let EvmInstKind::Br(br) = self.resolve(user) else {
                    return false;
                };
                if br.cond() != result {
                    return false;
                }
            }
        }

        true
    }

    fn inst_uses_derived_value(&self, inst: InstId) -> bool {
        self.function
            .dfg
            .inst(inst)
            .collect_values()
            .iter()
            .any(|value| self.derived_values.contains(value))
    }

    fn inst_uses_value(&self, inst: InstId, value: ValueId) -> bool {
        self.function
            .dfg
            .inst(inst)
            .collect_values()
            .contains(&value)
    }

    fn resolve(&self, inst: InstId) -> EvmInstKind<'_> {
        self.isa
            .inst_set()
            .resolve_inst(self.function.dfg.inst(inst))
    }
}

fn malloc_private_uses_are_compatible_with_fixed_base(
    function: &Function,
    isa: &Evm,
    malloc: InstId,
    exact_heap_base: bool,
) -> bool {
    PrivateMallocUseAnalysis::new(function, isa, malloc)
        .analyze_private_address_uses()
        .is_some_and(|info| !info.requires_exact_heap_base || exact_heap_base)
}

fn compute_program_free_ptr_slot_facts(
    module: &Module,
    funcs: &[FuncRef],
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) -> (bool, FxHashMap<FuncRef, bool>) {
    let local_facts: FxHashMap<_, _> = funcs
        .iter()
        .copied()
        .map(|func| {
            let facts = module.func_store.view(func, |function| {
                function_free_ptr_slot_facts(function, &module.ctx, backend, ptr_escape)
            });
            (func, facts)
        })
        .collect();
    let local_writes = local_facts
        .iter()
        .map(|(&func, facts)| (func, facts.writes))
        .collect();

    (
        local_facts.values().any(|facts| facts.touches),
        compute_free_ptr_write_summaries(module, funcs, &local_writes, &backend.isa),
    )
}

fn machine_mem_plan_from_semantic(
    func_plan: &memory_plan::FuncMemPlan,
) -> memory_plan::FuncMemPlan {
    let mut mem_plan = func_plan.clone();
    mem_plan.alloca_loc.clear();
    mem_plan.spill_obj = SecondaryMap::new();
    mem_plan.malloc_future_abs_words.clear();
    mem_plan.transient_mallocs.clear();
    mem_plan.malloc_escape_kinds.clear();
    mem_plan
}

fn backend_spill_reserve_abs_words(
    func_plan: &memory_plan::FuncMemPlan,
    reserve: BackendSpillReserve,
) -> u32 {
    let scratch_end = if reserve.scratch_words == 0 {
        0
    } else {
        func_plan.scratch_words
    };
    let stable_end = match func_plan.stable_mode {
        StableMode::StaticAbs { base_word } if reserve.stable_words != 0 => base_word
            .checked_add(func_plan.stable_words)
            .expect("backend stable reserve end overflow"),
        StableMode::None | StableMode::DynamicFrame | StableMode::StaticAbs { .. } => 0,
    };

    scratch_end.max(stable_end)
}

fn compute_entry_may_have_live_frame(
    module: &Module,
    funcs: &[FuncRef],
    semantic_plan: &memory_plan::ProgramMemoryPlan,
) -> FxHashMap<FuncRef, bool> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let mut entry_may_have_live_frame: FxHashMap<FuncRef, bool> =
        funcs.iter().copied().map(|func| (func, false)).collect();

    let mut changed = true;
    while changed {
        changed = false;
        for &caller in funcs {
            let caller_uses_dynamic_frame = semantic_plan
                .funcs
                .get(&caller)
                .is_some_and(memory_plan::FuncMemPlan::uses_dynamic_frame);
            let caller_live = entry_may_have_live_frame
                .get(&caller)
                .copied()
                .unwrap_or(false);
            if !caller_uses_dynamic_frame && !caller_live {
                continue;
            }

            for &callee in call_graph.callee_of(caller) {
                if funcs_set.contains(&callee)
                    && !entry_may_have_live_frame
                        .get(&callee)
                        .copied()
                        .unwrap_or(false)
                {
                    entry_may_have_live_frame.insert(callee, true);
                    changed = true;
                }
            }
        }
    }

    entry_may_have_live_frame
}

fn malloc_min_base(
    func_plan: &memory_plan::FuncMemPlan,
    global_dyn_base: u32,
    backend_spill_reserve_peak: u32,
    inst: InstId,
) -> u32 {
    let dyn_base_words = global_dyn_base
        .checked_sub(func_plan.arena_base)
        .expect("global dynamic base below arena base")
        / WORD_BYTES;
    let mut future_words = func_plan
        .malloc_future_abs_words
        .get(&inst)
        .copied()
        .unwrap_or(dyn_base_words)
        .max(func_plan.return_escape_caller_abs_words)
        .max(backend_spill_reserve_peak);
    let escape_kinds = func_plan
        .malloc_escape_kinds
        .get(&inst)
        .copied()
        .unwrap_or_default();
    if escape_kinds.has_global_or_unknown() {
        future_words = future_words.max(dyn_base_words.max(backend_spill_reserve_peak));
    }

    func_plan
        .arena_base
        .checked_add(
            WORD_BYTES
                .checked_mul(future_words)
                .expect("malloc minimum base overflow"),
        )
        .expect("malloc minimum base overflow")
}

#[cfg(test)]
mod tests {
    use rustc_hash::{FxHashMap, FxHashSet};
    use sonatina_ir::InstId;

    use super::*;
    use crate::isa::evm::{STATIC_BASE, malloc_plan::MallocEscapeKind};

    fn mem_plan_for_malloc(escape_kinds: MallocEscapeKind) -> memory_plan::FuncMemPlan {
        let malloc = InstId::from_u32(7);
        let mut malloc_future_abs_words = FxHashMap::default();
        malloc_future_abs_words.insert(malloc, 1);
        let mut malloc_escape_kinds = FxHashMap::default();
        malloc_escape_kinds.insert(malloc, escape_kinds);

        memory_plan::FuncMemPlan {
            arena_base: STATIC_BASE,
            scratch_words: 0,
            stable_words: 0,
            stable_mode: memory_plan::StableMode::None,
            entry_abs_words: 0,
            obj_loc: FxHashMap::default(),
            alloca_loc: FxHashMap::default(),
            spill_obj: SecondaryMap::new(),
            call_preserve: FxHashMap::default(),
            malloc_future_abs_words,
            transient_mallocs: FxHashSet::default(),
            malloc_escape_kinds,
            return_escape_caller_abs_words: 10,
        }
    }

    #[test]
    fn local_malloc_honors_caller_clamp() {
        let malloc = InstId::from_u32(7);
        let min_base = malloc_min_base(
            &mem_plan_for_malloc(MallocEscapeKind::default()),
            STATIC_BASE + WORD_BYTES,
            0,
            malloc,
        );

        assert_eq!(min_base, STATIC_BASE + 10 * WORD_BYTES);
    }

    #[test]
    fn global_or_unknown_escaping_malloc_honors_caller_clamp() {
        let malloc = InstId::from_u32(7);
        let min_base = malloc_min_base(
            &mem_plan_for_malloc(MallocEscapeKind::UNKNOWN),
            STATIC_BASE + WORD_BYTES,
            0,
            malloc,
        );

        assert_eq!(min_base, STATIC_BASE + 10 * WORD_BYTES);
    }

    #[test]
    fn local_malloc_honors_backend_spill_reserve() {
        let malloc = InstId::from_u32(7);
        let min_base = malloc_min_base(
            &mem_plan_for_malloc(MallocEscapeKind::default()),
            STATIC_BASE + WORD_BYTES,
            16,
            malloc,
        );

        assert_eq!(min_base, STATIC_BASE + 16 * WORD_BYTES);
    }
}
