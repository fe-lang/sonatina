mod heap_plan;
mod late_alias;
mod lazy_frame;
mod legalize;
pub use late_alias::canonicalize_alias_value;
pub(crate) use late_alias::normalize_alias_map;
mod malloc_plan;
mod mem_effects;
mod memory_plan;
pub mod opcode;
mod provenance;
mod ptr_escape;
mod scratch_effects;
mod scratch_plan;
pub(crate) mod static_arena_alloc;

use opcode::OpCode;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    cell::RefCell,
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};
use tracing::{debug_span, info_span, trace_span};

use crate::{
    analysis::func_behavior,
    cfg_edit::CleanupMode,
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    liveness::{InstLiveness, Liveness},
    machinst::{
        lower::{FixupUpdate, Lower, LowerBackend, LoweredFunction, SectionLoweringCtx},
        vcode::{Label, SymFixup, SymFixupKind, VCode, VCodeFixup, VCodeInst},
    },
    module_analysis::{CallGraph, SccBuilder},
    optim::{
        aggregate::{
            AggregateCombine, AggregateExpandAbi, AggregateLowerToMemoryLegalize,
            AggregateScalarize, EnumLowerToProduct, LocalObjectArgMap, ObjectLoadStore,
            ObjectLowerToMemory, ObjectReturnOutParam, assert_aggregate_legalized,
            collect_local_object_arg_info_with_effects, compute_object_effect_summaries, shape,
        },
        cfg_cleanup::CfgCleanup,
        dead_arg::{DeadArgElimConfig, run_dead_arg_elim},
        load_store::LoadStoreSolver,
        sccp::SccpSolver,
    },
    stackalloc::{Action, Actions, Allocator, StackifyAlloc, StackifyBuilder},
};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, Immediate, InstId, InstSetExt, Module, Type, U256, ValueId,
    cfg::ControlFlowGraph,
    inst::{control_flow::BranchKind, data::SymbolRef, evm::inst_set::EvmInstKind},
    ir_writer::{FuncWriter, IrWrite},
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
    object::{Directive, ObjectName, SectionName},
    types::{CompoundType, CompoundTypeRef},
};
use sonatina_triple::{EvmVersion, OperatingSystem};

use cranelift_entity::{EntityList, SecondaryMap};
use late_alias::compute_evm_late_aliases;
use lazy_frame::{FrameSite, FrameSummary, LazyFramePlan, compute_frame_summary};
use legalize::legalize_evm_section;
use mem_effects::compute_func_mem_effects;
pub(crate) use memory_plan::STATIC_BASE;
use memory_plan::{
    ArenaCostModel, DYN_SP_SLOT, FREE_PTR_SLOT, FuncMemPlan, ObjLoc, PreserveMode,
    ProgramMemoryPlan, StableMode, WORD_BYTES, compute_abs_clobber_words,
    compute_program_memory_plan, topo_sort_sccs,
};
use ptr_escape::{PtrEscapeSummary, compute_ptr_escape_summaries};
use static_arena_alloc::StackObjId;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum PushWidthPolicy {
    #[default]
    Push4,
    MinimalRelax,
}

#[derive(Clone)]
struct PreparedSection {
    module_ptr: usize,
    object: ObjectName,
    section: SectionName,
    funcs: Vec<FuncRef>,
    fingerprint: u64,
    section_entry: FuncRef,
    plan: ProgramMemoryPlan,
    has_persistent_mallocs: bool,
    has_explicit_free_ptr_writes: bool,
    dyn_sp_plan: DynSpPlan,
    function_entry_jump_targets: FxHashSet<FuncRef>,
    allocs: FxHashMap<FuncRef, StackifyAlloc>,
    block_orders: FxHashMap<FuncRef, Vec<BlockId>>,
}

#[derive(Clone, Default)]
struct DynSpPlan {
    entry_init: bool,
    frontier_init_calls: FxHashMap<FuncRef, FxHashSet<InstId>>,
    checked_frontier_init_calls: FxHashMap<FuncRef, FxHashSet<InstId>>,
    entry_live_frame: FxHashMap<FuncRef, bool>,
    frame_summaries: FxHashMap<FuncRef, FrameSummary>,
}

#[derive(Clone, Default)]
struct FuncDynSpPlan {
    entry_init: bool,
    frontier_init_calls: FxHashSet<InstId>,
    checked_frontier_init_calls: FxHashSet<InstId>,
    entry_live_frame: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FrontierInitKind {
    Always,
    Checked,
}

#[derive(Clone)]
struct PreparedLowering {
    alloc: StackifyAlloc,
    block_order: Vec<BlockId>,
    mem_plan: FuncMemPlan,
    frame_summary: FrameSummary,
    dyn_sp_plan: Option<FuncDynSpPlan>,
    function_entry_jumpdest: bool,
}

fn canonicalize_prepared_funcs(funcs: &[FuncRef]) -> Vec<FuncRef> {
    let mut funcs = funcs.to_vec();
    funcs.sort_unstable_by_key(|func| func.as_u32());
    funcs
}

fn compute_prepared_section_fingerprint(
    module: &Module,
    funcs: &[FuncRef],
    section_ctx: &SectionLoweringCtx<'_>,
) -> u64 {
    let funcs = canonicalize_prepared_funcs(funcs);
    let mut hasher = DefaultHasher::new();
    section_ctx.object.hash(&mut hasher);
    section_ctx.section.hash(&mut hasher);

    if let Some(object) = module.objects.get(section_ctx.object.0.as_str()) {
        let mut bytes = Vec::new();
        object
            .write(&mut bytes, &module.ctx)
            .expect("object fingerprint write failed");
        bytes.hash(&mut hasher);
    }

    for &func in &funcs {
        func.as_u32().hash(&mut hasher);
        let func_text = module.func_store.view(func, |function| {
            FuncWriter::new(func, function).dump_string()
        });
        func_text.hash(&mut hasher);
    }

    hasher.finish()
}

pub struct EvmBackend {
    isa: Evm,
    stackify_reach_depth: u8,
    arena_cost_model: ArenaCostModel,
    enable_late_cleanup_optimizations: bool,
    section_state: RefCell<Option<PreparedSection>>,
    current_mem_plan: RefCell<Option<FuncMemPlan>>,
    current_frame_summary: RefCell<Option<FrameSummary>>,
    current_dyn_sp_plan: RefCell<Option<FuncDynSpPlan>>,
    current_block_aliases: RefCell<Option<FxHashMap<BlockId, BlockId>>>,
}
impl EvmBackend {
    pub fn new(isa: Evm) -> Self {
        let triple = isa.triple();
        assert!(
            matches!(
                triple.operating_system,
                OperatingSystem::Evm(EvmVersion::Osaka)
            ),
            "EvmBackend requires evm-ethereum-osaka (got {triple})"
        );
        Self {
            isa,
            stackify_reach_depth: 16,
            arena_cost_model: ArenaCostModel::default(),
            enable_late_cleanup_optimizations: true,
            section_state: RefCell::new(None),
            current_mem_plan: RefCell::new(None),
            current_frame_summary: RefCell::new(None),
            current_dyn_sp_plan: RefCell::new(None),
            current_block_aliases: RefCell::new(None),
        }
    }

    pub fn with_stackify_reach_depth(mut self, reach_depth: u8) -> Self {
        assert!(
            (1..=16).contains(&reach_depth),
            "stackify reach_depth must be in 1..=16"
        );
        self.stackify_reach_depth = reach_depth;
        self
    }

    pub fn with_late_cleanup_optimizations(mut self, enable: bool) -> Self {
        self.enable_late_cleanup_optimizations = enable;
        self
    }

    pub fn stackify_reach_depth(&self) -> u8 {
        self.stackify_reach_depth
    }

    pub fn compute_stackify_value_aliases(
        &self,
        function: &Function,
        module: &ModuleCtx,
    ) -> SecondaryMap<ValueId, Option<ValueId>> {
        compute_evm_late_aliases(function, module, &self.isa)
            .map()
            .clone()
    }

    pub fn with_arena_cost_model(mut self, model: ArenaCostModel) -> Self {
        self.arena_cost_model = model;
        self
    }

    /// Render a deterministic memory-plan summary for snapshot tests.
    ///
    /// This intentionally includes alloca layout (offset/size + computed address),
    /// so snapshots can assert that alloca reuse is correct across loops/branches.
    pub fn snapshot_mem_plan(&self, module: &Module, funcs: &[FuncRef]) -> String {
        self.snapshot_mem_plan_impl(module, funcs, false)
    }

    pub fn snapshot_mem_plan_detail(&self, module: &Module, funcs: &[FuncRef]) -> String {
        self.snapshot_mem_plan_impl(module, funcs, true)
    }

    fn snapshot_mem_plan_impl(&self, module: &Module, funcs: &[FuncRef], detail: bool) -> String {
        use std::fmt::Write as _;

        let state = self.section_state.borrow();
        let Some(section) = state.as_ref() else {
            return String::new();
        };

        let mut out = String::new();
        writeln!(
            &mut out,
            "evm mem plan: global_dyn_base=0x{:x} static_base=0x{:x} scratch_peak_words={} static_chain_peak_words={}",
            section.plan.global_dyn_base,
            STATIC_BASE,
            section.plan.scratch_peak_words,
            section.plan.static_chain_peak_words
        )
        .expect("mem plan write failed");

        for &func in funcs {
            let Some(func_plan) = section.plan.funcs.get(&func) else {
                continue;
            };

            let name = module.ctx.func_sig(func, |sig| sig.name().to_string());

            let stable = match func_plan.stable_mode {
                StableMode::None => "None".to_string(),
                StableMode::DynamicFrame => "DynamicFrame".to_string(),
                StableMode::StaticAbs { base_word } => {
                    format!(
                        "StaticAbs(base=0x{:x})",
                        STATIC_BASE + (base_word * WORD_BYTES)
                    )
                }
            };
            writeln!(
                &mut out,
                "evm mem plan: {name} scratch_words={} stable_words={} stable_mode={} entry_abs_words={} abs_words_end={}",
                func_plan.scratch_words,
                func_plan.stable_words,
                stable,
                func_plan.entry_abs_words,
                func_plan.abs_words_end(),
            )
            .expect("mem plan write failed");

            let addr_of = |loc: ObjLoc| match loc {
                ObjLoc::ScratchAbs(off) => {
                    let addr_bytes = STATIC_BASE
                        .checked_add(off.checked_mul(WORD_BYTES).expect("address bytes overflow"))
                        .expect("address bytes overflow");
                    format!("0x{addr_bytes:x}")
                }
                ObjLoc::StableAbs(off) => {
                    let base_word = func_plan
                        .stable_base_word()
                        .expect("stable abs object missing stable base");
                    let addr_bytes = STATIC_BASE
                        .checked_add(
                            base_word
                                .checked_add(off)
                                .expect("address words overflow")
                                .checked_mul(WORD_BYTES)
                                .expect("address bytes overflow"),
                        )
                        .expect("address bytes overflow");
                    format!("0x{addr_bytes:x}")
                }
                ObjLoc::StableFrame(off) => {
                    let addr_bytes =
                        frame_slot_sp_relative_bytes(func_plan.frame_size_words(), off);
                    format!("sp-0x{addr_bytes:x}")
                }
                ObjLoc::StackPinned(depth) => format!("stack[{depth}]"),
            };

            if detail {
                let mut call_info: FxHashMap<InstId, FuncRef> = FxHashMap::default();
                module.func_store.view(func, |function| {
                    for block in function.layout.iter_block() {
                        for inst in function.layout.iter_inst(block) {
                            let Some(call) = function.dfg.call_info(inst) else {
                                continue;
                            };
                            call_info.insert(inst, call.callee());
                        }
                    }
                });

                let mut call_preserve: Vec<(InstId, &memory_plan::CallPreservePlan)> = func_plan
                    .call_preserve
                    .iter()
                    .map(|(inst, plan)| (*inst, plan))
                    .collect();
                call_preserve.sort_unstable_by_key(|(inst, _)| inst.as_u32());
                for (inst, plan) in call_preserve {
                    let callee = call_info.get(&inst).copied().unwrap_or_else(|| {
                        panic!(
                            "missing call info for preserve plan at inst {}",
                            inst.as_u32()
                        )
                    });
                    let callee_name = module.ctx.func_sig(callee, |sig| sig.name().to_string());
                    match &plan.mode {
                        PreserveMode::None => {}
                        PreserveMode::ShadowRuns { shadow_obj, runs } => {
                            let save_words: u32 = runs.iter().map(|run| run.len_words).sum();
                            writeln!(
                                &mut out,
                                "  call inst{} callee=%{callee_name} preserve=ShadowRuns shadow_obj={} result_count={} save_words={} runs={runs:?}",
                                inst.as_u32(),
                                shadow_obj.as_u32(),
                                plan.result_count,
                                save_words,
                            )
                            .expect("mem plan write failed");
                        }
                        PreserveMode::TinyStackLift { word_offsets } => {
                            writeln!(
                                &mut out,
                                "  call inst{} callee=%{callee_name} preserve=TinyStackLift result_count={} save_words={} save_offsets={word_offsets:?}",
                                inst.as_u32(),
                                plan.result_count,
                                word_offsets.len(),
                            )
                            .expect("mem plan write failed");
                        }
                    }
                }

                let mut scratch_spills: Vec<(ValueId, u32)> = Vec::new();
                if let Some(alloc) = section.allocs.get(&func) {
                    module.func_store.view(func, |function| {
                        for v in function.dfg.value_ids() {
                            let Some(slot) = alloc.scratch_slot_of_value[v] else {
                                continue;
                            };
                            scratch_spills.push((v, slot));
                        }
                    });
                }

                scratch_spills.sort_unstable_by_key(|(v, _)| v.as_u32());
                for (v, slot) in scratch_spills {
                    let addr_bytes = slot
                        .checked_mul(WORD_BYTES)
                        .expect("scratch slot addr overflow");
                    writeln!(
                        &mut out,
                        "  scratch_spill v{} slot={slot} addr=0x{addr_bytes:x}",
                        v.as_u32()
                    )
                    .expect("mem plan write failed");
                }

                let mut spills: Vec<(ValueId, u32, String)> = Vec::new();
                module.func_store.view(func, |function| {
                    for v in function.dfg.value_ids() {
                        let Some(obj) = func_plan.spill_obj[v] else {
                            continue;
                        };
                        let loc = func_plan
                            .obj_loc
                            .get(&obj)
                            .copied()
                            .expect("missing stack object location");
                        let offset_words = func_plan
                            .obj_word_offset(obj)
                            .expect("missing stack object offset");
                        spills.push((v, offset_words, addr_of(loc)));
                    }
                });

                spills.sort_unstable_by_key(|(v, _, _)| v.as_u32());
                for (v, offset_words, addr) in spills {
                    writeln!(
                        &mut out,
                        "  spill v{} offset_words={offset_words} addr={addr}",
                        v.as_u32()
                    )
                    .expect("mem plan write failed");
                }
            }

            let mut allocas: Vec<(ValueId, u32, u32, String)> = Vec::new();
            module.func_store.view(func, |function| {
                for block in function.layout.iter_block() {
                    for insn in function.layout.iter_inst(block) {
                        let data = self.isa.inst_set().resolve_inst(function.dfg.inst(insn));
                        let EvmInstKind::Alloca(alloca) = data else {
                            continue;
                        };
                        let Some(value) = function.dfg.inst_result(insn) else {
                            continue;
                        };
                        let loc = func_plan
                            .alloca_loc
                            .get(&insn)
                            .copied()
                            .expect("missing alloca plan");
                        let offset_words = match loc {
                            ObjLoc::ScratchAbs(off)
                            | ObjLoc::StableAbs(off)
                            | ObjLoc::StableFrame(off) => off,
                            ObjLoc::StackPinned(depth) => u32::from(depth),
                        };

                        let size_bytes = self
                            .isa
                            .type_layout()
                            .size_of(*alloca.ty(), &module.ctx)
                            .expect("alloca has invalid type")
                            as u32;
                        let size_words = size_bytes.div_ceil(WORD_BYTES);

                        allocas.push((value, offset_words, size_words, addr_of(loc)));
                    }
                }
            });

            if allocas.is_empty() {
                continue;
            }

            allocas.sort_unstable_by_key(|(v, _, _, _)| v.as_u32());
            for (value, offset_words, size_words, addr) in allocas {
                writeln!(
                    &mut out,
                    "  alloca v{} offset_words={offset_words} size_words={size_words} addr={addr}",
                    value.as_u32()
                )
                .expect("mem plan write failed");
            }
        }

        out
    }

    fn prepared_section_matches(
        &self,
        module: &Module,
        funcs: &[FuncRef],
        section_ctx: &SectionLoweringCtx<'_>,
    ) -> bool {
        let Some((module_ptr, object, section, prepared_funcs, fingerprint)) =
            self.section_state.borrow().as_ref().map(|state| {
                (
                    state.module_ptr,
                    state.object.clone(),
                    state.section.clone(),
                    state.funcs.clone(),
                    state.fingerprint,
                )
            })
        else {
            return false;
        };

        module_ptr == module as *const _ as usize
            && object == *section_ctx.object
            && section == *section_ctx.section
            && prepared_funcs == canonicalize_prepared_funcs(funcs)
            && fingerprint
                == compute_prepared_section_fingerprint(module, &prepared_funcs, section_ctx)
    }

    fn prepared_function(
        &self,
        module: &Module,
        func: FuncRef,
        section_ctx: &SectionLoweringCtx<'_>,
    ) -> Option<PreparedLowering> {
        let (module_ptr, object, section, funcs, fingerprint) =
            self.section_state.borrow().as_ref().map(|state| {
                (
                    state.module_ptr,
                    state.object.clone(),
                    state.section.clone(),
                    state.funcs.clone(),
                    state.fingerprint,
                )
            })?;

        if module_ptr != module as *const _ as usize
            || object != *section_ctx.object
            || section != *section_ctx.section
            || !funcs.contains(&func)
            || fingerprint != compute_prepared_section_fingerprint(module, &funcs, section_ctx)
        {
            *self.section_state.borrow_mut() = None;
            return None;
        }

        let state = self.section_state.borrow();
        let section = state.as_ref()?;

        let alloc = section.allocs.get(&func)?.clone();
        let block_order = section.block_orders.get(&func)?.clone();
        let mem_plan = section.plan.funcs.get(&func).cloned()?;
        let frame_summary = section
            .dyn_sp_plan
            .frame_summaries
            .get(&func)
            .cloned()
            .unwrap_or_default();
        let dyn_sp_plan = Some(FuncDynSpPlan {
            entry_init: func == section.section_entry && section.dyn_sp_plan.entry_init,
            frontier_init_calls: section
                .dyn_sp_plan
                .frontier_init_calls
                .get(&func)
                .cloned()
                .unwrap_or_default(),
            checked_frontier_init_calls: section
                .dyn_sp_plan
                .checked_frontier_init_calls
                .get(&func)
                .cloned()
                .unwrap_or_default(),
            entry_live_frame: section
                .dyn_sp_plan
                .entry_live_frame
                .get(&func)
                .copied()
                .unwrap_or(false),
        });

        Some(PreparedLowering {
            alloc,
            block_order,
            mem_plan,
            frame_summary,
            dyn_sp_plan,
            function_entry_jumpdest: section.function_entry_jump_targets.contains(&func),
        })
    }

    fn dyn_base(&self) -> u32 {
        self.section_state
            .borrow()
            .as_ref()
            .map(|s| s.plan.global_dyn_base)
            .unwrap_or(STATIC_BASE)
    }

    fn emit_frame_enter(&self, ctx: &mut Lower<OpCode>, frame_size_slots: u32) {
        if self.current_dyn_sp_plan.borrow().is_some() {
            enter_frame_initialized(ctx, frame_size_slots);
        } else {
            enter_frame_compat(ctx, frame_size_slots, self.dyn_base());
        }
    }

    fn current_lazy_frame_plan_matches(&self, pred: impl FnOnce(&LazyFramePlan) -> bool) -> bool {
        self.current_frame_summary
            .borrow()
            .as_ref()
            .and_then(|summary| summary.lowering.as_ref())
            .is_some_and(pred)
    }

    fn has_current_lazy_frame_lowering(&self) -> bool {
        self.current_frame_summary
            .borrow()
            .as_ref()
            .and_then(|summary| summary.lowering.as_ref())
            .is_some()
    }

    fn current_local_frame_active_before_inst(&self, inst: InstId) -> bool {
        self.current_frame_summary
            .borrow()
            .as_ref()
            .is_some_and(|summary| summary.local_frame_active_before_inst(inst))
    }

    fn current_frontier_init_kind(&self, inst: InstId) -> Option<FrontierInitKind> {
        let plan = self.current_dyn_sp_plan.borrow();
        let plan = plan.as_ref()?;
        if plan.checked_frontier_init_calls.contains(&inst) {
            Some(FrontierInitKind::Checked)
        } else if plan.frontier_init_calls.contains(&inst) {
            Some(FrontierInitKind::Always)
        } else {
            None
        }
    }

    fn current_malloc_needs_dyn_sp_clamp(&self, inst: InstId) -> bool {
        let entry_live_frame = self
            .current_dyn_sp_plan
            .borrow()
            .as_ref()
            .map(|plan| plan.entry_live_frame);
        entry_live_frame
            .map(|entry_live_frame| {
                entry_live_frame || self.current_local_frame_active_before_inst(inst)
            })
            .unwrap_or(true)
    }

    fn canonical_block_target(&self, block: BlockId) -> BlockId {
        self.current_block_aliases
            .borrow()
            .as_ref()
            .and_then(|aliases| aliases.get(&block).copied())
            .unwrap_or(block)
    }

    fn is_elided_block(&self, block: BlockId) -> bool {
        self.current_block_aliases
            .borrow()
            .as_ref()
            .is_some_and(|aliases| aliases.contains_key(&block))
    }

    fn emit_lazy_frame_enter_if_site_matches(
        &self,
        ctx: &mut Lower<OpCode>,
        frame_size_slots: u32,
        site: FrameSite,
    ) {
        if self.current_lazy_frame_plan_matches(|plan| plan.enter_before_site(site)) {
            self.emit_frame_enter(ctx, frame_size_slots);
        }
    }

    fn emit_lazy_frame_leave_if_site_matches(
        &self,
        ctx: &mut Lower<OpCode>,
        frame_size_slots: u32,
        site: FrameSite,
    ) {
        if self.current_lazy_frame_plan_matches(|plan| plan.exit_before_site(site)) {
            leave_frame(ctx, frame_size_slots);
        }
    }

    fn emit_actions_for_site(
        &self,
        ctx: &mut Lower<OpCode>,
        actions: &[Action],
        frame_size_slots: u32,
        site: FrameSite,
    ) {
        self.emit_actions_for_site_from_offset(ctx, actions, frame_size_slots, site, 0);
    }

    fn emit_actions_for_site_from_offset(
        &self,
        ctx: &mut Lower<OpCode>,
        actions: &[Action],
        frame_size_slots: u32,
        site: FrameSite,
        action_index_offset: usize,
    ) {
        self.emit_lazy_frame_enter_if_site_matches(ctx, frame_size_slots, site);

        let folded = fold_stack_actions(actions);
        for (index, action) in folded.iter().copied().enumerate() {
            let index = action_index_offset
                .checked_add(index)
                .expect("lazy frame action index overflow");
            if self.current_lazy_frame_plan_matches(|plan| plan.enter_before_action(site, index)) {
                self.emit_frame_enter(ctx, frame_size_slots);
            }
            if self.current_lazy_frame_plan_matches(|plan| plan.exit_before_action(site, index)) {
                leave_frame(ctx, frame_size_slots);
            }
            perform_action(ctx, action, frame_size_slots);
            if self.current_lazy_frame_plan_matches(|plan| plan.exit_after_action(site, index)) {
                leave_frame(ctx, frame_size_slots);
            }
        }

        if self.current_lazy_frame_plan_matches(|plan| plan.exit_after_site(site)) {
            leave_frame(ctx, frame_size_slots);
        }
    }

    fn section_has_persistent_mallocs(&self) -> bool {
        self.section_state
            .borrow()
            .as_ref()
            .is_none_or(|s| s.has_persistent_mallocs)
    }

    fn section_has_explicit_free_ptr_writes(&self) -> bool {
        self.section_state
            .borrow()
            .as_ref()
            .is_none_or(|s| s.has_explicit_free_ptr_writes)
    }

    fn lower_prepared_function(
        &self,
        module: &Module,
        func: FuncRef,
        prepared: PreparedLowering,
    ) -> Result<LoweredFunction<OpCode>, String> {
        let PreparedLowering {
            alloc,
            block_order,
            mem_plan,
            frame_summary,
            dyn_sp_plan,
            function_entry_jumpdest,
        } = prepared;
        let _span = trace_span!(
            "sonatina.codegen.evm.lower_prepared_function",
            func_ref = func.as_u32(),
            blocks = block_order.len()
        )
        .entered();
        let alias_plan = module.func_store.view(func, |function| {
            compute_late_block_alias_plan(function, &alloc, &frame_summary, &block_order)
        });
        let emitted_block_order = alias_plan.emitted_block_order;
        let block_aliases = alias_plan.aliases;
        module.func_store.view(func, |function| {
            assert_aggregate_legalized(function, &module.ctx);
        });
        let mut vcode = {
            let _span = trace_span!("sonatina.codegen.evm.lower_prepared_function.lower").entered();
            module.func_store.view(func, |function| {
                let _plan_guard =
                    CurrentMemPlanGuard::new(&self.current_mem_plan, mem_plan.clone());
                let _frame_summary_guard = CurrentFrameSummaryGuard::new(
                    &self.current_frame_summary,
                    frame_summary.clone(),
                );
                let _dyn_sp_plan_guard =
                    CurrentDynSpPlanGuard::new(&self.current_dyn_sp_plan, dyn_sp_plan.clone());
                let _block_alias_guard = CurrentBlockAliasesGuard::new(
                    &self.current_block_aliases,
                    block_aliases.clone(),
                );
                let mut alloc = FinalAlloc::new(alloc, mem_plan);
                let lower = Lower::new(&module.ctx, function, &emitted_block_order);
                lower.lower(self, &mut alloc).map_err(|e| format!("{e:?}"))
            })?
        };
        {
            let _span =
                trace_span!("sonatina.codegen.evm.lower_prepared_function.prune_redundant_opcodes")
                    .entered();
            prune_redundant_opcode_sequences(&mut vcode, &emitted_block_order);
        }
        {
            let _span =
                trace_span!("sonatina.codegen.evm.lower_prepared_function.materialize_jumpdests")
                    .entered();
            module.func_store.view(func, |function| {
                materialize_jumpdests(
                    &mut vcode,
                    function,
                    &emitted_block_order,
                    function_entry_jumpdest,
                );
            });
        }

        Ok(LoweredFunction {
            vcode,
            block_order: emitted_block_order,
        })
    }

    fn try_fold_gep_static_arena_addr(
        &self,
        ctx: &Lower<OpCode>,
        args: &[ValueId],
        steps: &[GepStep],
    ) -> Option<u32> {
        let mem_plan = self.current_mem_plan.borrow();
        let mem_plan = mem_plan.as_ref()?;
        let &base = args.first()?;
        let base_addr = self.try_fold_static_arena_addr_value(ctx, mem_plan, base)?;
        let offset = gep_const_offset_bytes(steps)?;
        base_addr.checked_add(offset)
    }

    fn try_fold_static_arena_addr_value(
        &self,
        ctx: &Lower<OpCode>,
        mem_plan: &FuncMemPlan,
        value: ValueId,
    ) -> Option<u32> {
        let inst = ctx.value_def_inst(value)?;
        let data = self.isa.inst_set().resolve_inst(ctx.insn_data(inst));
        match data {
            EvmInstKind::Alloca(_) => {
                let loc = mem_plan.alloca_loc.get(&inst).copied()?;
                obj_loc_abs_addr_bytes(mem_plan, loc)
            }
            EvmInstKind::Bitcast(bitcast) => {
                self.try_fold_static_arena_addr_value(ctx, mem_plan, *bitcast.from())
            }
            EvmInstKind::Gep(gep) => {
                let values = gep.values();
                let &base = values.first()?;
                let base_addr = self.try_fold_static_arena_addr_value(ctx, mem_plan, base)?;
                let steps = build_gep_lower_plan(ctx, values.as_slice()).steps;
                let offset = gep_const_offset_bytes(&steps)?;
                base_addr.checked_add(offset)
            }
            _ => None,
        }
    }
}

fn compute_function_entry_jump_targets(module: &Module, funcs: &[FuncRef]) -> FxHashSet<FuncRef> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let mut targets = FxHashSet::default();
    let evm_inst_set = Evm::new(module.ctx.triple).inst_set();

    for &func_ref in funcs {
        module.func_store.view(func_ref, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    match evm_inst_set.resolve_inst(function.dfg.inst(inst)) {
                        EvmInstKind::Call(call) => {
                            let callee = *call.callee();
                            if funcs_set.contains(&callee) {
                                targets.insert(callee);
                            }
                        }
                        EvmInstKind::GetFunctionPtr(get_fn) => {
                            let func = *get_fn.func();
                            if funcs_set.contains(&func) {
                                targets.insert(func);
                            }
                        }
                        EvmInstKind::SymAddr(sym_addr) => {
                            if let SymbolRef::Func(func) = sym_addr.sym()
                                && funcs_set.contains(func)
                            {
                                targets.insert(*func);
                            }
                        }
                        _ => {}
                    }
                }
            }
        });
    }

    targets
}

fn referenced_insn_label_targets(vcode: &VCode<OpCode>) -> FxHashSet<VCodeInst> {
    let mut targets = FxHashSet::default();
    for (_, fixup) in vcode.fixups.values() {
        let VCodeFixup::Label(label) = fixup else {
            continue;
        };
        if let Label::Insn(inst) = vcode.labels[*label] {
            targets.insert(inst);
        }
    }
    targets
}

fn referenced_block_label_targets(vcode: &VCode<OpCode>) -> FxHashSet<BlockId> {
    let mut targets = FxHashSet::default();
    for (_, fixup) in vcode.fixups.values() {
        let VCodeFixup::Label(label) = fixup else {
            continue;
        };
        if let Label::Block(block) = vcode.labels[*label] {
            targets.insert(block);
        }
    }
    targets
}

fn prepend_block_inst(vcode: &mut VCode<OpCode>, block: BlockId, op: OpCode) -> VCodeInst {
    let inst = vcode.insts.push(op);
    vcode.inst_ir[inst] = None.into();

    let existing: Vec<_> = vcode.block_insns(block).collect();
    let mut list: EntityList<VCodeInst> = Default::default();
    list.push(inst, &mut vcode.insts_pool);
    for inst in existing {
        list.push(inst, &mut vcode.insts_pool);
    }
    vcode.blocks[block] = list;

    inst
}

fn ensure_block_starts_with_jumpdest(vcode: &mut VCode<OpCode>, block: BlockId) {
    if vcode
        .block_insns(block)
        .next()
        .is_some_and(|inst| (vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8))
    {
        return;
    }

    prepend_block_inst(vcode, block, OpCode::JUMPDEST);
}

fn materialize_jumpdests(
    vcode: &mut VCode<OpCode>,
    function: &Function,
    block_order: &[BlockId],
    function_entry_jumpdest: bool,
) {
    let jump_targets = referenced_block_label_targets(vcode);
    let entry = function.layout.entry_block();

    for &block in block_order {
        if jump_targets.contains(&block) || (Some(block) == entry && function_entry_jumpdest) {
            ensure_block_starts_with_jumpdest(vcode, block);
        }
    }
}

#[derive(Default)]
struct LateBlockAliasPlan {
    aliases: FxHashMap<BlockId, BlockId>,
    emitted_block_order: Vec<BlockId>,
}

fn compute_late_block_alias_plan(
    function: &Function,
    alloc: &StackifyAlloc,
    frame_summary: &FrameSummary,
    block_order: &[BlockId],
) -> LateBlockAliasPlan {
    let mut raw_alias_targets: SecondaryMap<BlockId, Option<BlockId>> = SecondaryMap::new();
    let entry = function.layout.entry_block();

    for &block in block_order {
        let Some(term) = block_trampoline_jump_inst(function, block) else {
            continue;
        };

        if Some(block) == entry
            || !alloc.read(term, &[]).is_empty()
            || !alloc.write(term, &[]).is_empty()
            || lazy_frame_mentions_trampoline_site(frame_summary, block, term)
        {
            continue;
        }

        let dest = match function
            .dfg
            .branch_info(term)
            .expect("trampoline jump missing branch info")
            .branch_kind()
        {
            BranchKind::Jump(jump) => *jump.dest(),
            BranchKind::Br(_) | BranchKind::BrTable(_) => unreachable!("non-jump trampoline"),
        };
        raw_alias_targets[block] = Some(dest);
    }

    let mut aliases = FxHashMap::default();
    for &block in block_order {
        if raw_alias_targets[block].is_none() {
            continue;
        }

        let mut seen = FxHashSet::default();
        let mut cur = block;
        let canonical = loop {
            if !seen.insert(cur) {
                break None;
            }

            match raw_alias_targets[cur] {
                Some(next) => cur = next,
                None => break Some(cur),
            }
        };

        if let Some(canonical) = canonical
            && canonical != block
        {
            aliases.insert(block, canonical);
        }
    }

    let emitted_block_order = block_order
        .iter()
        .copied()
        .filter(|block| !aliases.contains_key(block))
        .collect();

    LateBlockAliasPlan {
        aliases,
        emitted_block_order,
    }
}

fn block_trampoline_jump_inst(function: &Function, block: BlockId) -> Option<InstId> {
    let term = function.layout.last_inst_of(block)?;
    if !matches!(
        function.dfg.branch_info(term)?.branch_kind(),
        BranchKind::Jump(_)
    ) {
        return None;
    }
    if function
        .layout
        .iter_inst(block)
        .any(|inst| function.dfg.is_phi(inst))
    {
        return None;
    }
    if function
        .layout
        .iter_inst(block)
        .filter(|&inst| !function.dfg.is_phi(inst))
        .count()
        != 1
    {
        return None;
    }

    Some(term)
}

fn lazy_frame_mentions_trampoline_site(
    frame_summary: &FrameSummary,
    block: BlockId,
    term: InstId,
) -> bool {
    let Some(plan) = frame_summary.lowering.as_ref() else {
        return false;
    };

    [
        FrameSite::BlockEntry(block),
        FrameSite::PreInst(term),
        FrameSite::Inst(term),
        FrameSite::PostInst(term),
    ]
    .into_iter()
    .any(|site| {
        plan.enter_before_site(site) || plan.exit_before_site(site) || plan.exit_after_site(site)
    })
}

fn compute_return_escape_caller_clamp_words(
    module: &Module,
    funcs: &[FuncRef],
    plan: &ProgramMemoryPlan,
) -> FxHashMap<FuncRef, u32> {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let abs_clobber_words = compute_abs_clobber_words(module, funcs, plan);

    let mut callers: FxHashMap<FuncRef, FxHashSet<FuncRef>> = FxHashMap::default();
    let mut clamp_words: FxHashMap<FuncRef, u32> = FxHashMap::default();
    for &func in funcs {
        callers.insert(func, FxHashSet::default());
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
            let Some(func_callers) = callers.get(&func) else {
                continue;
            };

            let mut next = clamp_words.get(&func).copied().unwrap_or(0);
            for caller in func_callers.iter() {
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

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct EntryFrameState {
    maybe_no_live_frame: bool,
    maybe_live_frame: bool,
}

impl EntryFrameState {
    fn no_live() -> Self {
        Self {
            maybe_no_live_frame: true,
            maybe_live_frame: false,
        }
    }

    fn live() -> Self {
        Self {
            maybe_no_live_frame: false,
            maybe_live_frame: true,
        }
    }

    fn is_reachable(self) -> bool {
        self.maybe_no_live_frame || self.maybe_live_frame
    }

    fn merge(&mut self, other: Self) -> bool {
        let next = Self {
            maybe_no_live_frame: self.maybe_no_live_frame || other.maybe_no_live_frame,
            maybe_live_frame: self.maybe_live_frame || other.maybe_live_frame,
        };
        let changed = next != *self;
        *self = next;
        changed
    }
}

fn resolve_section_entry(
    module: &Module,
    section_ctx: &SectionLoweringCtx<'_>,
    funcs: &[FuncRef],
) -> FuncRef {
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let object = module.objects.get(section_ctx.object.0.as_str());

    object
        .and_then(|object| {
            object
                .sections
                .iter()
                .find(|section| section.name == *section_ctx.section)
                .or_else(|| {
                    let mut matches = object.sections.iter().filter(|section| {
                        section.directives.iter().all(|directive| match directive {
                            Directive::Entry(func) | Directive::Include(func) => {
                                funcs_set.contains(func)
                            }
                            Directive::Data(_) | Directive::Embed(_) => true,
                        })
                    });
                    let first = matches.next()?;
                    matches.next().is_none().then_some(first)
                })
        })
        .and_then(|section| {
            section
                .directives
                .iter()
                .find_map(|directive| match directive {
                    Directive::Entry(func) => Some(*func),
                    Directive::Include(_) | Directive::Data(_) | Directive::Embed(_) => None,
                })
        })
        .or_else(|| funcs.first().copied())
        .expect("section must contain an entry function")
}

fn compute_dyn_sp_plan(
    module: &Module,
    funcs: &[FuncRef],
    section_entry: FuncRef,
    plan: &ProgramMemoryPlan,
    analyses: &FxHashMap<FuncRef, memory_plan::FuncAnalysis>,
    isa: &Evm,
) -> DynSpPlan {
    let mut frame_summaries: FxHashMap<FuncRef, FrameSummary> = FxHashMap::default();
    for &func in funcs {
        let analysis = analyses
            .get(&func)
            .unwrap_or_else(|| panic!("missing analysis for func {}", func.as_u32()));
        let mem_plan = plan
            .funcs
            .get(&func)
            .cloned()
            .unwrap_or_else(|| panic!("missing memory plan for func {}", func.as_u32()));
        let summary = module.func_store.view(func, |function| {
            let alloc = FinalAlloc::new(analysis.alloc.clone(), mem_plan.clone());
            compute_frame_summary(function, &alloc, &mem_plan, isa)
        });
        frame_summaries.insert(func, summary);
    }

    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let mut reachable_funcs: FxHashSet<FuncRef> = FxHashSet::default();
    let mut worklist = vec![section_entry];
    while let Some(func) = worklist.pop() {
        if !reachable_funcs.insert(func) {
            continue;
        }
        for &callee in call_graph.callee_of(func) {
            worklist.push(callee);
        }
    }

    let mut ordered_funcs: Vec<FuncRef> = funcs.to_vec();
    ordered_funcs.sort_unstable_by_key(|func| func.as_u32());
    let mut ordered_reachable: Vec<FuncRef> = reachable_funcs.iter().copied().collect();
    ordered_reachable.sort_unstable_by_key(|func| func.as_u32());

    let scc = SccBuilder::new().compute_scc(&call_graph);
    let topo = topo_sort_sccs(&reachable_funcs, &call_graph, &scc);
    let mut ready_sccs: FxHashSet<_> = FxHashSet::default();
    for &scc_ref in &topo {
        if scc
            .scc_info(scc_ref)
            .components
            .iter()
            .copied()
            .filter(|func| reachable_funcs.contains(func))
            .any(|func| {
                plan.funcs
                    .get(&func)
                    .is_some_and(|func_plan| func_plan.frame_size_words() != 0)
            })
        {
            ready_sccs.insert(scc_ref);
        }
    }

    let mut entry_states: FxHashMap<FuncRef, EntryFrameState> = FxHashMap::default();
    entry_states.insert(section_entry, EntryFrameState::no_live());
    let mut changed = true;
    while changed {
        changed = false;
        for &caller in &ordered_reachable {
            let caller_state = entry_states.get(&caller).copied().unwrap_or_default();
            if !caller_state.is_reachable() {
                continue;
            }
            let caller_summary = frame_summaries
                .get(&caller)
                .unwrap_or_else(|| panic!("missing frame summary for func {}", caller.as_u32()));
            module.func_store.view(caller, |function| {
                for block in function.layout.iter_block() {
                    for inst in function.layout.iter_inst(block) {
                        let Some(call) = function.dfg.call_info(inst) else {
                            continue;
                        };
                        let callee = call.callee();
                        if !reachable_funcs.contains(&callee) {
                            continue;
                        }

                        let edge_state = if caller_summary.local_frame_active_before_inst(inst) {
                            EntryFrameState::live()
                        } else {
                            caller_state
                        };
                        changed |= entry_states.entry(callee).or_default().merge(edge_state);
                    }
                }
            });
        }
    }

    let entry_init = ready_sccs.contains(&scc.scc_ref(section_entry));
    let mut frontier_init_calls: FxHashMap<FuncRef, FxHashSet<InstId>> = FxHashMap::default();
    let mut checked_frontier_init_calls: FxHashMap<FuncRef, FxHashSet<InstId>> =
        FxHashMap::default();
    for &caller in &ordered_reachable {
        let caller_scc = scc.scc_ref(caller);
        if ready_sccs.contains(&caller_scc) {
            continue;
        }

        let caller_summary = frame_summaries
            .get(&caller)
            .unwrap_or_else(|| panic!("missing frame summary for func {}", caller.as_u32()));
        let caller_state = entry_states.get(&caller).copied().unwrap_or_default();
        module.func_store.view(caller, |function| {
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let Some(call) = function.dfg.call_info(inst) else {
                        continue;
                    };
                    let callee = call.callee();
                    if !reachable_funcs.contains(&callee) {
                        continue;
                    }
                    let callee_scc = scc.scc_ref(callee);
                    if caller_scc == callee_scc || !ready_sccs.contains(&callee_scc) {
                        continue;
                    }
                    if caller_summary.local_frame_active_before_inst(inst) {
                        continue;
                    }

                    match (
                        caller_state.maybe_no_live_frame,
                        caller_state.maybe_live_frame,
                    ) {
                        (true, false) => {
                            frontier_init_calls.entry(caller).or_default().insert(inst);
                        }
                        (true, true) => {
                            frontier_init_calls.entry(caller).or_default().insert(inst);
                            checked_frontier_init_calls
                                .entry(caller)
                                .or_default()
                                .insert(inst);
                        }
                        (false, true) | (false, false) => {}
                    }
                }
            }
        });
    }

    let mut entry_live_frame: FxHashMap<FuncRef, bool> = FxHashMap::default();
    for func in ordered_funcs {
        let state = entry_states.get(&func).copied().unwrap_or_default();
        entry_live_frame.insert(func, state.maybe_live_frame);
    }

    DynSpPlan {
        entry_init,
        frontier_init_calls,
        checked_frontier_init_calls,
        entry_live_frame,
        frame_summaries,
    }
}

fn is_push_opcode(op: OpCode) -> bool {
    let byte = op as u8;
    byte == OpCode::PUSH0 as u8 || (OpCode::PUSH1 as u8..=OpCode::PUSH32 as u8).contains(&byte)
}

#[derive(Clone, Copy)]
enum StackPeepholeOp {
    Push,
    Dup(u8),
    Swap(u8),
    Pop,
}

fn classify_stack_peephole_op(
    vcode: &VCode<OpCode>,
    label_targets: &FxHashSet<VCodeInst>,
    inst: VCodeInst,
) -> Option<StackPeepholeOp> {
    if label_targets.contains(&inst) || vcode.fixups.get(inst).is_some() {
        return None;
    }
    let op = vcode.insts[inst];
    if is_push_opcode(op) {
        if (op as u8) == (OpCode::PUSH0 as u8) {
            if vcode.inst_imm_bytes.get(inst).is_none() {
                return Some(StackPeepholeOp::Push);
            }
            return None;
        }
        if vcode.inst_imm_bytes.get(inst).is_some() {
            return Some(StackPeepholeOp::Push);
        }
        return None;
    }
    if vcode.inst_imm_bytes.get(inst).is_some() {
        return None;
    }
    let byte = op as u8;
    if byte == OpCode::POP as u8 {
        return Some(StackPeepholeOp::Pop);
    }
    if (OpCode::DUP1 as u8..=OpCode::DUP16 as u8).contains(&byte) {
        return Some(StackPeepholeOp::Dup(byte - OpCode::DUP1 as u8 + 1));
    }
    if (OpCode::SWAP1 as u8..=OpCode::SWAP16 as u8).contains(&byte) {
        return Some(StackPeepholeOp::Swap(byte - OpCode::SWAP1 as u8 + 1));
    }
    None
}

fn is_bool_producer_opcode(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::LT
            | OpCode::GT
            | OpCode::SLT
            | OpCode::SGT
            | OpCode::EQ
            | OpCode::ISZERO
            | OpCode::CALL
            | OpCode::CALLCODE
            | OpCode::DELEGATECALL
            | OpCode::STATICCALL
    )
}

fn is_plain_inst(
    vcode: &VCode<OpCode>,
    label_targets: &FxHashSet<VCodeInst>,
    inst: VCodeInst,
) -> bool {
    !label_targets.contains(&inst)
        && vcode.fixups.get(inst).is_none()
        && vcode.inst_imm_bytes.get(inst).is_none()
}

fn push_immediate_u256(vcode: &VCode<OpCode>, inst: VCodeInst) -> Option<U256> {
    let op = vcode.insts[inst];
    if (op as u8) == (OpCode::PUSH0 as u8) {
        return Some(U256::zero());
    }
    if !is_push_opcode(op) || vcode.fixups.get(inst).is_some() {
        return None;
    }

    let (_, bytes) = vcode.inst_imm_bytes.get(inst)?;
    let mut be = [0u8; 32];
    be[32 - bytes.len()..].copy_from_slice(bytes);
    Some(U256::from_big_endian(&be))
}

fn is_noop_stack_peephole_sequence(
    vcode: &VCode<OpCode>,
    label_targets: &FxHashSet<VCodeInst>,
    insts: &[VCodeInst],
) -> bool {
    let mut stack: SmallVec<[u16; 64]> = (0..32).collect();
    let initial = stack.clone();
    let mut next_push_token: u16 = 1000;

    for &inst in insts {
        let Some(op) = classify_stack_peephole_op(vcode, label_targets, inst) else {
            return false;
        };
        match op {
            StackPeepholeOp::Push => {
                stack.push(next_push_token);
                next_push_token = next_push_token.wrapping_add(1);
            }
            StackPeepholeOp::Dup(depth) => {
                let depth = depth as usize;
                let len = stack.len();
                if len < depth {
                    return false;
                }
                let value = stack[len - depth];
                stack.push(value);
            }
            StackPeepholeOp::Swap(depth) => {
                let depth = depth as usize;
                let len = stack.len();
                if len <= depth {
                    return false;
                }
                stack.swap(len - 1, len - 1 - depth);
            }
            StackPeepholeOp::Pop => {
                if stack.pop().is_none() {
                    return false;
                }
            }
        }
    }

    stack == initial
}

fn prune_redundant_opcode_sequences(vcode: &mut VCode<OpCode>, block_order: &[BlockId]) {
    let label_targets = referenced_insn_label_targets(vcode);

    for block in block_order.iter().copied() {
        let insts: Vec<VCodeInst> = vcode.block_insns(block).collect();
        if insts.len() < 3 {
            continue;
        }

        let mut kept: Vec<VCodeInst> = Vec::with_capacity(insts.len());
        let mut changed = false;
        let mut i = 0usize;
        while i < insts.len() {
            // `iszero; iszero; push <label>; jumpi` can use the original condition directly:
            // JUMPI branches on any non-zero value, so double-negating to canonical {0,1}
            // is redundant in this specific control-flow shape.
            if i + 3 < insts.len() {
                let z0 = insts[i];
                let z1 = insts[i + 1];
                let push = insts[i + 2];
                let jumpi = insts[i + 3];
                if is_plain_inst(vcode, &label_targets, z0)
                    && is_plain_inst(vcode, &label_targets, z1)
                    && is_plain_inst(vcode, &label_targets, jumpi)
                    && (vcode.insts[z0] as u8) == (OpCode::ISZERO as u8)
                    && (vcode.insts[z1] as u8) == (OpCode::ISZERO as u8)
                    && is_push_opcode(vcode.insts[push])
                    && matches!(vcode.fixups.get(push), Some((_, VCodeFixup::Label(_))))
                    && (vcode.insts[jumpi] as u8) == (OpCode::JUMPI as u8)
                {
                    kept.push(push);
                    kept.push(jumpi);
                    changed = true;
                    i += 4;
                    continue;
                }
            }

            // `zext i1 -> i256` lowers to `push 1; and` in EVM codegen.
            // After known bool producers (already in {0,1}), this mask is a no-op.
            if i + 2 < insts.len() {
                let inst = insts[i];
                let push = insts[i + 1];
                let and = insts[i + 2];
                if is_plain_inst(vcode, &label_targets, inst)
                    && is_plain_inst(vcode, &label_targets, and)
                    && is_bool_producer_opcode(vcode.insts[inst])
                    && (vcode.insts[and] as u8) == (OpCode::AND as u8)
                    && push_immediate_u256(vcode, push) == Some(U256::one())
                {
                    kept.push(inst);
                    changed = true;
                    i += 3;
                    continue;
                }
            }

            // Collapse redundant ISZERO chains after known boolean producers.
            //
            // If `op` produces a 0/1 value:
            // - `op; iszero; iszero` is equivalent to `op`
            // - more trailing `iszero`s reduce by parity.
            if i + 2 < insts.len() {
                let inst = insts[i];
                if is_plain_inst(vcode, &label_targets, inst) {
                    let op = vcode.insts[inst];
                    if is_bool_producer_opcode(op) {
                        let mut j = i + 1;
                        while j < insts.len() {
                            let z = insts[j];
                            if label_targets.contains(&z)
                                || vcode.fixups.get(z).is_some()
                                || vcode.inst_imm_bytes.get(z).is_some()
                                || (vcode.insts[z] as u8) != (OpCode::ISZERO as u8)
                            {
                                break;
                            }
                            j += 1;
                        }

                        let run = j - (i + 1);
                        if run >= 2 {
                            kept.push(inst);
                            if run % 2 == 1 {
                                kept.push(insts[i + 1]);
                            }
                            changed = true;
                            i = j;
                            continue;
                        }
                    }
                }
            }

            const MAX_WINDOW: usize = 24;
            let run_limit = (i + MAX_WINDOW).min(insts.len());
            let mut run_end = i;
            while run_end < run_limit
                && classify_stack_peephole_op(vcode, &label_targets, insts[run_end]).is_some()
            {
                run_end += 1;
            }

            let mut removed = false;
            if run_end >= i + 3 {
                for end in (i + 3..=run_end).rev() {
                    if is_noop_stack_peephole_sequence(vcode, &label_targets, &insts[i..end]) {
                        changed = true;
                        removed = true;
                        i = end;
                        break;
                    }
                }
            }
            if removed {
                continue;
            }

            kept.push(insts[i]);
            i += 1;
        }

        if changed {
            let mut list: EntityList<VCodeInst> = Default::default();
            for inst in kept {
                list.push(inst, &mut vcode.insts_pool);
            }
            vcode.blocks[block] = list;
        }
    }
}

struct CurrentMemPlanGuard<'a> {
    slot: &'a RefCell<Option<FuncMemPlan>>,
}

impl<'a> CurrentMemPlanGuard<'a> {
    fn new(slot: &'a RefCell<Option<FuncMemPlan>>, plan: FuncMemPlan) -> Self {
        *slot.borrow_mut() = Some(plan);
        Self { slot }
    }
}

impl Drop for CurrentMemPlanGuard<'_> {
    fn drop(&mut self) {
        *self.slot.borrow_mut() = None;
    }
}

struct CurrentFrameSummaryGuard<'a> {
    slot: &'a RefCell<Option<FrameSummary>>,
}

impl<'a> CurrentFrameSummaryGuard<'a> {
    fn new(slot: &'a RefCell<Option<FrameSummary>>, summary: FrameSummary) -> Self {
        *slot.borrow_mut() = Some(summary);
        Self { slot }
    }
}

impl Drop for CurrentFrameSummaryGuard<'_> {
    fn drop(&mut self) {
        *self.slot.borrow_mut() = None;
    }
}

struct CurrentDynSpPlanGuard<'a> {
    slot: &'a RefCell<Option<FuncDynSpPlan>>,
}

impl<'a> CurrentDynSpPlanGuard<'a> {
    fn new(slot: &'a RefCell<Option<FuncDynSpPlan>>, plan: Option<FuncDynSpPlan>) -> Self {
        *slot.borrow_mut() = plan;
        Self { slot }
    }
}

impl Drop for CurrentDynSpPlanGuard<'_> {
    fn drop(&mut self) {
        *self.slot.borrow_mut() = None;
    }
}

struct CurrentBlockAliasesGuard<'a> {
    slot: &'a RefCell<Option<FxHashMap<BlockId, BlockId>>>,
}

impl<'a> CurrentBlockAliasesGuard<'a> {
    fn new(
        slot: &'a RefCell<Option<FxHashMap<BlockId, BlockId>>>,
        aliases: FxHashMap<BlockId, BlockId>,
    ) -> Self {
        *slot.borrow_mut() = Some(aliases);
        Self { slot }
    }
}

impl Drop for CurrentBlockAliasesGuard<'_> {
    fn drop(&mut self) {
        *self.slot.borrow_mut() = None;
    }
}

fn type_is_legalized_evm(ctx: &ModuleCtx, ty: Type, seen: &mut FxHashSet<CompoundTypeRef>) -> bool {
    match ty {
        Type::I1 | Type::I256 | Type::Unit => true,
        Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 => false,
        Type::EnumTag(_) => false,
        Type::Compound(compound) => {
            if !seen.insert(compound) {
                return true;
            }

            match ctx.with_ty_store(|store| store.resolve_compound(compound).clone()) {
                CompoundType::Array { elem, .. } | CompoundType::Ptr(elem) => {
                    type_is_legalized_evm(ctx, elem, seen)
                }
                CompoundType::ObjRef(_) => false,
                CompoundType::Func { args, ret_tys } => args
                    .iter()
                    .chain(ret_tys.iter())
                    .all(|&ty| type_is_legalized_evm(ctx, ty, seen)),
                CompoundType::Struct(data) => data
                    .fields
                    .iter()
                    .all(|&field| type_is_legalized_evm(ctx, field, seen)),
                CompoundType::Enum(_) => false,
            }
        }
    }
}

fn assert_type_is_legalized_evm(ctx: &ModuleCtx, ty: Type, context: &str) {
    let mut seen = FxHashSet::default();
    assert!(
        type_is_legalized_evm(ctx, ty, &mut seen),
        "{context} must be legalized to the EVM scalar subset, found {ty:?}"
    );
}

fn collect_call_closure(module: &Module, roots: &[FuncRef]) -> Vec<FuncRef> {
    let mut closure = FxHashSet::default();
    let mut worklist = Vec::from(roots);
    let evm_inst_set = Evm::new(module.ctx.triple).inst_set();

    while let Some(func_ref) = worklist.pop() {
        if !module.ctx.declared_funcs.contains_key(&func_ref) || !closure.insert(func_ref) {
            continue;
        }

        if !module.ctx.func_linkage(func_ref).has_definition() {
            continue;
        }

        module.func_store.view(func_ref, |func| {
            for block in func.layout.iter_block() {
                for inst in func.layout.iter_inst(block) {
                    match evm_inst_set.resolve_inst(func.dfg.inst(inst)) {
                        EvmInstKind::Call(call) => worklist.push(*call.callee()),
                        EvmInstKind::GetFunctionPtr(ptr) => worklist.push(*ptr.func()),
                        EvmInstKind::SymAddr(sym) => {
                            if let SymbolRef::Func(sym_func) = sym.sym() {
                                worklist.push(*sym_func);
                            }
                        }
                        EvmInstKind::SymSize(sym) => {
                            if let SymbolRef::Func(sym_func) = sym.sym() {
                                worklist.push(*sym_func);
                            }
                        }
                        _ => {}
                    }
                }
            }
        });
    }

    let mut closure: Vec<_> = closure.into_iter().collect();
    closure.sort_unstable();
    closure
}

fn run_evm_pre_memory_aggregate_pipeline(module: &Module) -> LocalObjectArgMap {
    EnumLowerToProduct.run(module);
    for func_ref in module.funcs() {
        module.func_store.modify(func_ref, |function| {
            AggregateCombine::default().run(function)
        });
    }
    let synthetic_out_args = ObjectReturnOutParam.run_with_synthetic_out_args(module);
    let object_effects = compute_object_effect_summaries(module);
    let mut local_object_args = collect_local_object_arg_info_with_effects(module, &object_effects);
    crate::optim::aggregate::merge_local_object_arg_info(
        &mut local_object_args,
        &synthetic_out_args,
    );
    for func_ref in module.funcs() {
        module.func_store.modify(func_ref, |function| {
            ObjectLoadStore::default().run_for_func(
                func_ref,
                function,
                &local_object_args,
                &object_effects,
            )
        });
    }
    ObjectLowerToMemory.run(module);
    AggregateExpandAbi::default().run(module);
    local_object_args
}

fn run_evm_post_legalize_cleanup(
    module: &Module,
    funcs: &[FuncRef],
    local_object_args: &LocalObjectArgMap,
) {
    for &func in funcs {
        module.func_store.modify(func, |function| {
            CfgCleanup::new(CleanupMode::Strict).run(function);
            AggregateCombine::default().run(function);
            AggregateScalarize::default().run_for_func(func, function, local_object_args);
        });
    }

    run_dead_arg_elim(module, DeadArgElimConfig::default());
    for &func in funcs {
        module.func_store.modify(func, |function| {
            CfgCleanup::new(CleanupMode::Strict).run(function);
        });
    }

    func_behavior::analyze_module(module);
    for &func in funcs {
        module.func_store.modify(func, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            LoadStoreSolver::new().run(function, &mut cfg);
            cfg.compute(function);
            SccpSolver::new().run(function, &mut cfg);
        });
    }
}

fn run_evm_post_memory_legalize_cleanup(module: &Module, funcs: &[FuncRef]) {
    for &func in funcs {
        module.func_store.modify(func, |function| {
            CfgCleanup::new(CleanupMode::Strict).run(function);
        });
    }

    func_behavior::analyze_module(module);
    for &func in funcs {
        module.func_store.modify(func, |function| {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(function);
            LoadStoreSolver::new().run(function, &mut cfg);
            cfg.compute(function);
            SccpSolver::new().run(function, &mut cfg);
        });
    }
}

fn assert_supported_lowering_ir(func_ref: FuncRef, func: &Function) {
    if let Some(sig) = func.ctx().get_sig(func_ref) {
        for &arg in sig.args() {
            assert_type_is_legalized_evm(func.ctx(), arg, "function argument type");
        }
        for &ret in sig.ret_tys() {
            assert_type_is_legalized_evm(func.ctx(), ret, "function return type");
        }
    }

    for &arg in &func.arg_values {
        assert_type_is_legalized_evm(
            func.ctx(),
            func.dfg.value_ty(arg),
            "function argument value",
        );
    }
    for value in func.dfg.value_ids() {
        assert_type_is_legalized_evm(func.ctx(), func.dfg.value_ty(value), "value type");
    }

    let evm_inst_set = Evm::new(func.ctx().triple).inst_set();
    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            match evm_inst_set.resolve_inst(func.dfg.inst(inst)) {
                EvmInstKind::Uaddo(_)
                | EvmInstKind::Uaddsat(_)
                | EvmInstKind::Saddo(_)
                | EvmInstKind::Saddsat(_)
                | EvmInstKind::Usubo(_)
                | EvmInstKind::Usubsat(_)
                | EvmInstKind::Ssubo(_)
                | EvmInstKind::Ssubsat(_)
                | EvmInstKind::Umulo(_)
                | EvmInstKind::Umulsat(_)
                | EvmInstKind::Smulo(_)
                | EvmInstKind::Smulsat(_)
                | EvmInstKind::Snego(_)
                | EvmInstKind::EvmUdivo(_)
                | EvmInstKind::EvmSdivo(_)
                | EvmInstKind::EvmUmodo(_)
                | EvmInstKind::EvmSmodo(_) => {
                    panic!(
                        "multi-result arithmetic must be legalized before EVM lowering: {}",
                        func.dfg.inst(inst).as_text()
                    );
                }
                EvmInstKind::Sdiv(_)
                | EvmInstKind::Udiv(_)
                | EvmInstKind::Umod(_)
                | EvmInstKind::Smod(_) => {
                    panic!(
                        "generic integer div/mod must be legalized to EVM-specific ops before lowering: {}",
                        func.dfg.inst(inst).as_text()
                    );
                }
                EvmInstKind::Sext(_) | EvmInstKind::Zext(_) | EvmInstKind::Trunc(_) => {
                    panic!(
                        "integer casts must be eliminated before EVM lowering: {}",
                        func.dfg.inst(inst).as_text()
                    );
                }
                EvmInstKind::Not(not) if func.dfg.value_ty(*not.arg()) == Type::I1 => {
                    panic!("not on i1 must be legalized before EVM lowering");
                }
                EvmInstKind::Bitcast(bitcast) => {
                    assert_type_is_legalized_evm(func.ctx(), *bitcast.ty(), "bitcast type");
                }
                EvmInstKind::IntToPtr(int_to_ptr) => {
                    assert_type_is_legalized_evm(func.ctx(), *int_to_ptr.ty(), "inttoptr type");
                }
                EvmInstKind::PtrToInt(ptr_to_int) => {
                    assert_type_is_legalized_evm(func.ctx(), *ptr_to_int.ty(), "ptrtoint type");
                }
                EvmInstKind::Mload(mload) => {
                    assert_type_is_legalized_evm(func.ctx(), *mload.ty(), "mload type");
                }
                EvmInstKind::Mstore(mstore) => {
                    assert_type_is_legalized_evm(func.ctx(), *mstore.ty(), "mstore type");
                }
                EvmInstKind::Alloca(alloca) => {
                    assert_type_is_legalized_evm(func.ctx(), *alloca.ty(), "alloca type");
                }
                _ => {}
            }

            let results = func.dfg.inst_results(inst);
            if results.len() <= 1 {
                continue;
            }

            assert!(
                func.dfg.is_call(inst),
                "multi-result instruction `{}` must be legalized before EVM lowering",
                func.dfg.inst(inst).as_text()
            );
            assert!(
                results.len() <= 16,
                "EVM lowering supports at most 16 call results"
            );
            if let Some(call) = func.dfg.call_info(inst)
                && let Some(sig) = func.ctx().get_sig(call.callee())
            {
                assert_eq!(
                    results.len(),
                    sig.ret_tys().len(),
                    "call result count must match callee signature before EVM lowering"
                );
            }
        }
    }
}

impl LowerBackend for EvmBackend {
    type MInst = OpCode;
    type Error = String;
    type FixupPolicy = PushWidthPolicy;

    fn prepare_section(
        &self,
        module: &Module,
        funcs: &[FuncRef],
        section_ctx: &SectionLoweringCtx<'_>,
    ) {
        if self.prepared_section_matches(module, funcs, section_ctx) {
            return;
        }

        let _span =
            info_span!("sonatina.codegen.evm.prepare_section", funcs = funcs.len()).entered();
        let local_object_args = run_evm_pre_memory_aggregate_pipeline(module);
        legalize_evm_section(module, funcs);
        if self.enable_late_cleanup_optimizations {
            run_evm_post_legalize_cleanup(module, funcs, &local_object_args);
        }
        for &func in funcs {
            module.func_store.view(func, |function| {
                assert_supported_lowering_ir(func, function)
            });
        }
        let ptr_escape = {
            let _span = debug_span!("sonatina.codegen.evm.compute_ptr_escape_summaries").entered();
            compute_ptr_escape_summaries(module, funcs, &self.isa)
        };

        // Pre-pass: insert free-ptr restore (conservative: treat all calls as barriers).
        {
            let _span = debug_span!("sonatina.codegen.evm.prepare_free_ptr_restore").entered();
            for &func in funcs {
                let _span = trace_span!(
                    "sonatina.codegen.evm.prepare_free_ptr_restore.func",
                    func_ref = func.as_u32()
                )
                .entered();
                module.func_store.modify(func, |function| {
                    prepare_free_ptr_restore(function, &module.ctx, self, &ptr_escape);
                });
            }
        }

        {
            let _span = debug_span!("sonatina.codegen.evm.aggregate_legalize").entered();
            for &func in funcs {
                let _span = trace_span!(
                    "sonatina.codegen.evm.aggregate_legalize.func",
                    func_ref = func.as_u32()
                )
                .entered();
                module.func_store.modify(func, |function| {
                    AggregateLowerToMemoryLegalize::default().run(function, &module.ctx);
                    assert_aggregate_legalized(function, &module.ctx);
                });
            }
        }
        if self.enable_late_cleanup_optimizations {
            run_evm_post_memory_legalize_cleanup(module, funcs);
        }

        {
            let _span = debug_span!("sonatina.codegen.evm.func_behavior").entered();
            func_behavior::analyze_module(module);
        }

        let (analyses, scratch_effects) =
            compute_scratch_effect_analyses(module, funcs, self, &ptr_escape);

        let mut plan = {
            let _span = debug_span!("sonatina.codegen.evm.compute_program_memory_plan").entered();
            compute_program_memory_plan(
                module,
                funcs,
                &analyses,
                &ptr_escape,
                &self.isa,
                &self.arena_cost_model,
            )
        };

        let mem_effects = {
            let _span = trace_span!("sonatina.codegen.evm.compute_func_mem_effects").entered();
            compute_func_mem_effects(module, funcs, &plan, &scratch_effects, &self.isa)
        };
        let return_escape_caller_abs_words = {
            let _span = trace_span!("sonatina.codegen.evm.compute_return_escape_clamps").entered();
            compute_return_escape_caller_clamp_words(module, funcs, &plan)
        };

        for &func in funcs {
            let _span = trace_span!(
                "sonatina.codegen.evm.annotate_mem_plan_for_func",
                func_ref = func.as_u32()
            )
            .entered();
            let analysis = analyses.get(&func).expect("missing analysis");
            let (malloc_escape_kinds, transient_mallocs) =
                module.func_store.view(func, |function| {
                    let escape_kinds = malloc_plan::compute_malloc_escape_kinds_for_function(
                        function,
                        &module.ctx,
                        &self.isa,
                        &ptr_escape,
                    );
                    let transient = malloc_plan::compute_transient_mallocs(
                        function,
                        &module.ctx,
                        &self.isa,
                        &ptr_escape,
                        Some(&mem_effects),
                        &analysis.inst_liveness,
                    );
                    (escape_kinds, transient)
                });
            if let Some(mem_plan) = plan.funcs.get_mut(&func) {
                mem_plan.malloc_escape_kinds = malloc_escape_kinds;
                mem_plan.return_escape_caller_abs_words = return_escape_caller_abs_words
                    .get(&func)
                    .copied()
                    .unwrap_or(0);
                mem_plan.transient_mallocs = transient_mallocs;
            }
        }

        let malloc_bounds = {
            let _span =
                debug_span!("sonatina.codegen.evm.compute_malloc_future_abs_words").entered();
            heap_plan::compute_malloc_future_abs_words(module, funcs, &plan, &analyses, &self.isa)
        };
        for (func, bounds) in malloc_bounds {
            if let Some(mem_plan) = plan.funcs.get_mut(&func) {
                mem_plan.malloc_future_abs_words = bounds;
            }
        }

        if std::env::var_os("SONATINA_EVM_MEM_DEBUG").is_some() {
            debug_print_mem_plan(module, funcs, &plan);
        }
        let has_persistent_mallocs = {
            let _span = trace_span!("sonatina.codegen.evm.detect_persistent_mallocs").entered();
            funcs.iter().copied().any(|func| {
                let Some(mem_plan) = plan.funcs.get(&func) else {
                    return false;
                };
                module.func_store.view(func, |function| {
                    function.layout.iter_block().any(|block| {
                        function.layout.iter_inst(block).any(|inst| {
                            matches!(
                                self.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                                EvmInstKind::EvmMalloc(_)
                            ) && !mem_plan.transient_mallocs.contains(&inst)
                        })
                    })
                })
            })
        };
        let has_explicit_free_ptr_writes = {
            let _span =
                trace_span!("sonatina.codegen.evm.detect_explicit_free_ptr_writes").entered();
            funcs.iter().copied().any(|func| {
                module.func_store.view(func, |function| {
                    function.layout.iter_block().any(|block| {
                        function.layout.iter_inst(block).any(|inst| {
                            match self.isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
                                EvmInstKind::Mstore(mstore) => function
                                    .dfg
                                    .value_imm(*mstore.addr())
                                    .and_then(immediate_u32)
                                    .is_some_and(|addr| addr == u32::from(FREE_PTR_SLOT)),
                                EvmInstKind::EvmMstore8(mstore8) => function
                                    .dfg
                                    .value_imm(*mstore8.addr())
                                    .and_then(immediate_u32)
                                    .is_some_and(|addr| addr == u32::from(FREE_PTR_SLOT)),
                                _ => false,
                            }
                        })
                    })
                })
            })
        };

        let section_entry = resolve_section_entry(module, section_ctx, funcs);
        let function_entry_jump_targets = {
            let _span =
                trace_span!("sonatina.codegen.evm.compute_function_entry_jump_targets").entered();
            compute_function_entry_jump_targets(module, funcs)
        };
        let dyn_sp_plan = {
            let _span = trace_span!("sonatina.codegen.evm.compute_dyn_sp_plan").entered();
            compute_dyn_sp_plan(module, funcs, section_entry, &plan, &analyses, &self.isa)
        };
        let has_dynamic_frames = plan.funcs.values().any(FuncMemPlan::uses_dynamic_frame);

        let (allocs, block_orders) = {
            let _span = trace_span!("sonatina.codegen.evm.extract_lowering_state").entered();
            let mut allocs: FxHashMap<FuncRef, StackifyAlloc> = FxHashMap::default();
            let mut block_orders: FxHashMap<FuncRef, Vec<BlockId>> = FxHashMap::default();
            for (func, analysis) in analyses {
                allocs.insert(func, analysis.alloc);
                block_orders.insert(func, analysis.block_order);
            }
            (allocs, block_orders)
        };

        {
            let _span = debug_span!(
                "sonatina.codegen.evm.prepare_section_summary",
                has_dynamic_frames,
                has_persistent_mallocs,
                has_explicit_free_ptr_writes
            )
            .entered();
            *self.section_state.borrow_mut() = Some(PreparedSection {
                module_ptr: module as *const _ as usize,
                object: section_ctx.object.clone(),
                section: section_ctx.section.clone(),
                funcs: canonicalize_prepared_funcs(funcs),
                fingerprint: compute_prepared_section_fingerprint(module, funcs, section_ctx),
                section_entry,
                plan,
                has_persistent_mallocs,
                has_explicit_free_ptr_writes,
                dyn_sp_plan,
                function_entry_jump_targets,
                allocs,
                block_orders,
            });
        }
    }

    fn lower_function(
        &self,
        module: &Module,
        func: FuncRef,
        section_ctx: &SectionLoweringCtx<'_>,
    ) -> Result<LoweredFunction<Self::MInst>, Self::Error> {
        let prepared = self.prepared_function(module, func, section_ctx);
        let _span = debug_span!(
            "sonatina.codegen.evm.lower_function",
            func_ref = func.as_u32(),
            prepared_path = prepared.is_some()
        )
        .entered();
        if let Some(prepared) = prepared {
            return self.lower_prepared_function(module, func, prepared);
        }

        let closure = collect_call_closure(module, std::slice::from_ref(&func));
        let local_object_args = run_evm_pre_memory_aggregate_pipeline(module);
        legalize_evm_section(module, &closure);
        if self.enable_late_cleanup_optimizations {
            run_evm_post_legalize_cleanup(module, &closure, &local_object_args);
        }
        module.func_store.view(func, |function| {
            assert_supported_lowering_ir(func, function)
        });

        let ptr_escape = {
            let _span =
                trace_span!("sonatina.codegen.evm.lower_function.compute_ptr_escape").entered();
            compute_ptr_escape_summaries(module, std::slice::from_ref(&func), &self.isa)
        };

        {
            let _span = trace_span!("sonatina.codegen.evm.lower_function.prepare_free_ptr_restore")
                .entered();
            module.func_store.modify(func, |function| {
                prepare_free_ptr_restore(function, &module.ctx, self, &ptr_escape);
            });
        }

        {
            let _span =
                trace_span!("sonatina.codegen.evm.lower_function.aggregate_legalize").entered();
            module.func_store.modify(func, |function| {
                AggregateLowerToMemoryLegalize::default().run(function, &module.ctx);
                assert_aggregate_legalized(function, &module.ctx);
            });
        }
        if self.enable_late_cleanup_optimizations {
            run_evm_post_memory_legalize_cleanup(module, std::slice::from_ref(&func));
        }

        {
            let _span = trace_span!("sonatina.codegen.evm.lower_function.func_behavior").entered();
            func_behavior::analyze_module(module);
        }

        let analysis = {
            let _span =
                trace_span!("sonatina.codegen.evm.lower_function.prepare_stackify_analysis")
                    .entered();
            module.func_store.modify(func, |function| {
                prepare_stackify_analysis(function, &module.ctx, self, &ptr_escape, None)
            })
        };

        let alloc_ctx =
            static_arena_alloc::StaticArenaAllocCtx::new(&module.ctx, &self.isa, &ptr_escape);
        let layout = {
            let _span =
                trace_span!("sonatina.codegen.evm.lower_function.plan_func_objects").entered();
            module.func_store.view(func, |function| {
                alloc_ctx.plan_func_objects(func, function, &analysis)
            })
        };

        let mem_plan = FuncMemPlan {
            scratch_words: 0,
            stable_words: layout.locals_words,
            stable_mode: StableMode::DynamicFrame,
            entry_abs_words: 0,
            obj_loc: layout
                .obj_offset_words
                .into_iter()
                .map(|(id, off)| (id, ObjLoc::StableFrame(off)))
                .collect(),
            alloca_loc: layout
                .alloca_offset_words
                .into_iter()
                .map(|(inst, off)| (inst, ObjLoc::StableFrame(off)))
                .collect(),
            spill_obj: layout.spill_obj,
            call_preserve: FxHashMap::default(),
            malloc_future_abs_words: FxHashMap::default(),
            transient_mallocs: FxHashSet::default(),
            malloc_escape_kinds: FxHashMap::default(),
            return_escape_caller_abs_words: 0,
        };
        let frame_summary = module.func_store.view(func, |function| {
            let alloc = FinalAlloc::new(analysis.alloc.clone(), mem_plan.clone());
            compute_frame_summary(function, &alloc, &mem_plan, &self.isa)
        });
        let lowering = PreparedLowering {
            alloc: analysis.alloc,
            block_order: analysis.block_order,
            mem_plan,
            frame_summary,
            dyn_sp_plan: None,
            function_entry_jumpdest: true,
        };
        self.lower_prepared_function(module, func, lowering)
    }

    fn apply_sym_fixup(
        &self,
        vcode: &mut VCode<Self::MInst>,
        inst: VCodeInst,
        fixup: &SymFixup,
        value: u32,
        policy: &Self::FixupPolicy,
    ) -> Result<FixupUpdate, Self::Error> {
        let _ = fixup;
        let (_, bytes) = vcode
            .inst_imm_bytes
            .get_mut(inst)
            .ok_or_else(|| "missing fixup immediate bytes".to_string())?;

        let new_bytes = u32_to_evm_push_bytes(value, *policy);

        if bytes.as_slice() == new_bytes.as_slice() {
            return Ok(FixupUpdate::Unchanged);
        }

        let layout_changed = bytes.len() != new_bytes.len();
        bytes.clear();
        bytes.extend_from_slice(&new_bytes);

        self.update_opcode_with_immediate_bytes(&mut vcode.insts[inst], bytes);

        Ok(if layout_changed {
            FixupUpdate::LayoutChanged
        } else {
            FixupUpdate::ContentChanged
        })
    }

    fn enter_function(
        &self,
        ctx: &mut Lower<Self::MInst>,
        alloc: &mut dyn Allocator,
        function: &Function,
    ) {
        let frame_size_slots = alloc.frame_size_slots();
        let actions = alloc.enter_function(function);
        if self
            .current_dyn_sp_plan
            .borrow()
            .as_ref()
            .is_some_and(|plan| plan.entry_init)
        {
            init_dyn_sp(ctx, self.dyn_base());
        }

        if self.has_current_lazy_frame_lowering() {
            self.emit_actions_for_site(ctx, &actions, frame_size_slots, FrameSite::EnterFunction);
        } else {
            self.emit_frame_enter(ctx, frame_size_slots);
            crate::isa::evm::perform_actions(ctx, &actions, frame_size_slots);
        }
    }

    fn enter_block(
        &self,
        ctx: &mut Lower<Self::MInst>,
        _alloc: &mut dyn Allocator,
        block: BlockId,
    ) {
        if self.is_elided_block(block) {
            return;
        }

        self.emit_lazy_frame_enter_if_site_matches(
            ctx,
            _alloc.frame_size_slots(),
            FrameSite::BlockEntry(block),
        );
        self.emit_lazy_frame_leave_if_site_matches(
            ctx,
            _alloc.frame_size_slots(),
            FrameSite::BlockEntry(block),
        );
    }

    fn lower(&self, ctx: &mut Lower<Self::MInst>, alloc: &mut dyn Allocator, insn: InstId) {
        if self.is_elided_block(ctx.insn_block(insn)) {
            return;
        }

        let frame_size_slots = alloc.frame_size_slots();
        let emit_pre_actions = |ctx: &mut Lower<Self::MInst>, actions: &[Action]| {
            self.emit_actions_for_site(ctx, actions, frame_size_slots, FrameSite::PreInst(insn))
        };
        let emit_post_actions = |ctx: &mut Lower<Self::MInst>, actions: &[Action]| {
            self.emit_actions_for_site(ctx, actions, frame_size_slots, FrameSite::PostInst(insn))
        };
        let results: SmallVec<[ValueId; 4]> = ctx.insn_results(insn).iter().copied().collect();
        let args = ctx.insn_data(insn).collect_values();
        let data = self.isa.inst_set().resolve_inst(ctx.insn_data(insn));

        let basic_op = |ctx: &mut Lower<Self::MInst>, ops: &[OpCode]| {
            emit_pre_actions(ctx, &alloc.read(insn, &args));
            for op in ops {
                ctx.push(*op);
            }
            emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
        };

        match &data {
            EvmInstKind::Neg(_) => basic_op(ctx, &[OpCode::PUSH0, OpCode::SUB]),
            EvmInstKind::Add(_) => basic_op(ctx, &[OpCode::ADD]),
            EvmInstKind::Uaddo(_)
            | EvmInstKind::Uaddsat(_)
            | EvmInstKind::Saddo(_)
            | EvmInstKind::Saddsat(_)
            | EvmInstKind::Usubo(_)
            | EvmInstKind::Usubsat(_)
            | EvmInstKind::Ssubo(_)
            | EvmInstKind::Ssubsat(_)
            | EvmInstKind::Umulo(_)
            | EvmInstKind::Umulsat(_)
            | EvmInstKind::Smulo(_)
            | EvmInstKind::Smulsat(_)
            | EvmInstKind::Snego(_) => {
                panic!("overflow instructions must be legalized before EVM lowering")
            }
            EvmInstKind::Mul(_) => basic_op(ctx, &[OpCode::MUL]),
            EvmInstKind::Sub(_) => basic_op(ctx, &[OpCode::SUB]),
            EvmInstKind::Sdiv(_)
            | EvmInstKind::Udiv(_)
            | EvmInstKind::Umod(_)
            | EvmInstKind::Smod(_) => {
                panic!("generic integer div/mod must be legalized before EVM lowering")
            }
            EvmInstKind::Shl(_) => basic_op(ctx, &[OpCode::SHL]),
            EvmInstKind::Shr(_) => basic_op(ctx, &[OpCode::SHR]),
            EvmInstKind::Sar(_) => basic_op(ctx, &[OpCode::SAR]),
            EvmInstKind::Sext(_sext) => {
                let from = args[0];
                let src_ty = ctx.value_ty(from);
                let src_bits = scalar_bit_width(src_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));

                if src_bits == 1 {
                    // Canonicalize to low bit first in case the producer left a non-canonical
                    // i1 payload on stack (e.g. raw MLOAD lowering), then materialize
                    // {0, -1} as required by sign-extension semantics.
                    if let Some(mask) = low_bits_mask(src_bits) {
                        let bytes = u256_to_be(&mask);
                        push_bytes(ctx, &bytes);
                        ctx.push(OpCode::AND);
                    }
                    ctx.push(OpCode::PUSH0);
                    ctx.push(OpCode::SUB);
                } else if (8..256).contains(&src_bits) {
                    let src_bytes = (src_bits / 8) as u8;
                    debug_assert!(src_bytes > 0 && src_bytes <= 32);
                    // `SIGNEXTEND` takes (byte_index, value) with `byte_index` at top of stack.
                    push_bytes(ctx, &[src_bytes - 1]);
                    ctx.push(OpCode::SIGNEXTEND);
                }

                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::Zext(_) => {
                let from = args[0];
                let src_ty = ctx.value_ty(from);
                let src_bits = scalar_bit_width(src_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(src_bits) {
                    let bytes = u256_to_be(&mask);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::AND);
                }
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }

            EvmInstKind::Trunc(trunc) => {
                let dst_ty = *trunc.ty();
                let dst_bits = scalar_bit_width(dst_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(dst_bits) {
                    let bytes = u256_to_be(&mask);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::AND);
                }
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::Bitcast(_) => {
                // No-op.
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::IntToPtr(_) => {
                // Pointers are represented as 256-bit integers on the EVM.
                let from = args[0];
                let src_ty = ctx.value_ty(from);
                let src_bits = scalar_bit_width(src_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(src_bits) {
                    let bytes = u256_to_be(&mask);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::AND);
                }
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::PtrToInt(ptr_to_int) => {
                let dst_ty = *ptr_to_int.ty();
                let dst_bits = scalar_bit_width(dst_ty, ctx.module).unwrap_or(256);

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(dst_bits) {
                    let bytes = u256_to_be(&mask);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::AND);
                }
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::Lt(_) => basic_op(ctx, &[OpCode::LT]),
            EvmInstKind::Gt(_) => basic_op(ctx, &[OpCode::GT]),
            EvmInstKind::Slt(_) => basic_op(ctx, &[OpCode::SLT]),
            EvmInstKind::Sgt(_) => basic_op(ctx, &[OpCode::SGT]),
            EvmInstKind::Le(_) => basic_op(ctx, &[OpCode::GT, OpCode::ISZERO]),
            EvmInstKind::Ge(_) => basic_op(ctx, &[OpCode::LT, OpCode::ISZERO]),
            EvmInstKind::Sle(_) => basic_op(ctx, &[OpCode::SGT, OpCode::ISZERO]),
            EvmInstKind::Sge(_) => basic_op(ctx, &[OpCode::SLT, OpCode::ISZERO]),
            EvmInstKind::Eq(_) => basic_op(ctx, &[OpCode::EQ]),
            EvmInstKind::Ne(_) => basic_op(ctx, &[OpCode::EQ, OpCode::ISZERO]),
            EvmInstKind::IsZero(_) => basic_op(ctx, &[OpCode::ISZERO]),

            EvmInstKind::Not(_) => basic_op(ctx, &[OpCode::NOT]),
            EvmInstKind::And(_) => basic_op(ctx, &[OpCode::AND]),
            EvmInstKind::Or(_) => basic_op(ctx, &[OpCode::OR]),
            EvmInstKind::Xor(_) => basic_op(ctx, &[OpCode::XOR]),

            EvmInstKind::Jump(jump) => {
                let dest = self.canonical_block_target(*jump.dest());
                emit_pre_actions(ctx, &alloc.read(insn, &[]));

                if !ctx.is_next_block(dest) {
                    let push_op = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(push_op, Label::Block(dest));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmInstKind::Br(br) => {
                let nz_dest = self.canonical_block_target(*br.nz_dest());
                let z_dest = self.canonical_block_target(*br.z_dest());

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if nz_dest == z_dest {
                    ctx.push(OpCode::POP);
                    if !ctx.is_next_block(nz_dest) {
                        ctx.push_jump_target(OpCode::PUSH1, Label::Block(nz_dest));
                        ctx.push(OpCode::JUMP);
                    }
                } else {
                    // JUMPI: dest is top of stack, bool val is next
                    if ctx.is_next_block(nz_dest) {
                        // Prefer fallthrough to the next block.
                        ctx.push(OpCode::ISZERO);
                        ctx.push_jump_target(OpCode::PUSH1, Label::Block(z_dest));
                        ctx.push(OpCode::JUMPI);
                    } else {
                        ctx.push_jump_target(OpCode::PUSH1, Label::Block(nz_dest));
                        ctx.push(OpCode::JUMPI);

                        if !ctx.is_next_block(z_dest) {
                            ctx.push_jump_target(OpCode::PUSH1, Label::Block(z_dest));
                            ctx.push(OpCode::JUMP);
                        }
                    }
                }
            }
            EvmInstKind::Phi(_) => {}
            EvmInstKind::Unreachable(_) => {
                emit_pre_actions(ctx, &alloc.read(insn, &[]));
                ctx.push(OpCode::INVALID);
            }

            EvmInstKind::BrTable(br) => {
                let table = br.table().clone();
                let scrutinee = *br.scrutinee();
                let default = (*br.default()).map(|dest| self.canonical_block_target(dest));

                // TODO: sanitize br_table ops
                assert!(!table.is_empty(), "empty br_table");
                assert_eq!(
                    table.len(),
                    table.iter().map(|(v, _)| v).collect::<FxHashSet<_>>().len(),
                    "br_table has duplicate scrutinee values"
                );

                for (case_val, dest) in table.iter() {
                    let dest = self.canonical_block_target(*dest);
                    self.emit_actions_for_site(
                        ctx,
                        &alloc.read(insn, &[scrutinee, *case_val]),
                        frame_size_slots,
                        FrameSite::PreInst(insn),
                    );
                    ctx.push(OpCode::EQ);

                    ctx.push_jump_target(OpCode::PUSH1, Label::Block(dest));
                    ctx.push(OpCode::JUMPI);
                }

                if let Some(dest) = default
                    && !ctx.is_next_block(dest)
                {
                    ctx.push_jump_target(OpCode::PUSH1, Label::Block(dest));
                    ctx.push(OpCode::JUMP);
                }
            }

            EvmInstKind::Call(call) => {
                let callee = *call.callee();
                let mut actions = alloc.read(insn, &args);

                let cont_pos = actions
                    .iter()
                    .position(|a| matches!(a, Action::PushContinuationOffset));
                if let Some(cont_pos) = cont_pos {
                    // Some allocators need to run block-entry prologues before pushing the
                    // continuation address for the call. We therefore allow the marker to
                    // appear anywhere in the action list and split around it.
                    let suffix: SmallVec<[Action; 2]> = actions.drain(cont_pos + 1..).collect();
                    let marker = actions.remove(cont_pos);
                    debug_assert_eq!(
                        marker,
                        Action::PushContinuationOffset,
                        "expected continuation marker at split point"
                    );

                    // Prefix actions run before the continuation address is pushed.
                    let prefix_folded_len = fold_stack_actions(&actions).len();
                    self.emit_actions_for_site_from_offset(
                        ctx,
                        &actions,
                        frame_size_slots,
                        FrameSite::PreInst(insn),
                        0,
                    );

                    // Push the return pc / continuation address.
                    let push_callback = ctx.push(OpCode::PUSH1);

                    // Move fn args onto stack
                    self.emit_actions_for_site_from_offset(
                        ctx,
                        &suffix,
                        frame_size_slots,
                        FrameSite::PreInst(insn),
                        prefix_folded_len,
                    );

                    match self.current_frontier_init_kind(insn) {
                        Some(FrontierInitKind::Always) => init_dyn_sp(ctx, self.dyn_base()),
                        Some(FrontierInitKind::Checked) => ensure_dyn_sp_init(ctx, self.dyn_base()),
                        None => {}
                    }

                    // Push fn address onto stack and jump
                    let p = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(p, Label::Function(callee));
                    ctx.push(OpCode::JUMP);

                    // Mark return pc as jumpdest
                    let jumpdest_op = ctx.push(OpCode::JUMPDEST);
                    ctx.add_label_reference(push_callback, Label::Insn(jumpdest_op));

                    // Post-call: spill the call results if needed.
                    emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
                } else {
                    // `noreturn` callees never re-enter the caller, so there is no local
                    // continuation address to materialize or post-call state to restore.
                    self.emit_actions_for_site(
                        ctx,
                        &actions,
                        frame_size_slots,
                        FrameSite::PreInst(insn),
                    );

                    match self.current_frontier_init_kind(insn) {
                        Some(FrontierInitKind::Always) => init_dyn_sp(ctx, self.dyn_base()),
                        Some(FrontierInitKind::Checked) => ensure_dyn_sp_init(ctx, self.dyn_base()),
                        None => {}
                    }

                    let p = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(p, Label::Function(callee));
                    ctx.push(OpCode::JUMP);
                }
            }

            EvmInstKind::Return(_) => {
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if !self.has_current_lazy_frame_lowering() {
                    leave_frame(ctx, alloc.frame_size_slots());
                }

                // Caller pushes return location onto stack prior to call.
                for depth in 1..=args.len() {
                    ctx.push(swap_op(depth as u8));
                }
                ctx.push(OpCode::JUMP);
            }
            EvmInstKind::Mload(_) => basic_op(ctx, &[OpCode::MLOAD]),
            EvmInstKind::Mstore(mstore) => {
                let ty_size = self
                    .isa
                    .type_layout()
                    .size_of(*mstore.ty(), ctx.module)
                    .unwrap();

                emit_pre_actions(ctx, &alloc.read(insn, &args));
                if ty_size == 0 {
                    // TODO: optimize away mstores of size 0
                    // Pop the args, and don't do an mstore.
                    ctx.push(OpCode::POP);
                    ctx.push(OpCode::POP);
                } else {
                    assert!(
                        ty_size == 32,
                        "word-slot model: expected 32-byte store (got {ty_size})"
                    );
                    ctx.push(OpCode::MSTORE);
                }
            }
            EvmInstKind::EvmMcopy(_) => basic_op(ctx, &[OpCode::MCOPY]),
            EvmInstKind::Gep(_) => {
                if args.is_empty() {
                    panic!("gep without operands");
                }

                let gep_plan = build_gep_lower_plan(ctx, &args);
                debug_assert_eq!(
                    gep_plan.runtime_args.len(),
                    1 + gep_plan.runtime_index_count(),
                    "GEP runtime args/step consumption mismatch",
                );

                if let Some(addr_bytes) =
                    self.try_fold_gep_static_arena_addr(ctx, &args, &gep_plan.steps)
                {
                    self.emit_actions_for_site(
                        ctx,
                        &alloc.read(insn, gep_plan.runtime_args.as_slice()),
                        frame_size_slots,
                        FrameSite::PreInst(insn),
                    );
                    for _ in 0..gep_plan.runtime_args.len() {
                        ctx.push(OpCode::POP);
                    }
                    push_bytes(ctx, &u32_to_be(addr_bytes));
                    emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
                    return;
                }

                self.emit_actions_for_site(
                    ctx,
                    &alloc.read(insn, gep_plan.runtime_args.as_slice()),
                    frame_size_slots,
                    FrameSite::PreInst(insn),
                );
                for step in gep_plan.steps {
                    match step {
                        GepStep::AddConst {
                            offset_bytes,
                            consume_index,
                        } => {
                            if consume_index {
                                ctx.push(OpCode::SWAP1);
                                ctx.push(OpCode::POP);
                            }
                            if offset_bytes != 0 {
                                push_bytes(ctx, &u32_to_be(offset_bytes));
                                ctx.push(OpCode::ADD);
                            }
                        }
                        GepStep::AddScaled(scale_bytes) => {
                            ctx.push(OpCode::SWAP1);
                            push_bytes(ctx, &u32_to_be(scale_bytes));
                            ctx.push(OpCode::MUL);
                            ctx.push(OpCode::ADD);
                        }
                    }
                }

                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::Alloca(_) => {
                let mem_plan = self.current_mem_plan.borrow();
                let mem_plan = mem_plan
                    .as_ref()
                    .expect("missing memory plan during lowering");

                let loc = *mem_plan.alloca_loc.get(&insn).expect("missing alloca plan");

                emit_pre_actions(ctx, &alloc.read(insn, &args));

                match loc {
                    ObjLoc::ScratchAbs(_) | ObjLoc::StableAbs(_) => {
                        let addr_bytes =
                            obj_loc_abs_addr_bytes(mem_plan, loc).expect("alloca abs addr missing");
                        push_bytes(ctx, &u32_to_be(addr_bytes));
                    }
                    ObjLoc::StableFrame(offset_words) => {
                        self.emit_lazy_frame_enter_if_site_matches(
                            ctx,
                            frame_size_slots,
                            FrameSite::Inst(insn),
                        );
                        emit_dyn_frame_addr(ctx, frame_size_slots, offset_words);
                        if self.current_lazy_frame_plan_matches(|plan| {
                            plan.exit_after_site(FrameSite::Inst(insn))
                        }) {
                            leave_frame(ctx, frame_size_slots);
                        }
                    }
                    ObjLoc::StackPinned(_) => panic!("stack-pinned allocas are not implemented"),
                }

                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::ObjAlloc(_)
            | EvmInstKind::ObjProj(_)
            | EvmInstKind::ObjIndex(_)
            | EvmInstKind::ObjLoad(_)
            | EvmInstKind::ObjStore(_)
            | EvmInstKind::EnumMake(_)
            | EvmInstKind::EnumTag(_)
            | EvmInstKind::EnumIsVariant(_)
            | EvmInstKind::EnumAssertVariant(_)
            | EvmInstKind::EnumAssertVariantRef(_)
            | EvmInstKind::EnumExtract(_)
            | EvmInstKind::EnumSetTag(_)
            | EvmInstKind::EnumWriteVariant(_)
            | EvmInstKind::EnumGetTag(_)
            | EvmInstKind::EnumProj(_)
            | EvmInstKind::ObjMaterializeStack(_)
            | EvmInstKind::ObjMaterializeHeap(_)
            | EvmInstKind::MemAllocDynamic(_) => {
                panic!(
                    "enum/object lowering invariant violated: high-level enum/object instruction reached EVM lowering"
                )
            }

            EvmInstKind::EvmStop(_) => basic_op(ctx, &[OpCode::STOP]),

            EvmInstKind::EvmSdiv(_) => basic_op(ctx, &[OpCode::SDIV]),
            EvmInstKind::EvmUdiv(_) => basic_op(ctx, &[OpCode::DIV]),
            EvmInstKind::EvmSdivo(_)
            | EvmInstKind::EvmUdivo(_)
            | EvmInstKind::EvmUmodo(_)
            | EvmInstKind::EvmSmodo(_) => {
                panic!("checked EVM div/mod instructions must be legalized before EVM lowering")
            }
            EvmInstKind::EvmUaddsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_uaddsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating add must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_unsigned_saturating_binary(
                    ctx,
                    OpCode::ADD,
                    bits,
                    low_bits_mask(bits).unwrap(),
                );
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmSaddsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_saddsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating add must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_signed_saturating_binary(ctx, OpCode::ADD, bits);
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmUsubsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_usubsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating sub must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_unsigned_saturating_binary(ctx, OpCode::SUB, bits, U256::zero());
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmSsubsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_ssubsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating sub must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_signed_saturating_binary(ctx, OpCode::SUB, bits);
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmUmulsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_umulsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating mul must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_unsigned_saturating_binary(
                    ctx,
                    OpCode::MUL,
                    bits,
                    low_bits_mask(bits).unwrap(),
                );
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmSmulsat(sat) => {
                let bits = scalar_bit_width(*sat.ty(), ctx.module)
                    .expect("evm_smulsat requires scalar type");
                assert!(
                    bits < 256,
                    "full-width saturating mul must be legalized earlier"
                );
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                emit_narrow_signed_saturating_binary(ctx, OpCode::MUL, bits);
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmUmod(_) => basic_op(ctx, &[OpCode::MOD]),
            EvmInstKind::EvmSmod(_) => basic_op(ctx, &[OpCode::SMOD]),
            EvmInstKind::EvmAddMod(_) => basic_op(ctx, &[OpCode::ADDMOD]),
            EvmInstKind::EvmMulMod(_) => basic_op(ctx, &[OpCode::MULMOD]),
            EvmInstKind::EvmExp(_) => basic_op(ctx, &[OpCode::EXP]),
            EvmInstKind::EvmByte(_) => basic_op(ctx, &[OpCode::BYTE]),
            EvmInstKind::EvmClz(_) => basic_op(ctx, &[OpCode::CLZ]),
            EvmInstKind::EvmKeccak256(_) => basic_op(ctx, &[OpCode::KECCAK256]),
            EvmInstKind::EvmAddress(_) => basic_op(ctx, &[OpCode::ADDRESS]),
            EvmInstKind::EvmBalance(_) => basic_op(ctx, &[OpCode::BALANCE]),
            EvmInstKind::EvmOrigin(_) => basic_op(ctx, &[OpCode::ORIGIN]),
            EvmInstKind::EvmCaller(_) => basic_op(ctx, &[OpCode::CALLER]),
            EvmInstKind::EvmCallValue(_) => basic_op(ctx, &[OpCode::CALLVALUE]),
            EvmInstKind::EvmCalldataLoad(_) => basic_op(ctx, &[OpCode::CALLDATALOAD]),
            EvmInstKind::EvmCalldataCopy(_) => basic_op(ctx, &[OpCode::CALLDATACOPY]),
            EvmInstKind::EvmCalldataSize(_) => basic_op(ctx, &[OpCode::CALLDATASIZE]),
            EvmInstKind::EvmCodeSize(_) => basic_op(ctx, &[OpCode::CODESIZE]),
            EvmInstKind::EvmCodeCopy(_) => basic_op(ctx, &[OpCode::CODECOPY]),
            EvmInstKind::EvmExtCodeCopy(_) => basic_op(ctx, &[OpCode::EXTCODECOPY]),
            EvmInstKind::EvmReturnDataSize(_) => basic_op(ctx, &[OpCode::RETURNDATASIZE]),
            EvmInstKind::EvmReturnDataCopy(_) => basic_op(ctx, &[OpCode::RETURNDATACOPY]),
            EvmInstKind::EvmExtCodeHash(_) => basic_op(ctx, &[OpCode::EXTCODEHASH]),
            EvmInstKind::EvmBlockHash(_) => basic_op(ctx, &[OpCode::BLOCKHASH]),
            EvmInstKind::EvmCoinBase(_) => basic_op(ctx, &[OpCode::COINBASE]),
            EvmInstKind::EvmTimestamp(_) => basic_op(ctx, &[OpCode::TIMESTAMP]),
            EvmInstKind::EvmNumber(_) => basic_op(ctx, &[OpCode::NUMBER]),
            EvmInstKind::EvmPrevRandao(_) => basic_op(ctx, &[OpCode::PREVRANDAO]),
            EvmInstKind::EvmGasLimit(_) => basic_op(ctx, &[OpCode::GASLIMIT]),
            EvmInstKind::EvmChainId(_) => basic_op(ctx, &[OpCode::CHAINID]),
            EvmInstKind::EvmSelfBalance(_) => basic_op(ctx, &[OpCode::SELFBALANCE]),
            EvmInstKind::EvmBaseFee(_) => basic_op(ctx, &[OpCode::BASEFEE]),
            EvmInstKind::EvmBlobHash(_) => basic_op(ctx, &[OpCode::BLOBHASH]),
            EvmInstKind::EvmBlobBaseFee(_) => basic_op(ctx, &[OpCode::BLOBBASEFEE]),
            EvmInstKind::EvmMstore8(_) => basic_op(ctx, &[OpCode::MSTORE8]),
            EvmInstKind::EvmSload(_) => basic_op(ctx, &[OpCode::SLOAD]),
            EvmInstKind::EvmSstore(_) => basic_op(ctx, &[OpCode::SSTORE]),
            EvmInstKind::EvmMsize(_) => basic_op(ctx, &[OpCode::MSIZE]),
            EvmInstKind::EvmGas(_) => basic_op(ctx, &[OpCode::GAS]),
            EvmInstKind::EvmTload(_) => basic_op(ctx, &[OpCode::TLOAD]),
            EvmInstKind::EvmTstore(_) => basic_op(ctx, &[OpCode::TSTORE]),
            EvmInstKind::EvmLog0(_) => basic_op(ctx, &[OpCode::LOG0]),
            EvmInstKind::EvmLog1(_) => basic_op(ctx, &[OpCode::LOG1]),
            EvmInstKind::EvmLog2(_) => basic_op(ctx, &[OpCode::LOG2]),
            EvmInstKind::EvmLog3(_) => basic_op(ctx, &[OpCode::LOG3]),
            EvmInstKind::EvmLog4(_) => basic_op(ctx, &[OpCode::LOG4]),
            EvmInstKind::EvmCreate(_) => basic_op(ctx, &[OpCode::CREATE]),
            EvmInstKind::EvmCall(_) => basic_op(ctx, &[OpCode::CALL]),
            EvmInstKind::EvmCallCode(_) => basic_op(ctx, &[OpCode::CALLCODE]),
            EvmInstKind::EvmReturn(_) => basic_op(ctx, &[OpCode::RETURN]),
            EvmInstKind::EvmDelegateCall(_) => basic_op(ctx, &[OpCode::DELEGATECALL]),
            EvmInstKind::EvmCreate2(_) => basic_op(ctx, &[OpCode::CREATE2]),
            EvmInstKind::EvmStaticCall(_) => basic_op(ctx, &[OpCode::STATICCALL]),
            EvmInstKind::EvmRevert(_) => basic_op(ctx, &[OpCode::REVERT]),
            EvmInstKind::EvmSelfDestruct(_) => basic_op(ctx, &[OpCode::SELFDESTRUCT]),
            EvmInstKind::EvmMalloc(_) => {
                let needs_dyn_sp_clamp = self.current_malloc_needs_dyn_sp_clamp(insn);
                let has_persistent_mallocs = self.section_has_persistent_mallocs();
                let has_explicit_free_ptr_writes = self.section_has_explicit_free_ptr_writes();
                let mem_plan = self.current_mem_plan.borrow();
                let mem_plan = mem_plan
                    .as_ref()
                    .expect("missing memory plan during lowering");
                let is_transient = mem_plan.transient_mallocs.contains(&insn);

                let dyn_base_words = self
                    .dyn_base()
                    .checked_sub(STATIC_BASE)
                    .expect("dyn base below static base")
                    / WORD_BYTES;
                let mut future_words = mem_plan
                    .malloc_future_abs_words
                    .get(&insn)
                    .copied()
                    .unwrap_or(dyn_base_words);
                let escape_kinds = mem_plan
                    .malloc_escape_kinds
                    .get(&insn)
                    .copied()
                    .unwrap_or_default();
                if escape_kinds.has_global_or_unknown() {
                    // Non-local/unknown escapes must survive any future caller that can clobber
                    // static arena state up to the section dynamic base.
                    future_words = future_words.max(dyn_base_words);
                } else if escape_kinds.is_return_only() {
                    // Return-only escapes only need to survive the transitive caller-clobber set
                    // of this function, not unrelated functions in the section.
                    future_words = future_words.max(mem_plan.return_escape_caller_abs_words);
                }

                let min_base_bytes = STATIC_BASE
                    .checked_add(
                        WORD_BYTES
                            .checked_mul(future_words)
                            .expect("malloc static bound bytes overflow"),
                    )
                    .expect("malloc static bound bytes overflow");

                let size = *args.first().expect("evm_malloc missing size");
                let aligned_size_imm = ctx.value_imm(size).map(aligned_malloc_size_imm);
                let runtime_args: SmallVec<[ValueId; 1]> = if aligned_size_imm.is_some() {
                    smallvec![]
                } else {
                    smallvec![size]
                };
                self.emit_actions_for_site(
                    ctx,
                    &alloc.read(insn, runtime_args.as_slice()),
                    frame_size_slots,
                    FrameSite::PreInst(insn),
                );

                if is_transient {
                    // Drop the requested size if it was materialized at runtime; transient bump
                    // allocations do not update `FREE_PTR_SLOT` and may overlap later ones.
                    if aligned_size_imm.is_none() {
                        ctx.push(OpCode::POP);
                    }

                    if aligned_size_imm.is_some()
                        && !needs_dyn_sp_clamp
                        && !has_persistent_mallocs
                        && !has_explicit_free_ptr_writes
                    {
                        // In static-only sections without persistent mallocs or explicit free-pointer
                        // writes, a non-escaping immediate-size malloc can use a fixed base directly.
                        push_bytes(ctx, &u32_to_be(min_base_bytes));
                    } else {
                        emit_malloc_base(ctx, min_base_bytes, needs_dyn_sp_clamp);
                    }

                    emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
                    return;
                }

                if aligned_size_imm.is_none() {
                    // Align to 32 bytes:
                    // aligned = (size + 31) & !31
                    push_bytes(ctx, &[0x1f]);
                    ctx.push(OpCode::ADD);
                    push_bytes(ctx, &[0x1f]);
                    ctx.push(OpCode::NOT);
                    ctx.push(OpCode::AND);
                }

                emit_malloc_base(ctx, min_base_bytes, needs_dyn_sp_clamp);

                // new_end = base + aligned_size; mstore(0x40, new_end); return base
                if let Some(aligned) = aligned_size_imm {
                    ctx.push(OpCode::DUP1);
                    if !aligned.is_zero() {
                        push_bytes(ctx, &u256_to_be(&aligned));
                        ctx.push(OpCode::ADD);
                    }
                } else {
                    ctx.push(OpCode::DUP1);
                    ctx.push(OpCode::SWAP2);
                    ctx.push(OpCode::ADD);
                }
                push_bytes(ctx, &[FREE_PTR_SLOT]);
                ctx.push(OpCode::MSTORE);

                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::InsertValue(_) => {
                panic!(
                    "aggregate legalization invariant violated: insert_value reached EVM lowering"
                )
            }
            EvmInstKind::ExtractValue(_) => {
                panic!(
                    "aggregate legalization invariant violated: extract_value reached EVM lowering"
                )
            }
            EvmInstKind::GetFunctionPtr(get_fn) => {
                let func = *get_fn.func();
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                ctx.push_jump_target(OpCode::PUSH1, Label::Function(func));
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::EvmInvalid(_) => basic_op(ctx, &[OpCode::INVALID]),

            EvmInstKind::SymAddr(sym_addr) => {
                let sym = sym_addr.sym().clone();
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                ctx.push_sym_fixup(
                    OpCode::PUSH0,
                    SymFixup {
                        kind: SymFixupKind::Addr,
                        sym,
                    },
                );
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
            EvmInstKind::SymSize(sym_size) => {
                let sym = sym_size.sym().clone();
                emit_pre_actions(ctx, &alloc.read(insn, &args));
                ctx.push_sym_fixup(
                    OpCode::PUSH0,
                    SymFixup {
                        kind: SymFixupKind::Size,
                        sym,
                    },
                );
                emit_post_actions(ctx, &alloc.write(insn, results.as_slice()));
            }
        }
    }

    fn update_opcode_with_immediate_bytes(
        &self,
        opcode: &mut OpCode,
        bytes: &mut SmallVec<[u8; 8]>,
    ) {
        debug_assert!(
            bytes.len() <= 32,
            "PUSH immediate too wide: {} bytes",
            bytes.len()
        );
        *opcode = push_op(bytes.len());
    }

    fn update_opcode_with_label(
        &self,
        opcode: &mut OpCode,
        label_offset: u32,
    ) -> SmallVec<[u8; 4]> {
        let bytes = label_offset
            .to_be_bytes()
            .into_iter()
            .skip_while(|b| *b == 0)
            .collect::<SmallVec<_>>();

        *opcode = push_op(bytes.len());
        bytes
    }

    fn emit_opcode(&self, opcode: &OpCode, buf: &mut Vec<u8>) {
        buf.push(*opcode as u8);
    }

    fn emit_immediate_bytes(&self, bytes: &[u8], buf: &mut Vec<u8>) {
        buf.extend_from_slice(bytes);
    }
    fn emit_label(&self, address: u32, buf: &mut Vec<u8>) {
        buf.extend(address.to_be_bytes().into_iter().skip_while(|b| *b == 0));
    }
}

struct FinalAlloc {
    inner: StackifyAlloc,
    mem_plan: FuncMemPlan,
}

impl FinalAlloc {
    fn new(inner: StackifyAlloc, mem_plan: FuncMemPlan) -> Self {
        Self { inner, mem_plan }
    }

    fn abs_addr_for_word(&self, word_off: u32) -> u32 {
        STATIC_BASE
            .checked_add(
                word_off
                    .checked_mul(WORD_BYTES)
                    .expect("stack object addr bytes overflow"),
            )
            .expect("stack object addr bytes overflow")
    }

    fn obj_loc_for_id(&self, id: StackObjId) -> ObjLoc {
        self.mem_plan
            .obj_loc
            .get(&id)
            .copied()
            .unwrap_or_else(|| panic!("missing stack object location for obj {}", id.as_u32()))
    }

    fn action_load_for_loc(&self, loc: ObjLoc, extra_words: u32) -> Action {
        match loc {
            ObjLoc::ScratchAbs(off) => Action::MemLoadAbs(
                self.abs_addr_for_word(
                    off.checked_add(extra_words)
                        .expect("scratch load offset overflow"),
                ),
            ),
            ObjLoc::StableAbs(off) => {
                let base_word = self
                    .mem_plan
                    .stable_base_word()
                    .expect("stable abs object missing stable base");
                Action::MemLoadAbs(
                    self.abs_addr_for_word(
                        base_word
                            .checked_add(off)
                            .and_then(|w| w.checked_add(extra_words))
                            .expect("stable load offset overflow"),
                    ),
                )
            }
            ObjLoc::StableFrame(off) => Action::MemLoadFrameSlot(
                off.checked_add(extra_words)
                    .expect("frame load offset overflow"),
            ),
            ObjLoc::StackPinned(depth) => {
                panic!("stack-pinned objects are not supported in EVM lowering (depth={depth})")
            }
        }
    }

    fn action_store_for_loc(&self, loc: ObjLoc, extra_words: u32) -> Action {
        match loc {
            ObjLoc::ScratchAbs(off) => Action::MemStoreAbs(
                self.abs_addr_for_word(
                    off.checked_add(extra_words)
                        .expect("scratch store offset overflow"),
                ),
            ),
            ObjLoc::StableAbs(off) => {
                let base_word = self
                    .mem_plan
                    .stable_base_word()
                    .expect("stable abs object missing stable base");
                Action::MemStoreAbs(
                    self.abs_addr_for_word(
                        base_word
                            .checked_add(off)
                            .and_then(|w| w.checked_add(extra_words))
                            .expect("stable store offset overflow"),
                    ),
                )
            }
            ObjLoc::StableFrame(off) => Action::MemStoreFrameSlot(
                off.checked_add(extra_words)
                    .expect("frame store offset overflow"),
            ),
            ObjLoc::StackPinned(depth) => {
                panic!("stack-pinned objects are not supported in EVM lowering (depth={depth})")
            }
        }
    }

    fn inject_call_save_pre(
        &self,
        inst: InstId,
        _operand_count: usize,
        actions: Actions,
    ) -> Actions {
        let Some(plan) = self.mem_plan.call_preserve.get(&inst) else {
            return actions;
        };
        let PreserveMode::ShadowRuns { shadow_obj, runs } = &plan.mode else {
            return actions;
        };
        if runs.is_empty() {
            return actions;
        }

        let Some(cont_pos) = actions
            .iter()
            .position(|a| matches!(a, Action::PushContinuationOffset))
        else {
            panic!("call save expected Action::PushContinuationOffset");
        };
        let shadow_loc = self.obj_loc_for_id(*shadow_obj);

        let mut out = Actions::new();
        for (idx, act) in actions.into_iter().enumerate() {
            if idx == cont_pos {
                for run in runs {
                    for word in 0..run.len_words {
                        out.push(
                            self.action_load_for_loc(
                                ObjLoc::ScratchAbs(run.scratch_src_word),
                                word,
                            ),
                        );
                        out.push(
                            self.action_store_for_loc(
                                shadow_loc,
                                run.shadow_dst_word
                                    .checked_add(word)
                                    .expect("shadow save offset overflow"),
                            ),
                        );
                    }
                }
            }
            out.push(act);
        }
        out
    }

    fn inject_call_save_post(&self, inst: InstId, actions: Actions) -> Actions {
        let Some(plan) = self.mem_plan.call_preserve.get(&inst) else {
            return actions;
        };
        let PreserveMode::ShadowRuns { shadow_obj, runs } = &plan.mode else {
            return actions;
        };
        if runs.is_empty() {
            return actions;
        }

        let mut restore: Actions = Actions::new();
        let shadow_loc = self.obj_loc_for_id(*shadow_obj);
        for run in runs.iter().rev() {
            for word in (0..run.len_words).rev() {
                restore.push(
                    self.action_load_for_loc(
                        shadow_loc,
                        run.shadow_dst_word
                            .checked_add(word)
                            .expect("shadow restore offset overflow"),
                    ),
                );
                restore.push(
                    self.action_store_for_loc(ObjLoc::ScratchAbs(run.scratch_src_word), word),
                );
            }
        }

        let mut out: Actions = Actions::new();
        out.extend(actions);
        out.extend(restore);
        out
    }

    fn rewrite_actions(&self, mut actions: Actions) -> Actions {
        for action in actions.iter_mut() {
            match action {
                Action::MemLoadObj(id) => {
                    *action = self.action_load_for_loc(self.obj_loc_for_id(*id), 0);
                }
                Action::MemStoreObj(id) => {
                    *action = self.action_store_for_loc(self.obj_loc_for_id(*id), 0);
                }
                _ => {}
            }
        }

        actions
    }
}

impl Allocator for FinalAlloc {
    fn enter_function(&self, function: &Function) -> Actions {
        self.rewrite_actions(self.inner.enter_function(function))
    }

    fn frame_size_slots(&self) -> u32 {
        self.mem_plan.frame_size_words()
    }

    fn read(&self, inst: InstId, vals: &[sonatina_ir::ValueId]) -> Actions {
        let actions = self.inner.read(inst, vals);
        let actions = self.inject_call_save_pre(inst, vals.len(), actions);
        self.rewrite_actions(actions)
    }

    fn write(&self, inst: InstId, vals: &[sonatina_ir::ValueId]) -> Actions {
        let actions = self.inner.write(inst, vals);
        let actions = self.inject_call_save_post(inst, actions);
        self.rewrite_actions(actions)
    }

    fn traverse_edge(&self, from: BlockId, to: BlockId) -> Actions {
        self.rewrite_actions(self.inner.traverse_edge(from, to))
    }
}

#[derive(Clone, Copy)]
enum GepStep {
    AddConst {
        offset_bytes: u32,
        consume_index: bool,
    },
    AddScaled(u32),
}

struct GepLowerPlan {
    runtime_args: SmallVec<[ValueId; 8]>,
    steps: Vec<GepStep>,
}

impl GepLowerPlan {
    fn runtime_index_count(&self) -> usize {
        self.steps
            .iter()
            .filter(|step| match step {
                GepStep::AddConst { consume_index, .. } => *consume_index,
                GepStep::AddScaled(_) => true,
            })
            .count()
    }
}

fn build_gep_lower_plan(ctx: &Lower<OpCode>, args: &[ValueId]) -> GepLowerPlan {
    let Some((&base, _indices)) = args.split_first() else {
        panic!("gep without operands");
    };

    let mut current_ty = ctx.value_ty(args[0]);
    if !current_ty.is_pointer(ctx.module) {
        panic!("gep base must be a pointer (got {current_ty:?})");
    }

    let mut runtime_args = SmallVec::<[ValueId; 8]>::new();
    runtime_args.push(base);
    let mut steps: Vec<GepStep> = Vec::new();
    for &idx_val in args.iter().skip(1) {
        let Some(cmpd) = current_ty.resolve_compound(ctx.module) else {
            panic!("invalid gep: indexing into scalar {current_ty:?}");
        };

        let idx_imm_u32 = ctx.value_imm(idx_val).and_then(immediate_u32);

        match cmpd {
            CompoundType::Ptr(elem_ty) => {
                let elem_size = u32::try_from(ctx.module.size_of_unchecked(elem_ty))
                    .expect("gep element too large");
                steps.push(gep_step(elem_size, idx_imm_u32));
                if idx_imm_u32.is_none() {
                    runtime_args.push(idx_val);
                }
                current_ty = elem_ty;
            }
            CompoundType::Array { elem, .. } => {
                let elem_size = u32::try_from(ctx.module.size_of_unchecked(elem))
                    .expect("gep element too large");
                steps.push(gep_step(elem_size, idx_imm_u32));
                if idx_imm_u32.is_none() {
                    runtime_args.push(idx_val);
                }
                current_ty = elem;
            }
            CompoundType::Struct(s) => {
                let Some(idx) = idx_imm_u32.map(|idx| idx as usize) else {
                    panic!("struct gep indices must be immediate constants");
                };
                let (field_offset, field_ty) =
                    shape::struct_field_offset_bytes(&s.fields, s.packed, idx, ctx.module)
                        .unwrap_or_else(|| {
                            panic!("invalid struct gep: packed/unsupported field projection")
                        });
                steps.push(GepStep::AddConst {
                    offset_bytes: field_offset,
                    consume_index: false,
                });
                current_ty = field_ty;
            }
            CompoundType::Func { .. } => {
                panic!("invalid gep: indexing into function type");
            }
            CompoundType::Enum(_) => {
                panic!("invalid gep: indexing into enum type");
            }
            CompoundType::ObjRef(_) => {
                panic!("invalid gep: indexing into object-reference type");
            }
        }
    }

    GepLowerPlan {
        runtime_args,
        steps,
    }
}

fn gep_const_offset_bytes(steps: &[GepStep]) -> Option<u32> {
    let mut total: u32 = 0;
    for &step in steps {
        let GepStep::AddConst { offset_bytes, .. } = step else {
            return None;
        };
        total = total.checked_add(offset_bytes)?;
    }
    Some(total)
}

fn gep_step(elem_size_bytes: u32, idx: Option<u32>) -> GepStep {
    let Some(idx) = idx else {
        return if elem_size_bytes == 0 {
            GepStep::AddConst {
                offset_bytes: 0,
                consume_index: true,
            }
        } else {
            GepStep::AddScaled(elem_size_bytes)
        };
    };

    GepStep::AddConst {
        offset_bytes: elem_size_bytes
            .checked_mul(idx)
            .expect("gep offset overflow"),
        consume_index: false,
    }
}

fn obj_loc_abs_addr_bytes(mem_plan: &FuncMemPlan, loc: ObjLoc) -> Option<u32> {
    mem_plan.abs_addr_for_loc(loc)
}

pub(crate) fn immediate_u32(imm: Immediate) -> Option<u32> {
    if imm.is_negative() {
        return None;
    }

    let u256 = imm.as_i256().to_u256();
    if u256 > U256::from(u32::MAX) {
        return None;
    }

    Some(u256.low_u32())
}

fn aligned_malloc_size_imm(imm: Immediate) -> U256 {
    let size = imm.as_i256().to_u256();
    let (size_padded, _) = size.overflowing_add(U256::from(0x1f_u8));
    size_padded & !U256::from(0x1f_u8)
}

fn fold_stack_actions(actions: &[Action]) -> SmallVec<[Action; 8]> {
    let mut out: SmallVec<[Action; 8]> = SmallVec::new();
    for &action in actions {
        out.push(action);
        loop {
            let len = out.len();

            let mut changed = false;
            if len >= 2 {
                let prev = out[len - 2];
                let last = out[len - 1];
                let cancels = match (prev, last) {
                    // SWAPn is its own inverse.
                    (Action::StackSwap(a), Action::StackSwap(b)) => a == b,
                    (Action::StackDup(_), Action::Pop) | (Action::Push(_), Action::Pop) => true,
                    _ => false,
                };
                if cancels {
                    out.truncate(len - 2);
                    changed = true;
                }
            }

            if !changed && len >= 3 {
                let a = out[len - 3];
                let b = out[len - 2];
                let c = out[len - 1];
                // For any existing top stack word x: PUSH a; SWAP1; POP transforms x -> x.
                if matches!(a, Action::Push(_)) && b == Action::StackSwap(1) && c == Action::Pop {
                    out.truncate(len - 3);
                    changed = true;
                }
            }

            if !changed && len >= 8 {
                let i = len - 8;
                // For any existing top stack word x and immediates a/b:
                // PUSH a; PUSH b; SWAP1; SWAP2; SWAP1; POP; SWAP1; POP transforms x -> x.
                if matches!(out[i], Action::Push(_))
                    && matches!(out[i + 1], Action::Push(_))
                    && out[i + 2] == Action::StackSwap(1)
                    && out[i + 3] == Action::StackSwap(2)
                    && out[i + 4] == Action::StackSwap(1)
                    && out[i + 5] == Action::Pop
                    && out[i + 6] == Action::StackSwap(1)
                    && out[i + 7] == Action::Pop
                {
                    out.truncate(len - 8);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }
    }
    out
}

fn frame_slot_sp_relative_bytes(frame_size_slots: u32, offset_words: u32) -> u32 {
    let sp_relative_words = frame_size_slots
        .checked_sub(offset_words)
        .filter(|words| *words != 0)
        .unwrap_or_else(|| {
            panic!(
                "frame slot offset {} out of range for frame size {}",
                offset_words, frame_size_slots
            )
        });
    sp_relative_words
        .checked_mul(WORD_BYTES)
        .expect("frame slot byte offset overflow")
}

fn emit_dyn_frame_addr(ctx: &mut Lower<OpCode>, frame_size_slots: u32, offset_words: u32) {
    let sp_relative_bytes = frame_slot_sp_relative_bytes(frame_size_slots, offset_words);
    push_bytes(ctx, &u32_to_be(sp_relative_bytes));
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MLOAD);
    ctx.push(OpCode::SUB);
}

fn perform_action(ctx: &mut Lower<OpCode>, action: Action, frame_size_slots: u32) {
    match action {
        Action::StackDup(slot) => {
            debug_assert!(slot < 16, "DUP out of range: {slot}");
            ctx.push(dup_op(slot));
        }
        Action::StackSwap(n) => {
            debug_assert!((1..=16).contains(&n), "SWAP out of range: {n}");
            ctx.push(swap_op(n));
        }
        Action::Push(imm) => {
            if imm.is_zero() {
                ctx.push(OpCode::PUSH0);
            } else {
                let bytes = match imm {
                    Immediate::I1(v) => smallvec![v as u8],
                    Immediate::I8(v) => SmallVec::from_slice(&v.to_be_bytes()),
                    Immediate::I16(v) => shrink_bytes(&v.to_be_bytes()),
                    Immediate::I32(v) => shrink_bytes(&v.to_be_bytes()),
                    Immediate::I64(v) => shrink_bytes(&v.to_be_bytes()),
                    Immediate::I128(v) => shrink_bytes(&v.to_be_bytes()),
                    Immediate::I256(v) => shrink_bytes(&v.to_u256().to_big_endian()),
                    Immediate::EnumTag { value, .. } => {
                        shrink_bytes(&value.to_u256().to_big_endian())
                    }
                };
                push_bytes(ctx, &bytes);

                // Sign-extend negative numbers to 32 bytes
                // TODO: signextend isn't always needed (eg push then mstore8)
                if imm.is_negative() && bytes.len() < 32 {
                    push_bytes(ctx, &u32_to_be((bytes.len() - 1) as u32));
                    ctx.push(OpCode::SIGNEXTEND);
                }
            }
        }
        Action::Pop => {
            ctx.push(OpCode::POP);
        }
        Action::MemLoadAbs(offset) => {
            let bytes = u32_to_be(offset);
            push_bytes(ctx, &bytes);
            ctx.push(OpCode::MLOAD);
        }
        Action::MemLoadFrameSlot(offset) => {
            emit_dyn_frame_addr(ctx, frame_size_slots, offset);
            ctx.push(OpCode::MLOAD);
        }
        Action::MemStoreAbs(offset) => {
            let bytes = u32_to_be(offset);
            push_bytes(ctx, &bytes);
            ctx.push(OpCode::MSTORE);
        }
        Action::MemStoreFrameSlot(offset) => {
            emit_dyn_frame_addr(ctx, frame_size_slots, offset);
            ctx.push(OpCode::MSTORE);
        }
        Action::MemLoadObj(_) | Action::MemStoreObj(_) => {
            // Invariant: stack-object ops must be rewritten by the allocator wrapper
            // (`FinalAlloc`) before lowering.
            panic!("unlowered Mem*Obj action");
        }
        Action::PushContinuationOffset => {
            panic!("handle PushContinuationOffset elsewhere");
        }
    }
}

fn perform_actions(ctx: &mut Lower<OpCode>, actions: &[Action], frame_size_slots: u32) {
    let folded = fold_stack_actions(actions);
    for action in folded {
        perform_action(ctx, action, frame_size_slots);
    }
}

fn push_bytes(ctx: &mut Lower<OpCode>, bytes: &[u8]) {
    assert!(!bytes.is_empty());
    if bytes == [0] {
        ctx.push(OpCode::PUSH0);
    } else {
        ctx.push_with_imm(push_op(bytes.len()), bytes);
    }
}

/// Remove unnecessary leading bytes of the big-endian two's complement
/// representation of a number.
fn shrink_bytes(bytes: &[u8]) -> SmallVec<[u8; 8]> {
    assert!(!bytes.is_empty());

    let is_neg = bytes[0].leading_ones() > 0;
    let skip = if is_neg { 0xff } else { 0x00 };
    let mut bytes = bytes
        .iter()
        .copied()
        .skip_while(|b| *b == skip)
        .collect::<SmallVec<[u8; 8]>>();

    // Negative numbers need a leading 1 bit for sign-extension
    if is_neg && bytes.first().map(|&b| b < 0x80).unwrap_or(true) {
        bytes.insert(0, 0xff);
    }
    bytes
}

fn u32_to_be(num: u32) -> SmallVec<[u8; 4]> {
    if num == 0 {
        smallvec![0]
    } else {
        num.to_be_bytes()
            .into_iter()
            .skip_while(|b| *b == 0)
            .collect()
    }
}

fn u256_to_be(num: &U256) -> SmallVec<[u8; 8]> {
    if num.is_zero() {
        smallvec![0]
    } else {
        let b = num.to_big_endian();
        b.into_iter().skip_while(|b| *b == 0).collect()
    }
}

fn scalar_bit_width(ty: Type, module: &sonatina_ir::module::ModuleCtx) -> Option<u16> {
    let bits = match ty {
        Type::I1 => 1,
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        Type::I128 => 128,
        Type::I256 => 256,
        Type::EnumTag(_) => return None,
        Type::Unit => 0,
        Type::Compound(_) if ty.is_pointer(module) => 256,
        Type::Compound(_) => return None,
    };
    Some(bits)
}

fn low_bits_mask(bits: u16) -> Option<U256> {
    if bits >= 256 {
        None
    } else if bits == 0 {
        Some(U256::zero())
    } else {
        Some((U256::one() << (bits as usize)) - U256::one())
    }
}

fn emit_signextend_top(ctx: &mut Lower<OpCode>, bits: u16) {
    debug_assert!((8..256).contains(&bits) && bits.is_multiple_of(8));
    push_bytes(ctx, &[((bits / 8) - 1) as u8]);
    ctx.push(OpCode::SIGNEXTEND);
}

fn emit_signextend_top_two_operands(ctx: &mut Lower<OpCode>, bits: u16) {
    emit_signextend_top(ctx, bits);
    ctx.push(OpCode::SWAP1);
    emit_signextend_top(ctx, bits);
    ctx.push(OpCode::SWAP1);
}

fn emit_narrow_unsigned_saturating_binary(
    ctx: &mut Lower<OpCode>,
    op: OpCode,
    bits: u16,
    saturated: U256,
) {
    debug_assert!((8..256).contains(&bits));
    let limit = U256::one() << (bits as usize);

    ctx.push(op);
    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &u256_to_be(&limit));
    ctx.push(OpCode::SWAP1);
    ctx.push(OpCode::LT);

    let keep_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    ctx.push(OpCode::POP);
    push_bytes(ctx, &u256_to_be(&saturated));

    let keep = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(keep_push, Label::Insn(keep));
}

fn emit_narrow_signed_saturating_binary(ctx: &mut Lower<OpCode>, op: OpCode, bits: u16) {
    debug_assert!((8..256).contains(&bits) && bits.is_multiple_of(8));
    let limit = U256::one() << (bits as usize);
    let sign = U256::one() << ((bits - 1) as usize);
    let smax = sign - U256::one();

    emit_signextend_top_two_operands(ctx, bits);
    ctx.push(op);
    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &u256_to_be(&sign));
    ctx.push(OpCode::ADD);
    push_bytes(ctx, &u256_to_be(&limit));
    ctx.push(OpCode::SWAP1);
    ctx.push(OpCode::LT);

    let keep_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &[0xff]);
    ctx.push(OpCode::SAR);
    push_bytes(ctx, &u256_to_be(&smax));
    ctx.push(OpCode::XOR);
    ctx.push(OpCode::SWAP1);
    ctx.push(OpCode::POP);

    let keep = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(keep_push, Label::Insn(keep));
}

fn emit_max_top_two(ctx: &mut Lower<OpCode>) {
    // Stack: [..., b, a] (a is top).
    // Result: [..., max(a, b)]
    ctx.push(OpCode::DUP2);
    ctx.push(OpCode::DUP2);
    ctx.push(OpCode::LT);

    let keep_b_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    // a >= b: rotate so common POP keeps `a`.
    ctx.push(OpCode::SWAP1);

    let keep_b = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(keep_b_push, Label::Insn(keep_b));

    // a < b (taken): [b, a] -> POP => [b]
    // a >= b (fallthrough): [b, a] -> SWAP1 => [a, b] -> POP => [a]
    ctx.push(OpCode::POP);
}

fn emit_max_top_with_const(ctx: &mut Lower<OpCode>, constant: &[u8]) {
    // Stack: [..., x]
    // Result: [..., max(x, constant)]
    let constant = U256::from_big_endian(constant);
    if constant.is_zero() {
        return;
    }

    // Use `x > (constant - 1)` so the hot keep path covers equality too.
    let compare_const = u256_to_be(&(constant - U256::from(1_u8)));
    push_bytes(ctx, &compare_const);
    ctx.push(OpCode::DUP2);
    ctx.push(OpCode::GT);

    let keep_x_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    // x < constant: replace x with constant.
    ctx.push(OpCode::POP);
    push_bytes(ctx, &u256_to_be(&constant));

    // x >= constant: keep x.
    let keep_x = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(keep_x_push, Label::Insn(keep_x));
}

fn emit_malloc_base(ctx: &mut Lower<OpCode>, min_base_bytes: u32, needs_dyn_sp_clamp: bool) {
    // heap_end = mload(0x40)
    push_bytes(ctx, &[FREE_PTR_SLOT]);
    ctx.push(OpCode::MLOAD);

    if needs_dyn_sp_clamp {
        // max(heap_end, mload(DYN_SP_SLOT))
        push_bytes(ctx, &[DYN_SP_SLOT]);
        ctx.push(OpCode::MLOAD);
        emit_max_top_two(ctx);
    }

    // max(base, min_base)
    let min_base = u32_to_be(min_base_bytes);
    emit_max_top_with_const(ctx, &min_base);
}

fn init_dyn_sp(ctx: &mut Lower<OpCode>, dyn_base: u32) {
    push_bytes(ctx, &u32_to_be(dyn_base));
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);
}

fn ensure_dyn_sp_init(ctx: &mut Lower<OpCode>, dyn_base: u32) {
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MLOAD);
    ctx.push(OpCode::DUP1);

    let skip_init_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    ctx.push(OpCode::POP);
    push_bytes(ctx, &u32_to_be(dyn_base));
    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);

    let skip_init = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(skip_init_push, Label::Insn(skip_init));
    ctx.push(OpCode::POP);
}

fn enter_frame_initialized(ctx: &mut Lower<OpCode>, frame_slots: u32) {
    if frame_slots == 0 {
        return;
    }

    let frame_bytes = frame_slots
        .checked_mul(WORD_BYTES)
        .expect("frame size overflow");

    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MLOAD);

    // Clamp dynamic stack pointer above any heap allocations.
    push_bytes(ctx, &[FREE_PTR_SLOT]);
    ctx.push(OpCode::MLOAD);
    emit_max_top_two(ctx);

    // new_sp = sp + frame_bytes; mstore(DYN_SP_SLOT, new_sp)
    push_bytes(ctx, &u32_to_be(frame_bytes));
    ctx.push(OpCode::ADD);
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);
}

fn enter_frame_compat(ctx: &mut Lower<OpCode>, frame_slots: u32, dyn_base: u32) {
    if frame_slots == 0 {
        return;
    }

    ensure_dyn_sp_init(ctx, dyn_base);
    enter_frame_initialized(ctx, frame_slots);
}

fn leave_frame(ctx: &mut Lower<OpCode>, frame_slots: u32) {
    if frame_slots == 0 {
        return;
    }

    // new_sp = sp - frame_bytes; mstore(DYN_SP_SLOT, new_sp)
    push_bytes(
        ctx,
        &u32_to_be(
            frame_slots
                .checked_mul(WORD_BYTES)
                .expect("frame size overflow"),
        ),
    );
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MLOAD);
    ctx.push(OpCode::SUB);
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);
}

fn dup_op(n: u8) -> OpCode {
    match n + 1 {
        1 => OpCode::DUP1,
        2 => OpCode::DUP2,
        3 => OpCode::DUP3,
        4 => OpCode::DUP4,
        5 => OpCode::DUP5,
        6 => OpCode::DUP6,
        7 => OpCode::DUP7,
        8 => OpCode::DUP8,
        9 => OpCode::DUP9,
        10 => OpCode::DUP10,
        11 => OpCode::DUP11,
        12 => OpCode::DUP12,
        13 => OpCode::DUP13,
        14 => OpCode::DUP14,
        15 => OpCode::DUP15,
        16 => OpCode::DUP16,
        _ => unreachable!(),
    }
}

fn swap_op(n: u8) -> OpCode {
    match n {
        1 => OpCode::SWAP1,
        2 => OpCode::SWAP2,
        3 => OpCode::SWAP3,
        4 => OpCode::SWAP4,
        5 => OpCode::SWAP5,
        6 => OpCode::SWAP6,
        7 => OpCode::SWAP7,
        8 => OpCode::SWAP8,
        9 => OpCode::SWAP9,
        10 => OpCode::SWAP10,
        11 => OpCode::SWAP11,
        12 => OpCode::SWAP12,
        13 => OpCode::SWAP13,
        14 => OpCode::SWAP14,
        15 => OpCode::SWAP15,
        16 => OpCode::SWAP16,
        _ => unreachable!(),
    }
}

fn push_op(bytes: usize) -> OpCode {
    match bytes {
        0 => OpCode::PUSH0,
        1 => OpCode::PUSH1,
        2 => OpCode::PUSH2,
        3 => OpCode::PUSH3,
        4 => OpCode::PUSH4,
        5 => OpCode::PUSH5,
        6 => OpCode::PUSH6,
        7 => OpCode::PUSH7,
        8 => OpCode::PUSH8,
        9 => OpCode::PUSH9,
        10 => OpCode::PUSH10,
        11 => OpCode::PUSH11,
        12 => OpCode::PUSH12,
        13 => OpCode::PUSH13,
        14 => OpCode::PUSH14,
        15 => OpCode::PUSH15,
        16 => OpCode::PUSH16,
        17 => OpCode::PUSH17,
        18 => OpCode::PUSH18,
        19 => OpCode::PUSH19,
        20 => OpCode::PUSH20,
        21 => OpCode::PUSH21,
        22 => OpCode::PUSH22,
        23 => OpCode::PUSH23,
        24 => OpCode::PUSH24,
        25 => OpCode::PUSH25,
        26 => OpCode::PUSH26,
        27 => OpCode::PUSH27,
        28 => OpCode::PUSH28,
        29 => OpCode::PUSH29,
        30 => OpCode::PUSH30,
        31 => OpCode::PUSH31,
        32 => OpCode::PUSH32,
        _ => unreachable!(),
    }
}

fn prepare_free_ptr_restore(
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

fn prepare_stackify_analysis(
    function: &mut Function,
    module: &ModuleCtx,
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
    scratch_effects: Option<&FxHashSet<FuncRef>>,
) -> memory_plan::FuncAnalysis {
    let _span = trace_span!("sonatina.codegen.evm.prepare_stackify_analysis").entered();
    let mut cfg = ControlFlowGraph::new();
    {
        let _span = trace_span!("sonatina.codegen.evm.stackify.compute_cfg").entered();
        cfg.compute(function);
    }

    {
        let _span = trace_span!("sonatina.codegen.evm.stackify.split_critical_edges").entered();
        let mut splitter = CriticalEdgeSplitter::new();
        splitter.run(function, &mut cfg);
    }

    let (dom, block_order) = {
        let _span = trace_span!("sonatina.codegen.evm.stackify.compute_domtree").entered();
        let mut dom = DomTree::new();
        dom.compute(&cfg);
        let block_order = dom.rpo().to_owned();
        (dom, block_order)
    };

    let inst_liveness = {
        let _span = trace_span!("sonatina.codegen.evm.stackify.compute_liveness").entered();
        let mut liveness = Liveness::new();
        liveness.compute(function, &cfg);

        let mut inst_liveness = InstLiveness::new();
        inst_liveness.compute(function, &cfg, &liveness);
        inst_liveness
    };

    let (value_aliases, stack_liveness, canonical_scratch_live_values) = {
        let _span = trace_span!("sonatina.codegen.evm.stackify.canonicalize_aliases").entered();
        let value_aliases = backend.compute_stackify_value_aliases(function, module);

        let mut stack_liveness = Liveness::new();
        stack_liveness.compute_with_value_normalizer(function, &cfg, |v| {
            canonicalize_alias_value(&value_aliases, v)
        });

        let scratch_live_values = scratch_plan::compute_scratch_live_values(
            function,
            module,
            &backend.isa,
            ptr_escape,
            scratch_effects,
            &inst_liveness,
        );
        let mut canonical_scratch_live_values: crate::bitset::BitSet<ValueId> =
            crate::bitset::BitSet::default();
        for v in scratch_live_values.iter() {
            canonical_scratch_live_values.insert(canonicalize_alias_value(&value_aliases, v));
        }
        (value_aliases, stack_liveness, canonical_scratch_live_values)
    };

    let alloc = {
        let _span = trace_span!("sonatina.codegen.evm.stackify.compute_alloc").entered();
        StackifyBuilder::new(
            function,
            &cfg,
            &dom,
            &stack_liveness,
            backend.stackify_reach_depth,
        )
        .with_scratch_live_values(canonical_scratch_live_values)
        .with_scratch_spills(scratch_plan::SCRATCH_SPILL_SLOTS)
        .with_value_aliases(&value_aliases)
        .compute()
    };

    memory_plan::FuncAnalysis {
        alloc,
        inst_liveness,
        block_order,
        value_aliases,
    }
}

fn compute_scratch_effect_analyses(
    module: &Module,
    funcs: &[FuncRef],
    backend: &EvmBackend,
    ptr_escape: &FxHashMap<FuncRef, PtrEscapeSummary>,
) -> (
    FxHashMap<FuncRef, memory_plan::FuncAnalysis>,
    FxHashSet<FuncRef>,
) {
    let _span = debug_span!("sonatina.codegen.evm.compute_scratch_effect_analyses").entered();
    let funcs_set: FxHashSet<FuncRef> = funcs.iter().copied().collect();
    let call_graph = CallGraph::build_graph_subset(module, &funcs_set);
    let scc = SccBuilder::new().compute_scc(&call_graph);
    let topo = topo_sort_sccs(&funcs_set, &call_graph, &scc);
    let local_scratch_clobbers =
        scratch_effects::compute_local_scratch_clobbers(module, funcs, &backend.isa);

    let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
    let mut scratch_effects: FxHashSet<FuncRef> = FxHashSet::default();

    for &scc_ref in topo.iter().rev() {
        let mut components: Vec<FuncRef> = scc
            .scc_info(scc_ref)
            .components
            .iter()
            .copied()
            .filter(|func| funcs_set.contains(func))
            .collect();
        components.sort_unstable_by_key(|func| func.as_u32());

        // Recursive SCCs are self-referential scratch barriers: if any member uses scratch
        // spills, every intra-SCC call must preserve them. Analyze the SCC under that barrier
        // assumption up front so scratch-spill eligibility remains monotone instead of
        // oscillating between "self-call is a barrier" and "self-call is not a barrier".
        let cycle_scratch_effects = scc.scc_info(scc_ref).is_cycle.then(|| {
            let mut cycle_scratch_effects = scratch_effects.clone();
            cycle_scratch_effects.extend(components.iter().copied());
            cycle_scratch_effects
        });
        let analysis_scratch_effects = cycle_scratch_effects.as_ref().unwrap_or(&scratch_effects);

        let mut scc_uses_scratch_spills = false;
        for func in components.iter().copied() {
            let _span = trace_span!(
                "sonatina.codegen.evm.prepare_stackify_analysis",
                func_ref = func.as_u32()
            )
            .entered();
            let analysis = module.func_store.modify(func, |function| {
                prepare_stackify_analysis(
                    function,
                    &module.ctx,
                    backend,
                    ptr_escape,
                    Some(analysis_scratch_effects),
                )
            });
            scc_uses_scratch_spills |= analysis.alloc.uses_scratch_spills();
            analyses.insert(func, analysis);
        }

        let scc_touches_scratch = scc_uses_scratch_spills
            || components
                .iter()
                .copied()
                .any(|func| local_scratch_clobbers.contains(&func))
            || components.iter().copied().any(|func| {
                call_graph
                    .callee_of(func)
                    .iter()
                    .copied()
                    .any(|callee| scratch_effects.contains(&callee))
            });
        if scc_touches_scratch {
            scratch_effects.extend(components);
        }
    }

    (analyses, scratch_effects)
}

fn debug_print_mem_plan(module: &Module, funcs: &[FuncRef], plan: &ProgramMemoryPlan) {
    let mut funcs_by_name: Vec<(String, FuncRef)> = funcs
        .iter()
        .copied()
        .map(|f| (module.ctx.func_sig(f, |sig| sig.name().to_string()), f))
        .collect();
    funcs_by_name.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));

    eprintln!(
        "evm mem debug: global_dyn_base=0x{:x} static_base=0x{:x} scratch_peak_words={} static_chain_peak_words={}",
        plan.global_dyn_base, STATIC_BASE, plan.scratch_peak_words, plan.static_chain_peak_words
    );
    eprintln!("evm mem debug: entry_mem_init_stores=0");

    for (name, func) in funcs_by_name {
        let Some(func_plan) = plan.funcs.get(&func) else {
            continue;
        };
        let stable_mode = match func_plan.stable_mode {
            StableMode::None => "None".to_string(),
            StableMode::DynamicFrame => "DynamicFrame".to_string(),
            StableMode::StaticAbs { base_word } => {
                format!("StaticAbs(base_word={base_word})")
            }
        };

        let (malloc_min, malloc_max, malloc_count) = if func_plan.malloc_future_abs_words.is_empty()
        {
            (None, None, 0)
        } else {
            let mut min: u32 = u32::MAX;
            let mut max: u32 = 0;
            for &w in func_plan.malloc_future_abs_words.values() {
                min = min.min(w);
                max = max.max(w);
            }
            (
                Some(min),
                Some(max),
                func_plan.malloc_future_abs_words.len(),
            )
        };

        let abs_end_words = func_plan.abs_words_end();
        let abs_end = (abs_end_words != 0).then(|| {
            STATIC_BASE
                .checked_add(
                    abs_end_words
                        .checked_mul(WORD_BYTES)
                        .expect("absolute end overflow"),
                )
                .expect("absolute end overflow")
        });

        eprintln!(
            "evm mem debug: {name} scratch_words={} stable_words={} stable_mode={} entry_abs_words={} abs_words_end={} malloc_bounds(min,max,count)=({:?},{:?},{malloc_count}) abs_end={:?}",
            func_plan.scratch_words,
            func_plan.stable_words,
            stable_mode,
            func_plan.entry_abs_words,
            abs_end_words,
            malloc_min,
            malloc_max,
            abs_end,
        );
    }
}

fn u32_to_evm_push_bytes(value: u32, policy: PushWidthPolicy) -> SmallVec<[u8; 4]> {
    match policy {
        PushWidthPolicy::Push4 => SmallVec::from_slice(&value.to_be_bytes()),
        PushWidthPolicy::MinimalRelax => {
            if value == 0 {
                SmallVec::new()
            } else {
                value
                    .to_be_bytes()
                    .into_iter()
                    .skip_while(|b| *b == 0)
                    .collect()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::func_behavior;
    use sonatina_ir::{
        InstSetBase,
        cfg::ControlFlowGraph,
        object::{EmbedSymbol, ObjectName, SectionName},
    };
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, TargetTriple, Vendor};

    struct PlanTestCtx {
        module: sonatina_ir::Module,
        funcs: Vec<FuncRef>,
        names: FxHashMap<String, FuncRef>,
        plan: ProgramMemoryPlan,
        analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis>,
    }

    struct DynSpTestCtx {
        module: sonatina_ir::Module,
        names: FxHashMap<String, FuncRef>,
        plan: DynSpPlan,
    }

    fn plan_test_ctx_from_src(src: &str) -> PlanTestCtx {
        let parsed = parse_module(src).expect("module parses");
        let funcs = parsed.module.funcs();
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
        for &func in &funcs {
            parsed.module.func_store.modify(func, |function| {
                let mut cfg = ControlFlowGraph::default();
                cfg.compute(function);

                let mut splitter = CriticalEdgeSplitter::new();
                splitter.run(function, &mut cfg);

                let mut liveness = Liveness::new();
                liveness.compute(function, &cfg);

                let mut inst_liveness = InstLiveness::new();
                inst_liveness.compute(function, &cfg, &liveness);

                let mut dom = DomTree::new();
                dom.compute(&cfg);

                analyses.insert(
                    func,
                    memory_plan::FuncAnalysis {
                        alloc: StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute(),
                        inst_liveness,
                        block_order: dom.rpo().to_vec(),
                        value_aliases: {
                            let mut value_aliases = SecondaryMap::new();
                            for value in function.dfg.value_ids() {
                                value_aliases[value] = Some(value);
                            }
                            value_aliases
                        },
                    },
                );
            });
        }

        let plan = compute_program_memory_plan(
            &parsed.module,
            &funcs,
            &analyses,
            &ptr_escape,
            &isa,
            &ArenaCostModel::default(),
        );

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for &func in &funcs {
            let name = parsed
                .module
                .ctx
                .func_sig(func, |sig| sig.name().to_string());
            names.insert(name, func);
        }

        PlanTestCtx {
            module: parsed.module,
            funcs,
            names,
            plan,
            analyses,
        }
    }

    fn dyn_sp_plan_from_src(src: &str) -> DynSpTestCtx {
        let ctx = plan_test_ctx_from_src(src);
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let section_entry = ctx
            .module
            .objects
            .values()
            .find_map(|object| {
                object.sections.iter().find_map(|section| {
                    section
                        .directives
                        .iter()
                        .find_map(|directive| match directive {
                            Directive::Entry(func) => Some(*func),
                            Directive::Include(_) | Directive::Data(_) | Directive::Embed(_) => {
                                None
                            }
                        })
                })
            })
            .unwrap_or(ctx.funcs[0]);
        let dyn_sp_plan = compute_dyn_sp_plan(
            &ctx.module,
            &ctx.funcs,
            section_entry,
            &ctx.plan,
            &ctx.analyses,
            &isa,
        );

        DynSpTestCtx {
            module: ctx.module,
            names: ctx.names,
            plan: dyn_sp_plan,
        }
    }

    #[test]
    fn fold_stack_actions_cancels_swap_self_inverse() {
        let actions = [Action::StackSwap(7), Action::StackSwap(7)];
        let folded = fold_stack_actions(&actions);
        assert!(folded.is_empty());
    }

    #[test]
    fn fold_stack_actions_keeps_nonmatching_dup_swap() {
        let actions = [Action::StackDup(3), Action::StackSwap(3)];
        let folded = fold_stack_actions(&actions);
        assert_eq!(folded.as_slice(), actions.as_slice());
    }

    #[test]
    fn fold_stack_actions_cancels_push_swap1_pop_noop() {
        let actions = [
            Action::Push(Immediate::I8(7)),
            Action::StackSwap(1),
            Action::Pop,
        ];
        let folded = fold_stack_actions(&actions);
        assert!(folded.is_empty());
    }

    #[test]
    fn fold_stack_actions_cancels_double_push_swap_pop_shuffle_noop() {
        let actions = [
            Action::StackSwap(3),
            Action::Push(Immediate::I1(false)),
            Action::Push(Immediate::I1(true)),
            Action::StackSwap(1),
            Action::StackSwap(2),
            Action::StackSwap(1),
            Action::Pop,
            Action::StackSwap(1),
            Action::Pop,
            Action::StackSwap(4),
        ];
        let folded = fold_stack_actions(&actions);
        assert_eq!(
            folded.as_slice(),
            [Action::StackSwap(3), Action::StackSwap(4)].as_slice()
        );
    }

    #[test]
    fn dyn_sp_entry_init_covers_ready_recursive_entry_scc() {
        let ctx = dyn_sp_plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v1 i256;
    v3.i256 = call %f 1.i1 v1;
    v4.i256 = mload v2 i256;
    v5.i256 = add v3 v4;
    return v5;
}
"#,
        );

        let f = ctx.names["f"];
        assert!(ctx.plan.entry_init);
        assert!(
            ctx.plan
                .frontier_init_calls
                .get(&f)
                .is_none_or(FxHashSet::is_empty)
        );
        assert!(ctx.plan.entry_live_frame[&f]);
    }

    #[test]
    fn return_escape_clamp_uses_caller_transitive_clobber_bound() {
        let ctx = plan_test_ctx_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %sum8(v0.i256, v1.i256, v2.i256, v3.i256, v4.i256, v5.i256, v6.i256, v7.i256) -> i256 {
block0:
    v8.i256 = add v0 v1;
    v9.i256 = add v2 v3;
    v10.i256 = add v4 v5;
    v11.i256 = add v6 v7;
    v12.i256 = add v8 v9;
    v13.i256 = add v10 v11;
    v14.i256 = add v12 v13;
    return v14;
}

func public %spill(v0.i256, v1.i256, v2.i256, v3.i256, v4.i256, v5.i256, v6.i256, v7.i256) -> i256 {
block1:
    v8.i256 = add v0 v1;
    v9.i256 = add v2 v3;
    v10.i256 = add v4 v5;
    v11.i256 = add v6 v7;
    v12.i256 = add v8 v9;
    v13.i256 = add v10 v11;
    v14.i256 = add v12 v13;
    jump block2;

block2:
    v15.i256 = phi (v14 block1) (v19 block2);
    v16.i256 = call %sum8 v0 v1 v2 v3 v4 v5 v6 v7;
    v17.i256 = call %sum8 v8 v9 v10 v11 v12 v13 v14 v15;
    v18.i256 = add v16 v17;
    v19.i256 = add v7 v18;
    v20.i1 = gt v19 1000.i256;
    br v20 block3 block2;

block3:
    return v18;
}

func public %mk() -> *i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.*i256 = bitcast v0 *i256;
    mstore v1 111.i256 i256;
    return v1;
}

func public %main(v0.i256, v1.i256, v2.i256, v3.i256, v4.i256, v5.i256, v6.i256, v7.i256) -> i256 {
block0:
    v8.*i256 = call %mk;
    v9.i256 = call %spill v0 v1 v2 v3 v4 v5 v6 v7;
    v10.i256 = mload v8 i256;
    v11.i256 = add v9 v10;
    return v11;
}
"#,
        );

        let mk = ctx.names["mk"];
        let main = ctx.names["main"];
        let abs_clobber_words = compute_abs_clobber_words(&ctx.module, &ctx.funcs, &ctx.plan);
        let clamp_words =
            compute_return_escape_caller_clamp_words(&ctx.module, &ctx.funcs, &ctx.plan);
        let main_active_words = ctx.plan.funcs[&main].active_abs_words();
        let main_clobber_words = abs_clobber_words[&main];

        assert!(
            main_clobber_words > main_active_words,
            "test setup requires a caller whose future callee clobber exceeds its own active frame"
        );
        assert_eq!(clamp_words[&mk], main_clobber_words);
    }

    #[test]
    fn dyn_sp_frontier_init_marks_call_from_non_ready_entry_into_ready_scc() {
        let ctx = dyn_sp_plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %dispatch(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.*i8 = evm_malloc 32.i256;
    v3.*i256 = bitcast v2 *i256;
    mstore v3 111.i256 i256;
    v4.i256 = mload v3 i256;
    return v4;

block2:
    v5.i256 = call %ready v1;
    return v5;
}

func private %ready(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 7.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = sub v0 1.i256;
    v4.i256 = call %ready v3;
    v5.i256 = mload v2 i256;
    v6.i256 = add v4 v5;
    return v6;
}
"#,
        );

        let dispatch = ctx.names["dispatch"];
        let ready = ctx.names["ready"];
        let frontier_calls = ctx
            .plan
            .frontier_init_calls
            .get(&dispatch)
            .expect("dispatch should have a frontier init call");
        let call_inst = ctx.module.func_store.view(dispatch, |function| {
            function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .find(|&inst| {
                    function
                        .dfg
                        .call_info(inst)
                        .is_some_and(|call| call.callee() == ready)
                })
                .expect("call to ready")
        });

        assert!(!ctx.plan.entry_init);
        assert!(frontier_calls.contains(&call_inst));
        assert!(
            ctx.plan
                .checked_frontier_init_calls
                .get(&dispatch)
                .is_none_or(|calls| !calls.contains(&call_inst))
        );
    }

    #[test]
    fn dyn_sp_entry_live_frame_propagates_only_from_active_callsites() {
        let ctx = dyn_sp_plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %ready(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.i256 = call %helper;
    return v2;

block2:
    v3.i1 = eq v1 0.i256;
    br v3 block3 block4;

block3:
    return 0.i256;

block4:
    v4.*i256 = alloca i256;
    mstore v4 v1 i256;
    v5.i256 = call %helper;
    v6.i256 = sub v1 1.i256;
    v7.i256 = call %ready 0.i1 v6;
    v8.i256 = mload v4 i256;
    v9.i256 = add v5 v8;
    return v9;
}

func private %helper() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.*i256 = bitcast v0 *i256;
    mstore v1 111.i256 i256;
    v2.i256 = mload v1 i256;
    return v2;
}
"#,
        );

        let ready = ctx.names["ready"];
        let helper = ctx.names["helper"];
        let helper_calls: Vec<InstId> = ctx.module.func_store.view(ready, |function| {
            function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .filter(|&inst| {
                    function
                        .dfg
                        .call_info(inst)
                        .is_some_and(|call| call.callee() == helper)
                })
                .collect()
        });
        assert_eq!(
            helper_calls.len(),
            2,
            "expected one cold and one hot helper call"
        );

        let summary = ctx
            .plan
            .frame_summaries
            .get(&ready)
            .expect("missing ready summary");
        let active_count = helper_calls
            .iter()
            .copied()
            .filter(|&inst| summary.local_frame_active_before_inst(inst))
            .count();

        assert_eq!(
            active_count, 1,
            "only the hot helper call should be frame-active"
        );
        assert!(ctx.plan.entry_live_frame[&helper]);
    }

    #[test]
    fn dyn_sp_helper_before_lazy_enter_stays_not_live() {
        let ctx = dyn_sp_plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %helper() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.*i256 = bitcast v0 *i256;
    mstore v1 111.i256 i256;
    v2.i256 = mload v1 i256;
    return v2;
}

func public %ready(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.i256 = call %helper;
    return v2;

block2:
    v3.*i256 = alloca i256;
    mstore v3 v1 i256;
    v4.i256 = mload v3 i256;
    return v4;
}

func public %entry(v0.i1, v1.i256) -> i256 {
block0:
    v2.i256 = call %ready v0 v1;
    return v2;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        );

        let helper = ctx.names["helper"];
        let ready = ctx.names["ready"];
        let ready_summary = ctx
            .plan
            .frame_summaries
            .get(&ready)
            .expect("missing ready summary");
        let helper_call = ctx.module.func_store.view(ready, |function| {
            function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .find(|&inst| {
                    function
                        .dfg
                        .call_info(inst)
                        .is_some_and(|call| call.callee() == helper)
                })
                .expect("call to helper")
        });

        assert!(
            !ready_summary.local_frame_active_before_inst(helper_call),
            "helper call should stay before lazy frame entry"
        );
        assert!(!ctx.plan.entry_live_frame[&helper]);
    }

    #[test]
    fn dyn_sp_mixed_entry_helper_uses_checked_frontier_init() {
        let ctx = dyn_sp_plan_from_src(
            r#"
target = "evm-ethereum-osaka"

func public %entry(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    v2.i256 = call %helper v1;
    return v2;

block2:
    v3.i256 = call %ready_caller v1;
    return v3;
}

func private %helper(v0.i256) -> i256 {
block0:
    v1.i256 = call %target v0;
    return v1;
}

func private %ready_caller(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = call %helper 0.i256;
    v4.i256 = sub v0 1.i256;
    v5.i256 = call %ready_caller v4;
    v6.i256 = mload v2 i256;
    v7.i256 = add v3 v5;
    v8.i256 = add v7 v6;
    return v8;
}

func private %target(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = sub v0 1.i256;
    v4.i256 = call %target v3;
    v5.i256 = mload v2 i256;
    v6.i256 = add v4 v5;
    return v6;
}
"#,
        );

        let helper = ctx.names["helper"];
        let target = ctx.names["target"];
        let helper_call = ctx.module.func_store.view(helper, |function| {
            function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .find(|&inst| {
                    function
                        .dfg
                        .call_info(inst)
                        .is_some_and(|call| call.callee() == target)
                })
                .expect("helper call to target")
        });

        assert!(
            ctx.plan
                .frontier_init_calls
                .get(&helper)
                .is_some_and(|calls| calls.contains(&helper_call))
        );
        assert!(
            ctx.plan
                .checked_frontier_init_calls
                .get(&helper)
                .is_some_and(|calls| calls.contains(&helper_call))
        );
    }

    #[test]
    fn noreturn_call_skips_continuation_marker_and_preserve() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %abort() -> i256 {
block0:
    evm_revert 0.i256 0.i256;
}

func public %caller(v0.i256) -> i256 {
block0:
    v1.*i256 = alloca i256;
    mstore v1 v0 i256;
    v2.i256 = call %abort;
    v3.i256 = mload v1 i256;
    return v3;
}
"#,
        )
        .unwrap();

        func_behavior::analyze_module(&parsed.module);

        let funcs = parsed.module.funcs();
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for &f in &funcs {
            let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
            names.insert(name, f);
        }
        let caller = names["caller"];

        let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
        for &func in &funcs {
            parsed.module.func_store.modify(func, |function| {
                let mut cfg = ControlFlowGraph::new();
                cfg.compute(function);

                let mut splitter = CriticalEdgeSplitter::new();
                splitter.run(function, &mut cfg);

                let mut liveness = Liveness::new();
                liveness.compute(function, &cfg);

                let mut inst_liveness = InstLiveness::new();
                inst_liveness.compute(function, &cfg, &liveness);

                let mut dom = DomTree::new();
                dom.compute(&cfg);

                analyses.insert(
                    func,
                    memory_plan::FuncAnalysis {
                        alloc: StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute(),
                        inst_liveness,
                        block_order: dom.rpo().to_vec(),
                        value_aliases: {
                            let mut value_aliases = SecondaryMap::new();
                            for value in function.dfg.value_ids() {
                                value_aliases[value] = Some(value);
                            }
                            value_aliases
                        },
                    },
                );
            });
        }

        let (call_inst, call_args) = parsed.module.func_store.view(caller, |function| {
            function
                .layout
                .iter_block()
                .flat_map(|block| function.layout.iter_inst(block))
                .find_map(|inst| {
                    function
                        .dfg
                        .cast_call(inst)
                        .map(|call| (inst, call.args().clone()))
                })
                .expect("missing call inst")
        });

        let actions = analyses
            .get(&caller)
            .expect("missing caller analysis")
            .alloc
            .read(call_inst, &call_args);
        assert!(
            !actions
                .iter()
                .any(|a| matches!(a, Action::PushContinuationOffset)),
            "noreturn call should not materialize a local continuation: {actions:?}"
        );

        let plan = compute_program_memory_plan(
            &parsed.module,
            &funcs,
            &analyses,
            &ptr_escape,
            &isa,
            &ArenaCostModel::default(),
        );
        assert!(
            !plan
                .funcs
                .get(&caller)
                .expect("missing caller plan")
                .call_preserve
                .contains_key(&call_inst),
            "noreturn call should not preserve caller scratch state"
        );
    }

    #[test]
    fn prepare_section_handles_recursive_scratch_barriers_without_oscillation() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    br v1 block1 block2;

block1:
    return 0.i256;

block2:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = mload v2 i256;
    v4.i256 = add v3 1.i256;
    v5.i256 = add v3 2.i256;
    v6.i256 = add v3 3.i256;
    v7.i256 = add v3 4.i256;
    mstore v2 v7 i256;
    v8.i256 = sub v3 1.i256;
    v9.i256 = call %f v8;
    v10.i256 = mload v2 i256;
    v11.i256 = add v9 v10;
    v12.i256 = add v11 v4;
    v13.i256 = add v12 v5;
    v14.i256 = add v13 v6;
    return v14;
}

func public %entry() {
block0:
    v0.i256 = call %f 3.i256;
    mstore 0.i32 v0 i256;
    evm_return 0.i8 32.i8;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        )
        .unwrap();

        let funcs = parsed.module.funcs();
        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for &func in &funcs {
            let name = parsed
                .module
                .ctx
                .func_sig(func, |sig| sig.name().to_string());
            names.insert(name, func);
        }

        let backend = EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }))
        .with_stackify_reach_depth(4);
        let object = ObjectName::from("Contract");
        let section = SectionName::from("runtime");
        let embeds: Vec<EmbedSymbol> = Vec::new();
        let section_ctx = SectionLoweringCtx {
            object: &object,
            section: &section,
            embed_symbols: &embeds,
        };

        backend.prepare_section(&parsed.module, &funcs, &section_ctx);

        let section_state = backend.section_state.borrow();
        let prepared = section_state.as_ref().expect("section prepared");
        assert!(
            !prepared.allocs[&names["f"]].uses_scratch_spills(),
            "recursive caller should treat self-call as a scratch barrier"
        );
    }

    #[test]
    fn prepare_section_runs_late_dead_arg_elim_on_helpers() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %helper(v0.i256, v1.i256) -> i256 {
block0:
    return v1;
}

func public %entry(v0.i256) -> i256 {
block0:
    v1.i256 = call %helper 0.i256 v0;
    return v1;
}

object @Contract {
  section runtime {
    entry %entry;
  }
}
"#,
        )
        .unwrap();

        let funcs = parsed.module.funcs();
        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for &func in &funcs {
            let name = parsed
                .module
                .ctx
                .func_sig(func, |sig| sig.name().to_string());
            names.insert(name, func);
        }

        let backend = EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }))
        .with_late_cleanup_optimizations(true);
        let object = ObjectName::from("Contract");
        let section = SectionName::from("runtime");
        let embeds: Vec<EmbedSymbol> = Vec::new();
        let section_ctx = SectionLoweringCtx {
            object: &object,
            section: &section,
            embed_symbols: &embeds,
        };

        backend.prepare_section(&parsed.module, &funcs, &section_ctx);

        let helper_sig = parsed
            .module
            .ctx
            .get_sig(names["helper"])
            .expect("helper signature should exist");
        assert_eq!(
            helper_sig.args().len(),
            1,
            "late cleanup should prune dead helper arg"
        );
        parsed.module.func_store.view(names["entry"], |function| {
            let dumped = FuncWriter::new(names["entry"], function).dump_string();
            assert!(
                dumped.contains("v1.i256 = call %helper v0;"),
                "entry callsite should be rewritten after late dead-arg elim:\n{dumped}"
            );
        });
    }

    #[test]
    fn lowering_elides_section_entry_jumpdest_for_noreturn_call() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %abort() {
block0:
    evm_revert 0.i256 0.i256;
}

func public %caller() {
block0:
    call %abort;
    unreachable;
}

object @Contract {
  section runtime {
    entry %caller;
  }
}
"#,
        )
        .unwrap();

        let funcs = parsed.module.funcs();
        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for &f in &funcs {
            let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
            names.insert(name, f);
        }

        let backend = EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }));
        let object = ObjectName::from("Contract");
        let section = SectionName::from("runtime");
        let embeds: Vec<EmbedSymbol> = Vec::new();
        let section_ctx = SectionLoweringCtx {
            object: &object,
            section: &section,
            embed_symbols: &embeds,
        };

        backend.prepare_section(&parsed.module, &funcs, &section_ctx);
        let lowered = backend
            .lower_function(&parsed.module, names["caller"], &section_ctx)
            .expect("caller lowers");

        assert_eq!(lowered.block_order.len(), 1, "expected single caller block");
        let block = lowered.block_order[0];
        let jumpdest_count = lowered
            .vcode
            .block_insns(block)
            .filter(|&inst| (lowered.vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8))
            .count();
        assert_eq!(
            jumpdest_count, 0,
            "section-entry caller should not need a JUMPDEST without incoming jumps"
        );

        let lowered_abort = backend
            .lower_function(&parsed.module, names["abort"], &section_ctx)
            .expect("abort lowers");
        let abort_block = lowered_abort.block_order[0];
        let abort_jumpdest_count = lowered_abort
            .vcode
            .block_insns(abort_block)
            .filter(|&inst| (lowered_abort.vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8))
            .count();
        assert_eq!(
            abort_jumpdest_count, 1,
            "direct call target should still materialize an entry JUMPDEST"
        );
    }

    #[test]
    fn lowering_materializes_jumpdest_for_nonfallthrough_block_target() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1) -> i256 {
block0:
    br v0 block2 block1;

block1:
    return 1.i256;

block2:
    return 2.i256;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();

        let func = parsed.module.funcs()[0];
        let backend = EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }));
        let object = ObjectName::from("Contract");
        let section = SectionName::from("runtime");
        let embeds: Vec<EmbedSymbol> = Vec::new();
        let section_ctx = SectionLoweringCtx {
            object: &object,
            section: &section,
            embed_symbols: &embeds,
        };

        backend.prepare_section(&parsed.module, &[func], &section_ctx);
        let lowered = backend
            .lower_function(&parsed.module, func, &section_ctx)
            .expect("main lowers");

        let block2 = lowered
            .block_order
            .iter()
            .copied()
            .find(|block| block.0 == 2)
            .expect("missing block2");
        assert!(
            lowered
                .vcode
                .block_insns(block2)
                .next()
                .is_some_and(|inst| {
                    (lowered.vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8)
                }),
            "non-fallthrough branch target should start with JUMPDEST"
        );
    }

    #[test]
    fn materialize_jumpdests_uses_final_block_fixups() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main() -> i256 {
block0:
    return 0.i256;

block1:
    return 1.i256;
}
"#,
        )
        .unwrap();

        let func = parsed.module.funcs()[0];
        parsed.module.func_store.view(func, |function| {
            let block_order: Vec<_> = function.layout.iter_block().collect();
            assert_eq!(block_order.len(), 2, "expected two blocks");

            let mut vcode = VCode::<OpCode>::default();
            let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block_order[0]);
            let label = vcode.labels.push(Label::Block(block_order[1]));
            vcode.fixups.insert((push, VCodeFixup::Label(label)));
            vcode.add_inst_to_block(OpCode::JUMP, None, block_order[0]);
            vcode.add_inst_to_block(OpCode::STOP, None, block_order[1]);

            materialize_jumpdests(&mut vcode, function, &block_order, false);

            assert!(
                vcode
                    .block_insns(block_order[1])
                    .next()
                    .is_some_and(|inst| (vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8)),
                "final block fixup should force a block-entry JUMPDEST"
            );
            assert!(
                vcode
                    .block_insns(block_order[0])
                    .next()
                    .is_some_and(|inst| (vcode.insts[inst] as u8) != (OpCode::JUMPDEST as u8)),
                "entry block should remain unpadded without function-entry targeting"
            );
        });
    }

    #[test]
    fn lowering_elides_pure_jump_alias_blocks() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1) {
block0:
    br v0 block1 block2;

block1:
    jump block3;

block2:
    v1.i256 = add 1.i256 2.i256;
    jump block3;

block3:
    evm_revert 0.i256 0.i256;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();

        let func = parsed.module.funcs()[0];
        let backend = EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }));
        let object = ObjectName::from("Contract");
        let section = SectionName::from("runtime");
        let embeds: Vec<EmbedSymbol> = Vec::new();
        let section_ctx = SectionLoweringCtx {
            object: &object,
            section: &section,
            embed_symbols: &embeds,
        };

        backend.prepare_section(&parsed.module, &[func], &section_ctx);
        let lowered = backend
            .lower_function(&parsed.module, func, &section_ctx)
            .expect("main lowers");

        assert!(
            lowered.block_order.iter().all(|block| block.0 != 1),
            "pure trampoline block should be omitted from final block order"
        );
        assert!(
            lowered
                .vcode
                .blocks
                .get(BlockId(1))
                .is_none_or(|block| block.is_empty()),
            "late alias block should not lower any instructions"
        );
        assert!(
            lowered.block_order.iter().all(|block| {
                let insts: Vec<_> = lowered.vcode.block_insns(*block).collect();
                !matches!(
                    insts.as_slice(),
                    [jumpdest, push, jump]
                        if (lowered.vcode.insts[*jumpdest] as u8) == (OpCode::JUMPDEST as u8)
                            && is_push_opcode(lowered.vcode.insts[*push])
                            && matches!(
                                lowered.vcode.fixups.get(*push),
                                Some((_, VCodeFixup::Label(_)))
                            )
                            && (lowered.vcode.insts[*jump] as u8) == (OpCode::JUMP as u8)
                )
            }),
            "late lowering should not leave pure jump trampoline blocks behind"
        );
    }

    #[test]
    fn lowering_folds_branch_with_same_canonical_dest() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main(v0.i1) {
block0:
    br v0 block1 block2;

block1:
    jump block3;

block2:
    jump block3;

block3:
    evm_revert 0.i256 0.i256;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();

        let func = parsed.module.funcs()[0];
        let backend = EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }));
        let object = ObjectName::from("Contract");
        let section = SectionName::from("runtime");
        let embeds: Vec<EmbedSymbol> = Vec::new();
        let section_ctx = SectionLoweringCtx {
            object: &object,
            section: &section,
            embed_symbols: &embeds,
        };

        backend.prepare_section(&parsed.module, &[func], &section_ctx);
        let lowered = backend
            .lower_function(&parsed.module, func, &section_ctx)
            .expect("main lowers");
        let entry = lowered.block_order[0];
        let ops: Vec<_> = lowered
            .vcode
            .block_insns(entry)
            .map(|inst| lowered.vcode.insts[inst] as u8)
            .collect();

        assert!(
            !ops.contains(&(OpCode::JUMPI as u8)),
            "branch with one canonical destination should not lower to JUMPI: {ops:?}"
        );
    }

    #[test]
    fn prepared_section_state_is_reusable_across_lower_calls() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 1.i256;
    return v1;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();

        let func = parsed.module.funcs()[0];
        let backend = EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }));
        let object = ObjectName::from("Contract");
        let section = SectionName::from("runtime");
        let embeds: Vec<EmbedSymbol> = Vec::new();
        let section_ctx = SectionLoweringCtx {
            object: &object,
            section: &section,
            embed_symbols: &embeds,
        };

        backend.prepare_section(&parsed.module, &[func], &section_ctx);
        assert!(backend.prepared_section_matches(&parsed.module, &[func], &section_ctx));

        backend
            .lower_function(&parsed.module, func, &section_ctx)
            .expect("first lower succeeds");
        assert!(backend.prepared_section_matches(&parsed.module, &[func], &section_ctx));
        assert!(
            backend
                .section_state
                .borrow()
                .as_ref()
                .is_some_and(|state| state.allocs.contains_key(&func)),
            "prepared alloc should remain cached after lowering"
        );

        backend
            .lower_function(&parsed.module, func, &section_ctx)
            .expect("second lower succeeds");
        assert!(backend.prepared_section_matches(&parsed.module, &[func], &section_ctx));
    }

    #[test]
    fn prepared_section_state_is_invalidated_after_module_mutation() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main() {
block0:
    evm_return 0.i256 0.i256;
}

object @Contract {
  section runtime {
    entry %main;
  }
}
"#,
        )
        .unwrap();

        let func = parsed.module.funcs()[0];
        let backend = EvmBackend::new(Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        }));
        let object = ObjectName::from("Contract");
        let section = SectionName::from("runtime");
        let embeds: Vec<EmbedSymbol> = Vec::new();
        let section_ctx = SectionLoweringCtx {
            object: &object,
            section: &section,
            embed_symbols: &embeds,
        };

        backend.prepare_section(&parsed.module, &[func], &section_ctx);
        assert!(
            backend
                .prepared_function(&parsed.module, func, &section_ctx)
                .is_some()
        );

        parsed.module.func_store.modify(func, |function| {
            let block = function.layout.entry_block().expect("entry block exists");
            let term = function
                .layout
                .last_inst_of(block)
                .expect("entry block terminator exists");
            let (addr, len) = match backend.isa.inst_set().resolve_inst(function.dfg.inst(term)) {
                EvmInstKind::EvmReturn(ret) => (*ret.addr(), *ret.len()),
                _ => panic!("terminator should be evm_return"),
            };
            function.dfg.replace_inst(
                term,
                Box::new(sonatina_ir::inst::evm::EvmRevert::new(
                    backend
                        .isa
                        .inst_set()
                        .has_evm_revert()
                        .expect("evm_revert supported"),
                    addr,
                    len,
                )),
            );
        });

        assert!(!backend.prepared_section_matches(&parsed.module, &[func], &section_ctx));
        assert!(
            backend
                .prepared_function(&parsed.module, func, &section_ctx)
                .is_none()
        );
        assert!(
            backend.section_state.borrow().is_none(),
            "stale prepared section should be cleared after invalidation"
        );

        let lowered = backend
            .lower_function(&parsed.module, func, &section_ctx)
            .expect("lower after mutation succeeds");
        assert!(
            lowered
                .vcode
                .insts
                .values()
                .any(|&op| (op as u8) == (OpCode::REVERT as u8)),
            "updated lowering should reflect the mutated terminator"
        );
        assert!(
            !lowered
                .vcode
                .insts
                .values()
                .any(|&op| (op as u8) == (OpCode::RETURN as u8)),
            "stale prepared lowering should not survive module mutation"
        );
    }

    #[test]
    fn call_save_pre_tucks_saved_words_below_operands() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %caller(v0.i256, v1.i256) -> i256 {
block0:
    v2.*i256 = alloca i256;
    mstore v2 1.i256 i256;
    v3.i256 = mload v2 i256;
    v4.i256 = add v3 v0;
    mstore v2 v4 i256;
    v5.i256 = call %caller 11.i256 22.i256;
    v6.i256 = mload v2 i256;
    v7.i256 = add v5 v6;
    return v7;
}
"#,
        )
        .unwrap();

        let funcs = parsed.module.funcs();
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
        for &func in &funcs {
            parsed.module.func_store.modify(func, |function| {
                let mut cfg = ControlFlowGraph::new();
                cfg.compute(function);

                let mut splitter = CriticalEdgeSplitter::new();
                splitter.run(function, &mut cfg);

                let mut liveness = Liveness::new();
                liveness.compute(function, &cfg);

                let mut inst_liveness = InstLiveness::new();
                inst_liveness.compute(function, &cfg, &liveness);

                let mut dom = DomTree::new();
                dom.compute(&cfg);

                let block_order = dom.rpo().to_owned();
                let alloc = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute();

                analyses.insert(
                    func,
                    memory_plan::FuncAnalysis {
                        alloc,
                        inst_liveness,
                        block_order,
                        value_aliases: {
                            let mut value_aliases = SecondaryMap::new();
                            for value in function.dfg.value_ids() {
                                value_aliases[value] = Some(value);
                            }
                            value_aliases
                        },
                    },
                );
            });
        }

        let cost_model = ArenaCostModel {
            w_save: 0,
            w_code: 0,
            ..ArenaCostModel::default()
        };
        let plan = compute_program_memory_plan(
            &parsed.module,
            &funcs,
            &analyses,
            &ptr_escape,
            &isa,
            &cost_model,
        );

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for &f in &funcs {
            let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
            names.insert(name, f);
        }
        let caller = names["caller"];

        let (call_inst, call_args): (InstId, SmallVec<[ValueId; 8]>) =
            parsed.module.func_store.view(caller, |function| {
                for block in function.layout.iter_block() {
                    for inst in function.layout.iter_inst(block) {
                        let Some(call) = function.dfg.cast_call(inst) else {
                            continue;
                        };
                        return (inst, call.args().clone());
                    }
                }
                panic!("missing call inst");
            });

        assert_eq!(call_args.len(), 2, "test expects a 2-arg call");

        let analysis = analyses.remove(&caller).expect("missing caller analysis");
        let mem_plan = plan
            .funcs
            .get(&caller)
            .expect("missing caller plan")
            .clone();
        let alloc = FinalAlloc::new(analysis.alloc, mem_plan);

        let save_plan = alloc
            .mem_plan
            .call_preserve
            .get(&call_inst)
            .expect("expected non-empty call preserve entry for call");
        let PreserveMode::ShadowRuns { shadow_obj, runs } = &save_plan.mode else {
            panic!("expected shadow preserve plan for caller");
        };
        assert!(!runs.is_empty(), "expected at least one saved run");

        let actions = alloc.read(call_inst, &call_args);
        let cont_pos = actions
            .iter()
            .position(|a| matches!(a, Action::PushContinuationOffset))
            .expect("missing continuation marker");

        let expected_len = runs
            .iter()
            .map(|run| usize::try_from(run.len_words).expect("run length overflow"))
            .sum::<usize>()
            .checked_mul(2)
            .expect("expected injected length overflow");
        assert!(
            cont_pos >= expected_len,
            "expected injected actions immediately before continuation marker"
        );
        let injected = &actions[cont_pos - expected_len..cont_pos];
        let shadow_loc = alloc.obj_loc_for_id(*shadow_obj);
        let mut expected = Actions::new();
        for run in runs {
            for word in 0..run.len_words {
                expected.push(
                    alloc.action_load_for_loc(ObjLoc::ScratchAbs(run.scratch_src_word), word),
                );
                expected.push(
                    alloc.action_store_for_loc(
                        shadow_loc,
                        run.shadow_dst_word
                            .checked_add(word)
                            .expect("shadow save offset overflow"),
                    ),
                );
            }
        }
        assert_eq!(injected, expected.as_slice());
    }

    #[test]
    fn call_save_post_preserves_two_results_above_saved_words() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %caller(v0.i256, v1.i256) -> (i256, i1) {
block0:
    v2.*i256 = alloca i256;
    mstore v2 1.i256 i256;
    v3.i256 = mload v2 i256;
    v4.i256 = add v3 v0;
    mstore v2 v4 i256;
    (v5.i256, v6.i1) = call %caller 11.i256 22.i256;
    v7.i256 = mload v2 i256;
    br v6 block1 block2;

block1:
    v8.i256 = add v5 v7;
    return (v8, v6);

block2:
    v9.i256 = add v7 1.i256;
    return (v9, v6);
}
"#,
        )
        .unwrap();

        let funcs = parsed.module.funcs();
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let ptr_escape = compute_ptr_escape_summaries(&parsed.module, &funcs, &isa);

        let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();
        for &func in &funcs {
            parsed.module.func_store.modify(func, |function| {
                let mut cfg = ControlFlowGraph::new();
                cfg.compute(function);

                let mut splitter = CriticalEdgeSplitter::new();
                splitter.run(function, &mut cfg);

                let mut liveness = Liveness::new();
                liveness.compute(function, &cfg);

                let mut inst_liveness = InstLiveness::new();
                inst_liveness.compute(function, &cfg, &liveness);

                let mut dom = DomTree::new();
                dom.compute(&cfg);

                let block_order = dom.rpo().to_owned();
                let alloc = StackifyBuilder::new(function, &cfg, &dom, &liveness, 16).compute();

                analyses.insert(
                    func,
                    memory_plan::FuncAnalysis {
                        alloc,
                        inst_liveness,
                        block_order,
                        value_aliases: {
                            let mut value_aliases = SecondaryMap::new();
                            for value in function.dfg.value_ids() {
                                value_aliases[value] = Some(value);
                            }
                            value_aliases
                        },
                    },
                );
            });
        }

        let cost_model = ArenaCostModel {
            w_save: 0,
            w_code: 0,
            ..ArenaCostModel::default()
        };
        let plan = compute_program_memory_plan(
            &parsed.module,
            &funcs,
            &analyses,
            &ptr_escape,
            &isa,
            &cost_model,
        );

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        for &f in &funcs {
            let name = parsed.module.ctx.func_sig(f, |sig| sig.name().to_string());
            names.insert(name, f);
        }
        let caller = names["caller"];

        let (call_inst, call_results): (InstId, SmallVec<[ValueId; 8]>) =
            parsed.module.func_store.view(caller, |function| {
                for block in function.layout.iter_block() {
                    for inst in function.layout.iter_inst(block) {
                        if function.dfg.call_info(inst).is_none() {
                            continue;
                        }
                        return (
                            inst,
                            function.dfg.inst_results(inst).iter().copied().collect(),
                        );
                    }
                }
                panic!("missing call inst");
            });

        let analysis = analyses.remove(&caller).expect("missing caller analysis");
        let mem_plan = plan
            .funcs
            .get(&caller)
            .expect("missing caller plan")
            .clone();
        let alloc = FinalAlloc::new(analysis.alloc, mem_plan);

        let save_plan = alloc
            .mem_plan
            .call_preserve
            .get(&call_inst)
            .expect("expected non-empty call preserve entry for call");
        assert_eq!(save_plan.result_count, 2);
        let PreserveMode::ShadowRuns { shadow_obj, runs } = &save_plan.mode else {
            panic!("expected shadow preserve plan for caller");
        };
        assert!(!runs.is_empty(), "expected at least one saved run");

        let actions = alloc.write(call_inst, &call_results);
        let mut expected = Actions::new();
        let shadow_loc = alloc.obj_loc_for_id(*shadow_obj);
        for run in runs.iter().rev() {
            for word in (0..run.len_words).rev() {
                expected.push(
                    alloc.action_load_for_loc(
                        shadow_loc,
                        run.shadow_dst_word
                            .checked_add(word)
                            .expect("shadow restore offset overflow"),
                    ),
                );
                expected.push(
                    alloc.action_store_for_loc(ObjLoc::ScratchAbs(run.scratch_src_word), word),
                );
            }
        }
        assert_eq!(
            actions.as_slice(),
            expected.as_slice(),
            "multi-result call preserve restore must copy saved scratch words back after post-actions"
        );
    }

    #[test]
    fn prune_removes_and_one_after_bool_producer() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);

        vcode.add_inst_to_block(OpCode::LT, None, block);
        let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
        vcode.inst_imm_bytes.insert((push, smallvec![1u8]));
        vcode.add_inst_to_block(OpCode::AND, None, block);

        prune_redundant_opcode_sequences(&mut vcode, &[block]);

        let ops: Vec<_> = vcode
            .block_insns(block)
            .map(|inst| vcode.insts[inst] as u8)
            .collect();
        assert_eq!(ops, vec![OpCode::LT as u8]);
    }

    #[test]
    fn prune_keeps_and_mask_when_not_bool_producer() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);

        vcode.add_inst_to_block(OpCode::ADD, None, block);
        let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
        vcode.inst_imm_bytes.insert((push, smallvec![1u8]));
        vcode.add_inst_to_block(OpCode::AND, None, block);

        prune_redundant_opcode_sequences(&mut vcode, &[block]);

        let ops: Vec<_> = vcode
            .block_insns(block)
            .map(|inst| vcode.insts[inst] as u8)
            .collect();
        assert_eq!(
            ops,
            vec![OpCode::ADD as u8, OpCode::PUSH1 as u8, OpCode::AND as u8]
        );
    }

    #[test]
    fn prune_keeps_and_mask_when_mask_not_one() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);

        vcode.add_inst_to_block(OpCode::EQ, None, block);
        let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
        vcode.inst_imm_bytes.insert((push, smallvec![3u8]));
        vcode.add_inst_to_block(OpCode::AND, None, block);

        prune_redundant_opcode_sequences(&mut vcode, &[block]);

        let ops: Vec<_> = vcode
            .block_insns(block)
            .map(|inst| vcode.insts[inst] as u8)
            .collect();
        assert_eq!(
            ops,
            vec![OpCode::EQ as u8, OpCode::PUSH1 as u8, OpCode::AND as u8]
        );
    }

    #[test]
    fn prune_removes_iszero_iszero_before_labeled_jumpi() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);

        vcode.add_inst_to_block(OpCode::ISZERO, None, block);
        vcode.add_inst_to_block(OpCode::ISZERO, None, block);
        let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
        vcode.add_inst_to_block(OpCode::JUMPI, None, block);

        let label = vcode.labels.push(Label::Block(BlockId(1)));
        vcode.fixups.insert((push, VCodeFixup::Label(label)));

        prune_redundant_opcode_sequences(&mut vcode, &[block]);

        let ops: Vec<_> = vcode
            .block_insns(block)
            .map(|inst| vcode.insts[inst] as u8)
            .collect();
        assert_eq!(ops, vec![OpCode::PUSH1 as u8, OpCode::JUMPI as u8]);
    }

    #[test]
    fn prune_keeps_iszero_iszero_before_non_labeled_jumpi() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);

        vcode.add_inst_to_block(OpCode::ISZERO, None, block);
        vcode.add_inst_to_block(OpCode::ISZERO, None, block);
        let push = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
        vcode.inst_imm_bytes.insert((push, smallvec![7u8]));
        vcode.add_inst_to_block(OpCode::JUMPI, None, block);

        prune_redundant_opcode_sequences(&mut vcode, &[block]);

        let ops: Vec<_> = vcode
            .block_insns(block)
            .map(|inst| vcode.insts[inst] as u8)
            .collect();
        assert_eq!(
            ops,
            vec![
                OpCode::ISZERO as u8,
                OpCode::ISZERO as u8,
                OpCode::PUSH1 as u8,
                OpCode::JUMPI as u8
            ]
        );
    }
}
