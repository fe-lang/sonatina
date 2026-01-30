mod heap_plan;
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
use std::cell::RefCell;

use crate::{
    critical_edge::CriticalEdgeSplitter,
    domtree::DomTree,
    liveness::{InstLiveness, Liveness},
    machinst::{
        lower::{FixupUpdate, Lower, LowerBackend, LoweredFunction, SectionLoweringCtx},
        vcode::{Label, SymFixup, SymFixupKind, VCode, VCodeInst},
    },
    stackalloc::{Action, Actions, Allocator, StackifyAlloc, StackifyLiveValues},
};
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    BlockId, Function, Immediate, InstId, InstSetExt, Module, Type, U256, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{Isa, evm::Evm},
    module::{FuncRef, ModuleCtx},
    types::CompoundType,
};
use sonatina_triple::{EvmVersion, OperatingSystem};

use mem_effects::compute_func_mem_effects;
use memory_plan::{
    ArenaCostModel, CallPreserveChoice, DYN_FP_SLOT, DYN_SP_SLOT, FREE_PTR_SLOT, FuncMemPlan,
    MemScheme, ProgramMemoryPlan, STATIC_BASE, WORD_BYTES, compute_program_memory_plan,
};
use ptr_escape::{PtrEscapeSummary, compute_ptr_escape_summaries};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum PushWidthPolicy {
    #[default]
    Push4,
    MinimalRelax,
}

struct PreparedSection {
    plan: ProgramMemoryPlan,
    allocs: FxHashMap<FuncRef, StackifyAlloc>,
    block_orders: FxHashMap<FuncRef, Vec<BlockId>>,
}

struct PreparedLowering {
    alloc: StackifyAlloc,
    block_order: Vec<BlockId>,
    mem_plan: FuncMemPlan,
}

pub struct EvmBackend {
    isa: Evm,
    stackify_reach_depth: u8,
    arena_cost_model: ArenaCostModel,
    section_state: RefCell<Option<PreparedSection>>,
    current_mem_plan: RefCell<Option<FuncMemPlan>>,
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
            section_state: RefCell::new(None),
            current_mem_plan: RefCell::new(None),
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

    pub fn stackify_reach_depth(&self) -> u8 {
        self.stackify_reach_depth
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
            "evm mem plan: dyn_base=0x{:x} static_base=0x{:x}",
            section.plan.dyn_base, STATIC_BASE
        )
        .expect("mem plan write failed");

        for &func in funcs {
            let Some(func_plan) = section.plan.funcs.get(&func) else {
                continue;
            };

            let name = module.ctx.func_sig(func, |sig| sig.name().to_string());

            match &func_plan.scheme {
                MemScheme::StaticArena(st) => {
                    writeln!(
                        &mut out,
                        "evm mem plan: {name} scheme=StaticArena need_words={} locals_words={}",
                        st.need_words, func_plan.locals_words
                    )
                    .expect("mem plan write failed");
                }
                MemScheme::DynamicFrame => {
                    writeln!(
                        &mut out,
                        "evm mem plan: {name} scheme=DynamicFrame locals_words={}",
                        func_plan.locals_words
                    )
                    .expect("mem plan write failed");
                }
            }

            let addr_of = |offset_words: u32| match &func_plan.scheme {
                MemScheme::StaticArena(_) => {
                    let addr_bytes = STATIC_BASE
                        .checked_add(
                            offset_words
                                .checked_mul(WORD_BYTES)
                                .expect("address bytes overflow"),
                        )
                        .expect("address bytes overflow");
                    format!("0x{addr_bytes:x}")
                }
                MemScheme::DynamicFrame => {
                    let addr_bytes = offset_words
                        .checked_mul(WORD_BYTES)
                        .expect("address bytes overflow");
                    if addr_bytes == 0 {
                        "fp".to_string()
                    } else {
                        format!("fp+0x{addr_bytes:x}")
                    }
                }
            };

            if detail {
                let mut direct_callee_need_max: u32 = 0;
                module.func_store.view(func, |function| {
                    for block in function.layout.iter_block() {
                        for insn in function.layout.iter_inst(block) {
                            let Some(call) = function.dfg.call_info(insn) else {
                                continue;
                            };
                            let Some(callee_plan) = section.plan.funcs.get(&call.callee()) else {
                                continue;
                            };
                            let MemScheme::StaticArena(st) = &callee_plan.scheme else {
                                continue;
                            };
                            direct_callee_need_max = direct_callee_need_max.max(st.need_words);
                        }
                    }
                });

                if let MemScheme::StaticArena(st) = &func_plan.scheme {
                    writeln!(
                        &mut out,
                        "  detail locals_words={} direct_callee_need_max_words={direct_callee_need_max} need_words={}",
                        func_plan.locals_words, st.need_words
                    )
                    .expect("mem plan write failed");

                    let mut call_info: FxHashMap<InstId, (FuncRef, bool)> = FxHashMap::default();
                    module.func_store.view(func, |function| {
                        for block in function.layout.iter_block() {
                            for inst in function.layout.iter_inst(block) {
                                let Some(call) = function.dfg.call_info(inst) else {
                                    continue;
                                };
                                call_info.insert(
                                    inst,
                                    (call.callee(), function.dfg.inst_result(inst).is_some()),
                                );
                            }
                        }
                    });

                    let mut call_choices: Vec<(InstId, CallPreserveChoice)> =
                        st.call_choice.iter().map(|(i, c)| (*i, *c)).collect();
                    call_choices.sort_unstable_by_key(|(i, _)| i.as_u32());

                    for (inst, choice) in call_choices {
                        let (callee, has_return) =
                            call_info.get(&inst).copied().unwrap_or_else(|| {
                                panic!("missing call info for inst {}", inst.as_u32())
                            });
                        let callee_name = module.ctx.func_sig(callee, |sig| sig.name().to_string());
                        let callee_need_words = section
                            .plan
                            .funcs
                            .get(&callee)
                            .and_then(|p| match &p.scheme {
                                MemScheme::StaticArena(st) => Some(st.need_words),
                                MemScheme::DynamicFrame => None,
                            })
                            .unwrap_or(0);

                        let save_offsets = st
                            .call_saves
                            .get(&inst)
                            .map(|p| p.save_word_offsets.as_slice())
                            .unwrap_or(&[]);

                        if save_offsets.is_empty() {
                            writeln!(
                                &mut out,
                                "  call inst{} callee=%{callee_name} callee_need_words={callee_need_words} choice={choice:?} has_return={has_return} save_words=0",
                                inst.as_u32()
                            )
                            .expect("mem plan write failed");
                        } else {
                            writeln!(
                                &mut out,
                                "  call inst{} callee=%{callee_name} callee_need_words={callee_need_words} choice={choice:?} has_return={has_return} save_words={} save_offsets={save_offsets:?}",
                                inst.as_u32(),
                                save_offsets.len(),
                            )
                            .expect("mem plan write failed");
                        }
                    }
                }

                let mut scratch_spills: Vec<(ValueId, u32)> = Vec::new();
                if let Some(alloc) = section.allocs.get(&func) {
                    module.func_store.view(func, |function| {
                        for v in function.dfg.values.keys() {
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
                    for v in function.dfg.values.keys() {
                        let Some(obj) = func_plan.spill_obj[v] else {
                            continue;
                        };
                        let offset_words = *func_plan
                            .obj_offset_words
                            .get(&obj)
                            .expect("missing stack object offset");
                        spills.push((v, offset_words, addr_of(offset_words)));
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
                        let offset_words = *func_plan
                            .alloca_offset_words
                            .get(&insn)
                            .expect("missing alloca plan");

                        let size_bytes = self
                            .isa
                            .type_layout()
                            .size_of(*alloca.ty(), &module.ctx)
                            .expect("alloca has invalid type")
                            as u32;
                        let size_words = size_bytes.div_ceil(WORD_BYTES);

                        allocas.push((value, offset_words, size_words, addr_of(offset_words)));
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

    fn take_prepared_function(&self, func: FuncRef) -> Option<PreparedLowering> {
        let mut state = self.section_state.borrow_mut();
        let section = state.as_mut()?;

        let alloc = section.allocs.remove(&func)?;
        let block_order = section.block_orders.remove(&func)?;
        let mem_plan = section.plan.funcs.get(&func).cloned()?;

        Some(PreparedLowering {
            alloc,
            block_order,
            mem_plan,
        })
    }

    fn dyn_base(&self) -> u32 {
        self.section_state
            .borrow()
            .as_ref()
            .map(|s| s.plan.dyn_base)
            .unwrap_or(STATIC_BASE)
    }

    fn lower_prepared_function(
        &self,
        module: &Module,
        func: FuncRef,
        prepared: PreparedLowering,
    ) -> Result<LoweredFunction<OpCode>, String> {
        let mem_plan = prepared.mem_plan;

        let vcode = module.func_store.view(func, |function| {
            let _plan_guard = CurrentMemPlanGuard::new(&self.current_mem_plan, mem_plan.clone());
            let mut alloc = FinalAlloc::new(prepared.alloc, mem_plan);
            let lower = Lower::new(&module.ctx, function, &prepared.block_order);
            lower.lower(self, &mut alloc).map_err(|e| format!("{e:?}"))
        })?;

        Ok(LoweredFunction {
            vcode,
            block_order: prepared.block_order,
        })
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

impl LowerBackend for EvmBackend {
    type MInst = OpCode;
    type Error = String;
    type FixupPolicy = PushWidthPolicy;

    fn prepare_section(
        &self,
        module: &Module,
        funcs: &[FuncRef],
        _section_ctx: &SectionLoweringCtx<'_>,
    ) {
        let ptr_escape = compute_ptr_escape_summaries(module, funcs, &self.isa);

        // Pre-pass: insert free-ptr restore (conservative: treat all calls as barriers).
        for &func in funcs {
            module.func_store.modify(func, |function| {
                prepare_free_ptr_restore(function, &module.ctx, self, &ptr_escape);
            });
        }

        // Scratch fixed point: scratch spills depend on transitive scratch barriers.
        let mut scratch_spill_funcs: FxHashSet<FuncRef> = FxHashSet::default();
        let mut scratch_effects = scratch_effects::compute_scratch_effects(
            module,
            funcs,
            &scratch_spill_funcs,
            &self.isa,
        );

        let mut analyses: FxHashMap<FuncRef, memory_plan::FuncAnalysis> = FxHashMap::default();

        loop {
            analyses.clear();
            let mut new_scratch_spill_funcs: FxHashSet<FuncRef> = FxHashSet::default();

            for &func in funcs {
                let analysis = module.func_store.modify(func, |function| {
                    prepare_stackify_analysis(
                        function,
                        &module.ctx,
                        self,
                        &ptr_escape,
                        Some(&scratch_effects),
                    )
                });
                if analysis.alloc.uses_scratch_spills() {
                    new_scratch_spill_funcs.insert(func);
                }
                analyses.insert(func, analysis);
            }

            if new_scratch_spill_funcs == scratch_spill_funcs {
                break;
            }

            scratch_spill_funcs = new_scratch_spill_funcs;
            scratch_effects = scratch_effects::compute_scratch_effects(
                module,
                funcs,
                &scratch_spill_funcs,
                &self.isa,
            );
        }

        let mut plan = compute_program_memory_plan(
            module,
            funcs,
            &analyses,
            &ptr_escape,
            &self.isa,
            &self.arena_cost_model,
        );

        let mem_effects =
            compute_func_mem_effects(module, funcs, &plan, &scratch_effects, &self.isa);

        for &func in funcs {
            let analysis = analyses.get(&func).expect("missing analysis");
            let transient_mallocs = module.func_store.view(func, |function| {
                malloc_plan::compute_transient_mallocs(
                    function,
                    &module.ctx,
                    &self.isa,
                    &ptr_escape,
                    Some(&mem_effects),
                    &analysis.inst_liveness,
                )
            });
            if let Some(mem_plan) = plan.funcs.get_mut(&func) {
                mem_plan.transient_mallocs = transient_mallocs;
            }
        }

        let malloc_bounds = heap_plan::compute_malloc_future_static_words(
            module, funcs, &plan, &analyses, &self.isa,
        );
        for (func, bounds) in malloc_bounds {
            if let Some(mem_plan) = plan.funcs.get_mut(&func) {
                mem_plan.malloc_future_static_words = bounds;
            }
        }

        if std::env::var_os("SONATINA_EVM_MEM_DEBUG").is_some() {
            debug_print_mem_plan(module, funcs, &plan);
        }

        let mut allocs: FxHashMap<FuncRef, StackifyAlloc> = FxHashMap::default();
        let mut block_orders: FxHashMap<FuncRef, Vec<BlockId>> = FxHashMap::default();
        for (func, analysis) in analyses {
            allocs.insert(func, analysis.alloc);
            block_orders.insert(func, analysis.block_order);
        }

        *self.section_state.borrow_mut() = Some(PreparedSection {
            plan,
            allocs,
            block_orders,
        });
    }

    fn lower_function(
        &self,
        module: &Module,
        func: FuncRef,
        section_ctx: &SectionLoweringCtx<'_>,
    ) -> Result<LoweredFunction<Self::MInst>, Self::Error> {
        let _ = section_ctx;

        if let Some(prepared) = self.take_prepared_function(func) {
            return self.lower_prepared_function(module, func, prepared);
        }

        let ptr_escape =
            compute_ptr_escape_summaries(module, std::slice::from_ref(&func), &self.isa);

        module.func_store.modify(func, |function| {
            prepare_free_ptr_restore(function, &module.ctx, self, &ptr_escape);
        });

        let analysis = module.func_store.modify(func, |function| {
            prepare_stackify_analysis(function, &module.ctx, self, &ptr_escape, None)
        });

        let layout = module.func_store.view(func, |function| {
            static_arena_alloc::plan_func_objects(
                func,
                function,
                &module.ctx,
                &self.isa,
                &ptr_escape,
                &analysis.alloc,
                &analysis.inst_liveness,
                &analysis.block_order,
                |_| None,
            )
        });

        let lowering = PreparedLowering {
            alloc: analysis.alloc,
            block_order: analysis.block_order,
            mem_plan: FuncMemPlan {
                scheme: MemScheme::DynamicFrame,
                obj_offset_words: layout.obj_offset_words,
                alloca_offset_words: layout.alloca_offset_words,
                spill_obj: layout.spill_obj,
                locals_words: layout.locals_words,
                malloc_future_static_words: FxHashMap::default(),
                transient_mallocs: FxHashSet::default(),
            },
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
        enter_frame(ctx, alloc.frame_size_slots(), self.dyn_base());
        perform_actions(ctx, &alloc.enter_function(function));
    }

    fn enter_block(
        &self,
        ctx: &mut Lower<Self::MInst>,
        _alloc: &mut dyn Allocator,
        _block: BlockId,
    ) {
        // Every block start is a jumpdest unless
        //  - all incoming edges are fallthroughs (TODO)
        //  - it's the entry block of the main fn (TODO)
        ctx.push(OpCode::JUMPDEST);
    }

    fn lower(&self, ctx: &mut Lower<Self::MInst>, alloc: &mut dyn Allocator, insn: InstId) {
        let result = ctx.insn_result(insn);
        let args = ctx.insn_data(insn).collect_values();
        let data = self.isa.inst_set().resolve_inst(ctx.insn_data(insn));

        let basic_op = |ctx: &mut Lower<Self::MInst>, ops: &[OpCode]| {
            perform_actions(ctx, &alloc.read(insn, &args));
            for op in ops {
                ctx.push(*op);
            }
            perform_actions(ctx, &alloc.write(insn, result));
        };

        match &data {
            EvmInstKind::Neg(_) => basic_op(ctx, &[OpCode::PUSH0, OpCode::SUB]),
            EvmInstKind::Add(_) => basic_op(ctx, &[OpCode::ADD]),
            EvmInstKind::Mul(_) => basic_op(ctx, &[OpCode::MUL]),
            EvmInstKind::Sub(_) => basic_op(ctx, &[OpCode::SUB]),
            EvmInstKind::Shl(_) => basic_op(ctx, &[OpCode::SHL]),
            EvmInstKind::Shr(_) => basic_op(ctx, &[OpCode::SHR]),
            EvmInstKind::Sar(_) => basic_op(ctx, &[OpCode::SAR]),
            EvmInstKind::Sext(_sext) => {
                let from = args[0];
                let src_ty = ctx.value_ty(from);
                let src_bits = scalar_bit_width(src_ty, ctx.module).unwrap_or(256);

                perform_actions(ctx, &alloc.read(insn, &args));

                // `i1` is treated as a boolean; sext is equivalent to zext.
                if src_bits == 1 {
                    push_bytes(ctx, &[1]);
                    ctx.push(OpCode::AND);
                } else if (8..256).contains(&src_bits) {
                    let src_bytes = (src_bits / 8) as u8;
                    debug_assert!(src_bytes > 0 && src_bytes <= 32);
                    // `SIGNEXTEND` takes (byte_index, value) with `byte_index` at top of stack.
                    push_bytes(ctx, &[src_bytes - 1]);
                    ctx.push(OpCode::SIGNEXTEND);
                }

                perform_actions(ctx, &alloc.write(insn, result));
            }
            EvmInstKind::Zext(_) => {
                let from = args[0];
                let src_ty = ctx.value_ty(from);
                let src_bits = scalar_bit_width(src_ty, ctx.module).unwrap_or(256);

                perform_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(src_bits) {
                    let bytes = u256_to_be(&mask);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::AND);
                }
                perform_actions(ctx, &alloc.write(insn, result));
            }

            EvmInstKind::Trunc(trunc) => {
                let dst_ty = *trunc.ty();
                let dst_bits = scalar_bit_width(dst_ty, ctx.module).unwrap_or(256);

                perform_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(dst_bits) {
                    let bytes = u256_to_be(&mask);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::AND);
                }
                perform_actions(ctx, &alloc.write(insn, result));
            }
            EvmInstKind::Bitcast(_) => {
                // No-op.
                perform_actions(ctx, &alloc.read(insn, &args));
                perform_actions(ctx, &alloc.write(insn, result));
            }
            EvmInstKind::IntToPtr(_) => {
                // Pointers are represented as 256-bit integers on the EVM.
                let from = args[0];
                let src_ty = ctx.value_ty(from);
                let src_bits = scalar_bit_width(src_ty, ctx.module).unwrap_or(256);

                perform_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(src_bits) {
                    let bytes = u256_to_be(&mask);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::AND);
                }
                perform_actions(ctx, &alloc.write(insn, result));
            }
            EvmInstKind::PtrToInt(ptr_to_int) => {
                let dst_ty = *ptr_to_int.ty();
                let dst_bits = scalar_bit_width(dst_ty, ctx.module).unwrap_or(256);

                perform_actions(ctx, &alloc.read(insn, &args));
                if let Some(mask) = low_bits_mask(dst_bits) {
                    let bytes = u256_to_be(&mask);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::AND);
                }
                perform_actions(ctx, &alloc.write(insn, result));
            }
            EvmInstKind::Lt(_) => basic_op(ctx, &[OpCode::LT]),
            EvmInstKind::Gt(_) => basic_op(ctx, &[OpCode::GT]),
            EvmInstKind::Slt(_) => basic_op(ctx, &[OpCode::SLT]),
            EvmInstKind::Sgt(_) => basic_op(ctx, &[OpCode::SGT]),
            EvmInstKind::Le(_) => basic_op(ctx, &[OpCode::GT, OpCode::ISZERO]),
            EvmInstKind::Ge(_) => basic_op(ctx, &[OpCode::LT, OpCode::ISZERO]),
            EvmInstKind::Sge(_) => basic_op(ctx, &[OpCode::SLT, OpCode::ISZERO]),
            EvmInstKind::Eq(_) => basic_op(ctx, &[OpCode::EQ]),
            EvmInstKind::Ne(_) => basic_op(ctx, &[OpCode::EQ, OpCode::ISZERO]),
            EvmInstKind::IsZero(_) => basic_op(ctx, &[OpCode::ISZERO]),

            EvmInstKind::Not(_) => basic_op(ctx, &[OpCode::NOT]),
            EvmInstKind::And(_) => basic_op(ctx, &[OpCode::AND]),
            EvmInstKind::Or(_) => basic_op(ctx, &[OpCode::OR]),
            EvmInstKind::Xor(_) => basic_op(ctx, &[OpCode::XOR]),

            EvmInstKind::Jump(jump) => {
                let dest = *jump.dest();
                perform_actions(ctx, &alloc.read(insn, &[]));

                if !ctx.is_next_block(dest) {
                    let push_op = ctx.push(OpCode::PUSH1);
                    ctx.add_label_reference(push_op, Label::Block(dest));
                    ctx.push(OpCode::JUMP);
                }
            }
            EvmInstKind::Br(br) => {
                let nz_dest = *br.nz_dest();
                let z_dest = *br.z_dest();

                // JUMPI: dest is top of stack, bool val is next
                perform_actions(ctx, &alloc.read(insn, &args));

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
            EvmInstKind::Phi(_) => {}

            EvmInstKind::BrTable(br) => {
                let table = br.table().clone();
                let scrutinee = *br.scrutinee();
                let default = *br.default();

                // TODO: sanitize br_table ops
                assert!(!table.is_empty(), "empty br_table");
                assert_eq!(
                    table.len(),
                    table.iter().map(|(v, _)| v).collect::<FxHashSet<_>>().len(),
                    "br_table has duplicate scrutinee values"
                );

                for (case_val, dest) in table.iter() {
                    perform_actions(ctx, &alloc.read(insn, &[scrutinee, *case_val]));
                    ctx.push(OpCode::EQ);

                    ctx.push_jump_target(OpCode::PUSH1, Label::Block(*dest));
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
                // xxx if func uses memory, store new fp

                let callee = *call.callee();
                let mut actions = alloc.read(insn, &args);

                let Some(cont_pos) = actions
                    .iter()
                    .position(|a| matches!(a, Action::PushContinuationOffset))
                else {
                    panic!("call lowering expected Action::PushContinuationOffset");
                };

                // Some allocators need to run block-entry prologues before pushing the
                // continuation address for the call. We therefore allow the marker to
                // appear anywhere in the action list and split around it.
                let suffix: SmallVec<[Action; 2]> = actions.drain(cont_pos + 1..).collect();
                debug_assert_eq!(
                    actions.remove(cont_pos),
                    Action::PushContinuationOffset,
                    "expected continuation marker at split point"
                );

                // Prefix actions run before the continuation address is pushed.
                perform_actions(ctx, &actions);

                // Push the return pc / continuation address.
                let push_callback = ctx.push(OpCode::PUSH1);

                // Move fn args onto stack
                perform_actions(ctx, &suffix);

                // Push fn address onto stack and jump
                let p = ctx.push(OpCode::PUSH1);
                ctx.add_label_reference(p, Label::Function(callee));
                ctx.push(OpCode::JUMP);

                // Mark return pc as jumpdest
                let jumpdest_op = ctx.push(OpCode::JUMPDEST);
                ctx.add_label_reference(push_callback, Label::Insn(jumpdest_op));

                // Post-call: spill the call result if needed.
                perform_actions(ctx, &alloc.write(insn, result));
            }

            EvmInstKind::Return(_) => {
                perform_actions(ctx, &alloc.read(insn, &args));
                leave_frame(ctx, alloc.frame_size_slots());

                // Caller pushes return location onto stack prior to call.
                if !args.is_empty() {
                    // Swap the return loc to the top.
                    ctx.push(OpCode::SWAP1);
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

                perform_actions(ctx, &alloc.read(insn, &args));
                if ty_size == 0 {
                    // TODO: optimize away mstores of size 0
                    // Pop the args, and don't do an mstore.
                    ctx.push(OpCode::POP);
                    ctx.push(OpCode::POP);
                } else {
                    debug_assert_eq!(ty_size, 32, "word-slot model: expected 32-byte store");
                    ctx.push(OpCode::MSTORE);
                }
            }
            EvmInstKind::EvmMcopy(_) => basic_op(ctx, &[OpCode::MCOPY]),
            EvmInstKind::Gep(_) => {
                perform_actions(ctx, &alloc.read(insn, &args));
                if args.is_empty() {
                    panic!("gep without operands");
                }

                let mut current_ty = ctx.value_ty(args[0]);
                if !current_ty.is_pointer(ctx.module) {
                    panic!("gep base must be a pointer (got {current_ty:?})");
                }

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
                            current_ty = elem_ty;
                        }
                        CompoundType::Array { elem, .. } => {
                            let elem_size = u32::try_from(ctx.module.size_of_unchecked(elem))
                                .expect("gep element too large");
                            steps.push(gep_step(elem_size, idx_imm_u32));
                            current_ty = elem;
                        }
                        CompoundType::Struct(s) => {
                            let Some(idx) = idx_imm_u32.map(|idx| idx as usize) else {
                                panic!("struct gep indices must be immediate constants");
                            };
                            let (field_offset, field_ty) =
                                struct_field_offset_bytes(&s.fields, s.packed, idx, ctx.module);
                            steps.push(GepStep::AddConst(field_offset));
                            current_ty = field_ty;
                        }
                        CompoundType::Func { .. } => {
                            panic!("invalid gep: indexing into function type");
                        }
                    }
                }

                for step in steps {
                    match step {
                        GepStep::AddConst(offset_bytes) => {
                            ctx.push(OpCode::SWAP1);
                            ctx.push(OpCode::POP);
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

                perform_actions(ctx, &alloc.write(insn, result));
            }
            EvmInstKind::Alloca(_) => {
                let mem_plan = self.current_mem_plan.borrow();
                let mem_plan = mem_plan
                    .as_ref()
                    .expect("missing memory plan during lowering");

                let offset_words = *mem_plan
                    .alloca_offset_words
                    .get(&insn)
                    .expect("missing alloca plan");

                perform_actions(ctx, &alloc.read(insn, &args));

                match &mem_plan.scheme {
                    MemScheme::StaticArena(_) => {
                        let addr_bytes = STATIC_BASE
                            .checked_add(
                                offset_words
                                    .checked_mul(WORD_BYTES)
                                    .expect("alloca address bytes overflow"),
                            )
                            .expect("alloca address bytes overflow");
                        push_bytes(ctx, &u32_to_be(addr_bytes));
                    }
                    MemScheme::DynamicFrame => {
                        let addr_bytes = offset_words
                            .checked_mul(WORD_BYTES)
                            .expect("alloca address bytes overflow");
                        push_bytes(ctx, &[DYN_FP_SLOT]);
                        ctx.push(OpCode::MLOAD);
                        if addr_bytes != 0 {
                            push_bytes(ctx, &u32_to_be(addr_bytes));
                            ctx.push(OpCode::ADD);
                        }
                    }
                }

                perform_actions(ctx, &alloc.write(insn, result));
            }

            EvmInstKind::EvmStop(_) => basic_op(ctx, &[OpCode::STOP]),

            EvmInstKind::EvmSdiv(_) => basic_op(ctx, &[OpCode::SDIV]),
            EvmInstKind::EvmUdiv(_) => basic_op(ctx, &[OpCode::DIV]),
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
                let future_words = mem_plan
                    .malloc_future_static_words
                    .get(&insn)
                    .copied()
                    .unwrap_or(dyn_base_words);

                let min_base_bytes = STATIC_BASE
                    .checked_add(
                        WORD_BYTES
                            .checked_mul(future_words)
                            .expect("malloc static bound bytes overflow"),
                    )
                    .expect("malloc static bound bytes overflow");

                perform_actions(ctx, &alloc.read(insn, &args));

                if is_transient {
                    // Drop the requested size; this is a transient bump allocation that does not
                    // update `FREE_PTR_SLOT` and is allowed to overlap with later allocations.
                    ctx.push(OpCode::POP);

                    // heap_end = mload(0x40)
                    push_bytes(ctx, &[FREE_PTR_SLOT]);
                    ctx.push(OpCode::MLOAD);

                    // sp = mload(DYN_SP_SLOT)
                    push_bytes(ctx, &[DYN_SP_SLOT]);
                    ctx.push(OpCode::MLOAD);

                    // max(heap_end, sp)
                    emit_max_top_two(ctx);

                    // max(max(heap_end, sp), min_base)
                    push_bytes(ctx, &u32_to_be(min_base_bytes));
                    emit_max_top_two(ctx);

                    perform_actions(ctx, &alloc.write(insn, result));
                    return;
                }

                // Align to 32 bytes:
                // aligned = (size + 31) & !31
                push_bytes(ctx, &[0x1f]);
                ctx.push(OpCode::ADD);
                push_bytes(ctx, &[0x1f]);
                ctx.push(OpCode::NOT);
                ctx.push(OpCode::AND);

                // heap_end = mload(0x40)
                push_bytes(ctx, &[FREE_PTR_SLOT]);
                ctx.push(OpCode::MLOAD);

                // sp = mload(DYN_SP_SLOT)
                push_bytes(ctx, &[DYN_SP_SLOT]);
                ctx.push(OpCode::MLOAD);

                // max(heap_end, sp)
                emit_max_top_two(ctx);

                // max(max(heap_end, sp), min_base)
                push_bytes(ctx, &u32_to_be(min_base_bytes));
                emit_max_top_two(ctx);

                // new_end = base + aligned_size; mstore(0x40, new_end); return base
                ctx.push(OpCode::DUP1);
                ctx.push(OpCode::SWAP2);
                ctx.push(OpCode::ADD);
                push_bytes(ctx, &[FREE_PTR_SLOT]);
                ctx.push(OpCode::MSTORE);

                perform_actions(ctx, &alloc.write(insn, result));
            }
            EvmInstKind::InsertValue(_) => todo!(),
            EvmInstKind::ExtractValue(_) => todo!(),
            EvmInstKind::GetFunctionPtr(get_fn) => {
                let func = *get_fn.func();
                perform_actions(ctx, &alloc.read(insn, &args));
                ctx.push_jump_target(OpCode::PUSH1, Label::Function(func));
                perform_actions(ctx, &alloc.write(insn, result));
            }
            EvmInstKind::EvmInvalid(_) => basic_op(ctx, &[OpCode::INVALID]),

            EvmInstKind::SymAddr(sym_addr) => {
                let sym = sym_addr.sym().clone();
                perform_actions(ctx, &alloc.read(insn, &args));
                ctx.push_sym_fixup(
                    OpCode::PUSH0,
                    SymFixup {
                        kind: SymFixupKind::Addr,
                        sym,
                    },
                );
                perform_actions(ctx, &alloc.write(insn, result));
            }
            EvmInstKind::SymSize(sym_size) => {
                let sym = sym_size.sym().clone();
                perform_actions(ctx, &alloc.read(insn, &args));
                ctx.push_sym_fixup(
                    OpCode::PUSH0,
                    SymFixup {
                        kind: SymFixupKind::Size,
                        sym,
                    },
                );
                perform_actions(ctx, &alloc.write(insn, result));
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

    fn inject_call_save_pre(
        &self,
        inst: InstId,
        operand_count: usize,
        actions: Actions,
    ) -> Actions {
        let MemScheme::StaticArena(st) = &self.mem_plan.scheme else {
            return actions;
        };
        let Some(plan) = st.call_saves.get(&inst) else {
            return actions;
        };
        if plan.save_word_offsets.is_empty() {
            return actions;
        }

        assert!(
            operand_count <= 16,
            "call operand count exceeds SWAP16: {operand_count}"
        );
        let Some(cont_pos) = actions
            .iter()
            .position(|a| matches!(a, Action::PushContinuationOffset))
        else {
            panic!("call save expected Action::PushContinuationOffset");
        };

        let mut out = Actions::new();
        for (idx, act) in actions.into_iter().enumerate() {
            if idx == cont_pos {
                for &w in &plan.save_word_offsets {
                    out.push(Action::MemLoadAbs(self.abs_addr_for_word(w)));
                    if operand_count != 0 {
                        for depth in (1..=operand_count).rev() {
                            out.push(Action::StackSwap(
                                u8::try_from(depth).expect("swap depth too large"),
                            ));
                        }
                    }
                }
            }
            out.push(act);
        }
        out
    }

    fn inject_call_save_post(&self, inst: InstId, actions: Actions) -> Actions {
        let MemScheme::StaticArena(st) = &self.mem_plan.scheme else {
            return actions;
        };
        let Some(plan) = st.call_saves.get(&inst) else {
            return actions;
        };
        if plan.save_word_offsets.is_empty() {
            return actions;
        }

        let mut restore: Actions = Actions::new();
        let mut stack_order: Vec<u32> = plan.save_word_offsets.iter().copied().rev().collect();

        if plan.has_return {
            while !stack_order.is_empty() {
                let m = stack_order.len().min(16);
                restore.push(Action::StackSwap(m as u8));

                // After SWAPm, the deepest saved word in this chunk is on top, followed by the
                // remaining (m-1) saved words, then the return value.
                let deepest = stack_order[m - 1];
                restore.push(Action::MemStoreAbs(self.abs_addr_for_word(deepest)));
                for &w in stack_order.iter().take(m - 1) {
                    restore.push(Action::MemStoreAbs(self.abs_addr_for_word(w)));
                }

                stack_order.drain(..m);
            }
        } else {
            for w in stack_order {
                restore.push(Action::MemStoreAbs(self.abs_addr_for_word(w)));
            }
        }

        let mut out: Actions = Actions::new();
        out.extend(restore);
        out.extend(actions);
        out
    }

    fn rewrite_actions(&self, mut actions: Actions) -> Actions {
        for action in actions.iter_mut() {
            match action {
                Action::MemLoadObj(id) => {
                    // Invariant: every stackify `Mem*Obj` must have a planned offset.
                    // Should be checked by a post-plan verifier.
                    let off = *self.mem_plan.obj_offset_words.get(id).unwrap_or_else(|| {
                        panic!("missing stack object offset for obj {}", id.as_u32())
                    });
                    *action = match &self.mem_plan.scheme {
                        MemScheme::StaticArena(_) => Action::MemLoadAbs(
                            STATIC_BASE
                                .checked_add(
                                    off.checked_mul(WORD_BYTES)
                                        .expect("stack object addr bytes overflow"),
                                )
                                .expect("stack object addr bytes overflow"),
                        ),
                        MemScheme::DynamicFrame => Action::MemLoadFrameSlot(off),
                    };
                }
                Action::MemStoreObj(id) => {
                    // Invariant: every stackify `Mem*Obj` must have a planned offset.
                    // Should be checked by a post-plan verifier.
                    let off = *self.mem_plan.obj_offset_words.get(id).unwrap_or_else(|| {
                        panic!("missing stack object offset for obj {}", id.as_u32())
                    });
                    *action = match &self.mem_plan.scheme {
                        MemScheme::StaticArena(_) => Action::MemStoreAbs(
                            STATIC_BASE
                                .checked_add(
                                    off.checked_mul(WORD_BYTES)
                                        .expect("stack object addr bytes overflow"),
                                )
                                .expect("stack object addr bytes overflow"),
                        ),
                        MemScheme::DynamicFrame => Action::MemStoreFrameSlot(off),
                    };
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
        match self.mem_plan.scheme {
            MemScheme::StaticArena(_) => 0,
            MemScheme::DynamicFrame => self.mem_plan.locals_words,
        }
    }

    fn read(&self, inst: InstId, vals: &[sonatina_ir::ValueId]) -> Actions {
        let actions = self.inner.read(inst, vals);
        let actions = self.inject_call_save_pre(inst, vals.len(), actions);
        self.rewrite_actions(actions)
    }

    fn write(&self, inst: InstId, val: Option<sonatina_ir::ValueId>) -> Actions {
        let actions = self.inner.write(inst, val);
        let actions = self.inject_call_save_post(inst, actions);
        self.rewrite_actions(actions)
    }

    fn traverse_edge(&self, from: BlockId, to: BlockId) -> Actions {
        self.rewrite_actions(self.inner.traverse_edge(from, to))
    }
}

enum GepStep {
    AddConst(u32),
    AddScaled(u32),
}

fn gep_step(elem_size_bytes: u32, idx: Option<u32>) -> GepStep {
    let Some(idx) = idx else {
        return if elem_size_bytes == 0 {
            GepStep::AddConst(0)
        } else {
            GepStep::AddScaled(elem_size_bytes)
        };
    };

    GepStep::AddConst(
        elem_size_bytes
            .checked_mul(idx)
            .expect("gep offset overflow"),
    )
}

fn immediate_u32(imm: Immediate) -> Option<u32> {
    if imm.is_negative() {
        return None;
    }

    let u256 = imm.as_i256().to_u256();
    if u256 > U256::from(u32::MAX) {
        return None;
    }

    Some(u256.low_u32())
}

fn struct_field_offset_bytes(
    fields: &[Type],
    packed: bool,
    idx: usize,
    module: &ModuleCtx,
) -> (u32, Type) {
    let &field_ty = fields.get(idx).expect("struct gep index out of bounds");

    let mut offset: u32 = 0;
    for &ty in fields.iter().take(idx) {
        if !packed {
            let align =
                u32::try_from(module.align_of_unchecked(ty)).expect("struct field align too large");
            offset = align_to(offset, align);
        }

        let size =
            u32::try_from(module.size_of_unchecked(ty)).expect("struct field size too large");
        offset = offset
            .checked_add(size)
            .expect("struct field offset overflow");
    }

    if !packed {
        let align = u32::try_from(module.align_of_unchecked(field_ty))
            .expect("struct field align too large");
        offset = align_to(offset, align);
    }

    (offset, field_ty)
}

fn align_to(offset: u32, align: u32) -> u32 {
    if align <= 1 {
        return offset;
    }
    debug_assert!(align.is_power_of_two(), "alignment must be power of two");

    offset.checked_add(align - 1).expect("align overflow") & !(align - 1)
}

fn perform_actions(ctx: &mut Lower<OpCode>, actions: &[Action]) {
    for action in actions {
        match action {
            Action::StackDup(slot) => {
                debug_assert!(*slot < 16, "DUP out of range: {slot}");
                ctx.push(dup_op(*slot));
            }
            Action::StackSwap(n) => {
                debug_assert!((1..=16).contains(n), "SWAP out of range: {n}");
                ctx.push(swap_op(*n));
            }
            Action::Push(imm) => {
                if imm.is_zero() {
                    ctx.push(OpCode::PUSH0);
                } else {
                    let bytes = match imm {
                        Immediate::I1(v) => smallvec![*v as u8],
                        Immediate::I8(v) => SmallVec::from_slice(&v.to_be_bytes()),
                        Immediate::I16(v) => shrink_bytes(&v.to_be_bytes()),
                        Immediate::I32(v) => shrink_bytes(&v.to_be_bytes()),
                        Immediate::I64(v) => shrink_bytes(&v.to_be_bytes()),
                        Immediate::I128(v) => shrink_bytes(&v.to_be_bytes()),
                        Immediate::I256(v) => shrink_bytes(&v.to_u256().to_big_endian()),
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
                let bytes = u32_to_be(*offset);
                push_bytes(ctx, &bytes);
                ctx.push(OpCode::MLOAD);
            }
            Action::MemLoadFrameSlot(offset) => {
                push_bytes(ctx, &[DYN_FP_SLOT]);
                ctx.push(OpCode::MLOAD);
                let byte_offset = offset
                    .checked_mul(WORD_BYTES)
                    .expect("frame slot offset overflow");
                if byte_offset != 0 {
                    let bytes = u32_to_be(byte_offset);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::ADD);
                }
                ctx.push(OpCode::MLOAD);
            }
            Action::MemStoreAbs(offset) => {
                let bytes = u32_to_be(*offset);
                push_bytes(ctx, &bytes);
                ctx.push(OpCode::MSTORE);
            }
            Action::MemStoreFrameSlot(offset) => {
                push_bytes(ctx, &[DYN_FP_SLOT]);
                ctx.push(OpCode::MLOAD);
                let byte_offset = offset
                    .checked_mul(WORD_BYTES)
                    .expect("frame slot offset overflow");
                if byte_offset != 0 {
                    let bytes = u32_to_be(byte_offset);
                    push_bytes(ctx, &bytes);
                    ctx.push(OpCode::ADD);
                }
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

fn emit_max_top_two(ctx: &mut Lower<OpCode>) {
    // Stack: [..., b, a] (a is top).
    // Result: [..., max(a, b)]
    ctx.push(OpCode::DUP2);
    ctx.push(OpCode::DUP2);
    ctx.push(OpCode::GT);

    let keep_a_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    // keep b (a <= b): drop a.
    ctx.push(OpCode::POP);
    let end_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMP);

    // keep a (a > b): drop b.
    let keep_a = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(keep_a_push, Label::Insn(keep_a));
    ctx.push(OpCode::SWAP1);
    ctx.push(OpCode::POP);

    let end = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(end_push, Label::Insn(end));
}

fn enter_frame(ctx: &mut Lower<OpCode>, frame_slots: u32, dyn_base: u32) {
    if frame_slots == 0 {
        return;
    }

    let frame_bytes = frame_slots
        .checked_mul(WORD_BYTES)
        .expect("frame size overflow");

    // sp = mload(DYN_SP_SLOT); if sp == 0, initialize it.
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MLOAD);

    // if sp != 0, skip init.
    ctx.push(OpCode::DUP1);
    ctx.push(OpCode::ISZERO);
    ctx.push(OpCode::ISZERO);
    let skip_init_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    // init: pop 0 sp; sp = dyn_base; mstore(DYN_SP_SLOT, sp)
    ctx.push(OpCode::POP);
    push_bytes(ctx, &u32_to_be(dyn_base));
    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);

    let skip_init = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(skip_init_push, Label::Insn(skip_init));

    // Clamp dynamic stack pointer above any heap allocations.
    push_bytes(ctx, &[FREE_PTR_SLOT]);
    ctx.push(OpCode::MLOAD);
    emit_max_top_two(ctx);

    // Save old fp at frame_base (sp): mstore(sp, mload(DYN_FP_SLOT))
    push_bytes(ctx, &[DYN_FP_SLOT]);
    ctx.push(OpCode::MLOAD);
    ctx.push(OpCode::DUP2);
    ctx.push(OpCode::MSTORE);

    // new_fp = sp + WORD_BYTES; mstore(DYN_FP_SLOT, new_fp)
    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &u32_to_be(WORD_BYTES));
    ctx.push(OpCode::ADD);
    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &[DYN_FP_SLOT]);
    ctx.push(OpCode::MSTORE);

    // new_sp = new_fp + frame_bytes; mstore(DYN_SP_SLOT, new_sp)
    if frame_bytes != 0 {
        push_bytes(ctx, &u32_to_be(frame_bytes));
        ctx.push(OpCode::ADD);
    }
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);

    // Discard frame_base (sp).
    ctx.push(OpCode::POP);
}

fn leave_frame(ctx: &mut Lower<OpCode>, frame_slots: u32) {
    if frame_slots == 0 {
        return;
    }

    // frame_base = fp - WORD_BYTES
    //
    // NOTE: `SUB` computes `a - b` with `a` on top of stack.
    push_bytes(ctx, &u32_to_be(WORD_BYTES));
    push_bytes(ctx, &[DYN_FP_SLOT]);
    ctx.push(OpCode::MLOAD);
    ctx.push(OpCode::SUB);

    // old_fp = mload(frame_base)
    ctx.push(OpCode::DUP1);
    ctx.push(OpCode::MLOAD);

    // mstore(DYN_FP_SLOT, old_fp)
    push_bytes(ctx, &[DYN_FP_SLOT]);
    ctx.push(OpCode::MSTORE);

    // mstore(DYN_SP_SLOT, frame_base)
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
    let mut cfg = ControlFlowGraph::new();
    cfg.compute(function);

    let mut splitter = CriticalEdgeSplitter::new();
    splitter.run(function, &mut cfg);

    let mut dom = DomTree::new();
    dom.compute(&cfg);

    let block_order = dom.rpo().to_owned();

    let mut liveness = Liveness::new();
    liveness.compute(function, &cfg);

    let mut inst_liveness = InstLiveness::new();
    inst_liveness.compute(function, &cfg, &liveness);

    let scratch_live_values = scratch_plan::compute_scratch_live_values(
        function,
        module,
        &backend.isa,
        ptr_escape,
        scratch_effects,
        &inst_liveness,
    );

    let alloc = StackifyAlloc::for_function_with_call_live_values_and_scratch_spills(
        function,
        &cfg,
        &dom,
        &liveness,
        backend.stackify_reach_depth,
        StackifyLiveValues {
            scratch_live_values,
        },
        scratch_plan::SCRATCH_SPILL_SLOTS,
    );

    memory_plan::FuncAnalysis {
        alloc,
        inst_liveness,
        block_order,
    }
}

fn debug_print_mem_plan(module: &Module, funcs: &[FuncRef], plan: &ProgramMemoryPlan) {
    let mut funcs_by_name: Vec<(String, FuncRef)> = funcs
        .iter()
        .copied()
        .map(|f| (module.ctx.func_sig(f, |sig| sig.name().to_string()), f))
        .collect();
    funcs_by_name.sort_unstable_by(|(a, _), (b, _)| a.cmp(b));

    eprintln!(
        "evm mem debug: dyn_base=0x{:x} static_base=0x{:x}",
        plan.dyn_base, STATIC_BASE
    );
    eprintln!("evm mem debug: entry_mem_init_stores=0");

    for (name, func) in funcs_by_name {
        let Some(func_plan) = plan.funcs.get(&func) else {
            continue;
        };
        let (scheme, need_words) = match &func_plan.scheme {
            MemScheme::StaticArena(st) => ("StaticArena", Some(st.need_words)),
            MemScheme::DynamicFrame => ("DynamicFrame", None),
        };

        let (malloc_min, malloc_max, malloc_count) =
            if func_plan.malloc_future_static_words.is_empty() {
                (None, None, 0)
            } else {
                let mut min: u32 = u32::MAX;
                let mut max: u32 = 0;
                for &w in func_plan.malloc_future_static_words.values() {
                    min = min.min(w);
                    max = max.max(w);
                }
                (
                    Some(min),
                    Some(max),
                    func_plan.malloc_future_static_words.len(),
                )
            };

        let static_end = need_words.map(|w| {
            STATIC_BASE
                .checked_add(w.checked_mul(WORD_BYTES).expect("static end overflow"))
                .expect("static end overflow")
        });

        eprintln!(
            "evm mem debug: {name} scheme={scheme} locals_words={} need_words={:?} malloc_bounds(min,max,count)=({:?},{:?},{malloc_count}) static_end={:?}",
            func_plan.locals_words, need_words, malloc_min, malloc_max, static_end
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
    use sonatina_ir::cfg::ControlFlowGraph;
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, TargetTriple, Vendor};

    #[test]
    fn call_save_pre_tucks_saved_words_below_operands() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %callee(v0.i256, v1.i256) -> i256 {
block0:
    v2.*i256 = alloca i256;
    mstore v2 v0 i256;
    v3.i256 = mload v2 i256;
    v4.i256 = add v3 v1;
    return v4;
}

func public %caller() -> i256 {
block0:
    v0.*i256 = alloca i256;
    mstore v0 1.i256 i256;
    v1.i256 = call %callee 11.i256 22.i256;
    v2.i256 = mload v0 i256;
    v3.i256 = add v1 v2;
    return v3;
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
                let alloc = StackifyAlloc::for_function(function, &cfg, &dom, &liveness, 16);

                analyses.insert(
                    func,
                    memory_plan::FuncAnalysis {
                        alloc,
                        inst_liveness,
                        block_order,
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

        let MemScheme::StaticArena(st) = &alloc.mem_plan.scheme else {
            panic!("expected StaticArena plan for caller");
        };
        let save_plan = st
            .call_saves
            .get(&call_inst)
            .expect("expected non-empty call_saves entry for call");
        assert!(
            !save_plan.save_word_offsets.is_empty(),
            "expected at least one saved word"
        );

        let actions = alloc.read(call_inst, &call_args);
        let cont_pos = actions
            .iter()
            .position(|a| matches!(a, Action::PushContinuationOffset))
            .expect("missing continuation marker");

        let arity = call_args.len();
        let expected_len = save_plan
            .save_word_offsets
            .len()
            .checked_mul(arity + 1)
            .expect("expected injected length overflow");
        assert!(
            cont_pos >= expected_len,
            "expected injected actions immediately before continuation marker"
        );
        let injected = &actions[cont_pos - expected_len..cont_pos];

        for (i, &w) in save_plan.save_word_offsets.iter().enumerate() {
            let base = i * (arity + 1);
            assert_eq!(
                injected[base],
                Action::MemLoadAbs(alloc.abs_addr_for_word(w))
            );
            for (j, depth) in (1..=arity).rev().enumerate() {
                assert_eq!(
                    injected[base + 1 + j],
                    Action::StackSwap(u8::try_from(depth).expect("swap depth too large"))
                );
            }
        }
    }
}
