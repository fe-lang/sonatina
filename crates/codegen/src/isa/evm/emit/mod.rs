mod alloc;
mod insn;
mod layout;
mod stack;

pub(crate) use alloc::FinalAlloc;
pub(crate) use layout::{
    LateBlockAliasPlan, compute_function_entry_jump_targets, compute_late_block_alias_plan,
    materialize_jumpdests, referenced_insn_label_targets, rewrite_evm_local_fallthrough_layout,
};
pub(crate) use stack::{
    fold_stack_actions, frame_slot_sp_relative_bytes, immediate_u32, is_plain_inst, is_push_opcode,
    perform_actions, prune_redundant_opcode_sequences, push_op,
};

use tracing::trace_span;

use crate::{
    machinst::lower::{Lower, LoweredFunction},
    stackalloc::{Action, Allocator},
    transform::aggregate::assert_aggregate_legalized,
};
use sonatina_ir::{BlockId, Function, InstId, Module, module::FuncRef};

use self::stack::{enter_frame_initialized, leave_frame, perform_action};
use super::{
    EvmBackend, EvmFunctionPlan, EvmSectionPlan, FrameSite, FrontierInitKind, LateCleanupProfile,
    LazyFramePlan, late_block_merge::run_late_block_merge, opcode::OpCode,
};

pub(crate) struct EvmFunctionLowering<'a> {
    backend: &'a EvmBackend,
    section_plan: &'a EvmSectionPlan,
    function_plan: &'a EvmFunctionPlan,
}

impl<'a> EvmFunctionLowering<'a> {
    pub(crate) fn new(
        backend: &'a EvmBackend,
        section_plan: &'a EvmSectionPlan,
        function_plan: &'a EvmFunctionPlan,
    ) -> Self {
        Self {
            backend,
            section_plan,
            function_plan,
        }
    }

    fn dyn_base(&self) -> u32 {
        self.section_plan.dyn_base
    }

    fn emit_frame_enter(&self, ctx: &mut Lower<OpCode>, frame_size_slots: u32) {
        enter_frame_initialized(ctx, frame_size_slots);
    }

    fn lazy_frame_plan_matches(&self, pred: impl FnOnce(&LazyFramePlan) -> bool) -> bool {
        self.function_plan
            .frame_summary
            .lowering
            .as_ref()
            .is_some_and(pred)
    }

    fn has_lazy_frame_lowering(&self) -> bool {
        self.function_plan.frame_summary.lowering.is_some()
    }

    fn local_frame_active_before_inst(&self, inst: InstId) -> bool {
        self.function_plan
            .frame_summary
            .local_frame_active_before_inst(inst)
    }

    fn frontier_init_kind(&self, inst: InstId) -> Option<FrontierInitKind> {
        let plan = &self.function_plan.dyn_sp_plan;
        if plan.checked_frontier_init_calls.contains(&inst) {
            Some(FrontierInitKind::Checked)
        } else if plan.frontier_init_calls.contains(&inst) {
            Some(FrontierInitKind::Always)
        } else {
            None
        }
    }

    fn malloc_needs_dyn_sp_clamp(&self, inst: InstId) -> bool {
        self.function_plan.dyn_sp_plan.entry_live_frame || self.local_frame_active_before_inst(inst)
    }

    fn canonical_block_target(&self, block: BlockId) -> BlockId {
        self.function_plan
            .block_aliases
            .get(&block)
            .copied()
            .unwrap_or(block)
    }

    fn is_elided_block(&self, block: BlockId) -> bool {
        self.function_plan.block_aliases.contains_key(&block)
    }

    fn emit_lazy_frame_enter_if_site_matches(
        &self,
        ctx: &mut Lower<OpCode>,
        frame_size_slots: u32,
        site: FrameSite,
    ) {
        if self.lazy_frame_plan_matches(|plan| plan.enter_before_site(site)) {
            self.emit_frame_enter(ctx, frame_size_slots);
        }
    }

    fn emit_lazy_frame_leave_if_site_matches(
        &self,
        ctx: &mut Lower<OpCode>,
        frame_size_slots: u32,
        site: FrameSite,
    ) {
        if self.lazy_frame_plan_matches(|plan| plan.exit_before_site(site)) {
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
            if self.lazy_frame_plan_matches(|plan| plan.enter_before_action(site, index)) {
                self.emit_frame_enter(ctx, frame_size_slots);
            }
            if self.lazy_frame_plan_matches(|plan| plan.exit_before_action(site, index)) {
                leave_frame(ctx, frame_size_slots);
            }
            perform_action(ctx, action, frame_size_slots);
            if self.lazy_frame_plan_matches(|plan| plan.exit_after_action(site, index)) {
                leave_frame(ctx, frame_size_slots);
            }
        }

        if self.lazy_frame_plan_matches(|plan| plan.exit_after_site(site)) {
            leave_frame(ctx, frame_size_slots);
        }
    }

    pub(crate) fn lower_prepared_function(
        &self,
        module: &Module,
        func: FuncRef,
    ) -> Result<LoweredFunction<OpCode>, String> {
        let mut emitted_block_order = self.function_plan.emitted_block_order.clone();
        let _span = trace_span!(
            "sonatina.codegen.evm.lower_prepared_function",
            func_ref = func.as_u32(),
            blocks = emitted_block_order.len()
        )
        .entered();
        module.func_store.view(func, |function| {
            assert_aggregate_legalized(function, &module.ctx);
        });
        let mut vcode = {
            let _span = trace_span!("sonatina.codegen.evm.lower_prepared_function.lower").entered();
            module.func_store.view(func, |function| {
                let mut alloc = FinalAlloc::new(
                    self.function_plan.alloc.clone(),
                    self.function_plan.mem_plan.clone(),
                );
                let lower = Lower::new(&module.ctx, function, &emitted_block_order);
                lower
                    .lower(
                        &mut alloc,
                        |ctx, alloc, block| self.enter_block(ctx, alloc, block),
                        |ctx, alloc, function| self.enter_function(ctx, alloc, function),
                        |ctx, alloc, insn| self.lower_insn(ctx, alloc, insn),
                    )
                    .map_err(|e| format!("{e:?}"))
            })?
        };
        {
            let _span =
                trace_span!("sonatina.codegen.evm.lower_prepared_function.prune_redundant_opcodes")
                    .entered();
            prune_redundant_opcode_sequences(&mut vcode, &emitted_block_order);
        }
        if self.backend.late_cleanup_profile != LateCleanupProfile::Off {
            let _span =
                trace_span!("sonatina.codegen.evm.lower_prepared_function.late_block_merge")
                    .entered();
            module.func_store.view(func, |function| {
                run_late_block_merge(
                    &mut vcode,
                    &mut emitted_block_order,
                    function
                        .layout
                        .entry_block()
                        .expect("prepared lowering requires an entry block"),
                    self.backend.late_cleanup_profile,
                );
            });
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
                    self.function_plan.function_entry_jumpdest,
                );
            });
        }

        Ok(LoweredFunction {
            vcode,
            block_order: emitted_block_order,
        })
    }

    fn enter_function(
        &self,
        ctx: &mut Lower<OpCode>,
        alloc: &mut dyn Allocator,
        function: &Function,
    ) {
        let frame_size_slots = alloc.frame_size_slots();
        let actions = alloc.enter_function(function);
        if self.function_plan.dyn_sp_plan.entry_init {
            if self.function_plan.dyn_sp_plan.entry_live_frame {
                stack::ensure_dyn_sp_init(ctx, self.dyn_base());
            } else {
                stack::init_dyn_sp(ctx, self.dyn_base());
            }
        }

        if self.has_lazy_frame_lowering() {
            self.emit_actions_for_site(ctx, &actions, frame_size_slots, FrameSite::EnterFunction);
        } else {
            self.emit_frame_enter(ctx, frame_size_slots);
            perform_actions(ctx, &actions, frame_size_slots);
        }
    }

    fn enter_block(&self, ctx: &mut Lower<OpCode>, alloc: &mut dyn Allocator, block: BlockId) {
        if self.is_elided_block(block) {
            return;
        }

        self.emit_lazy_frame_enter_if_site_matches(
            ctx,
            alloc.frame_size_slots(),
            FrameSite::BlockEntry(block),
        );
        self.emit_lazy_frame_leave_if_site_matches(
            ctx,
            alloc.frame_size_slots(),
            FrameSite::BlockEntry(block),
        );
    }
}
