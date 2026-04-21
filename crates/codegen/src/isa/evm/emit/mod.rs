mod alloc;
mod insn;
mod layout;
mod stack;

pub(crate) use alloc::FinalAlloc;
pub(crate) use layout::{
    LateBlockAliasPlan, compute_function_entry_jump_targets, compute_late_block_alias_plan,
    materialize_jumpdests, referenced_insn_label_targets, rewrite_evm_local_fallthrough_layout,
};
#[cfg(test)]
pub(crate) use stack::fold_stack_actions;
pub(crate) use stack::{
    immediate_u32, is_plain_inst, is_push_opcode, perform_actions,
    prune_redundant_opcode_sequences, push_op,
};

use tracing::trace_span;

use crate::{
    machinst::lower::{Lower, LoweredFunction},
    stackalloc::Allocator,
    transform::aggregate::assert_aggregate_legalized,
};
use sonatina_ir::{BlockId, Function, Module, module::FuncRef};

use self::stack::enter_frame_initialized;
use super::{
    DynSpInitKind, DynamicFrameLayout, EvmBackend, EvmFunctionPlan, EvmSectionPlan,
    LateCleanupProfile, late_block_merge::run_late_block_merge, opcode::OpCode,
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

    fn frame_layout(&self) -> Option<DynamicFrameLayout> {
        self.function_plan.mem_plan.dynamic_frame_layout()
    }

    fn emit_frame_enter(&self, ctx: &mut Lower<OpCode>, frame_layout: DynamicFrameLayout) {
        enter_frame_initialized(ctx, frame_layout);
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

    fn emit_actions(
        &self,
        ctx: &mut Lower<OpCode>,
        actions: &[crate::stackalloc::Action],
        frame_layout: Option<DynamicFrameLayout>,
    ) {
        perform_actions(ctx, actions, frame_layout);
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
        let frame_layout = self.frame_layout();
        let actions = alloc.enter_function(function);
        debug_assert!(
            !(self.function_plan.dyn_sp_plan.entry_live_frame
                && self.function_plan.dyn_sp_plan.entry_init == Some(DynSpInitKind::Always)),
            "entry with possible live-frame reentry cannot use unconditional dyn-sp init"
        );
        match self.function_plan.dyn_sp_plan.entry_init {
            None => {}
            Some(DynSpInitKind::Always) => stack::init_dyn_sp(ctx, self.dyn_base()),
            Some(DynSpInitKind::Checked) => stack::ensure_dyn_sp_init(ctx, self.dyn_base()),
        }

        if let Some(frame_layout) = frame_layout {
            self.emit_frame_enter(ctx, frame_layout);
        }
        self.emit_actions(ctx, &actions, frame_layout);
    }

    fn enter_block(&self, _: &mut Lower<OpCode>, _: &mut dyn Allocator, _: BlockId) {}
}
