use rustc_hash::FxHashMap;
use tracing::{debug_span, info_span, trace_span};

use crate::{
    machinst::lower::SectionWorkModule,
    optim::{
        dead_arg::{DeadArgElimConfig, run_dead_arg_elim},
        pipeline::{FuncPassOverrides, Pass, run_function_pass_round},
    },
    transform::{
        aggregate::{
            AggregateExpandAbi, AggregateLowerToMemoryLegalize, LocalObjectArgMap,
            ObjectAggregateAbi, ObjectEffectSummaryMap, ObjectLowerToMemory,
            assert_aggregate_legalized, collect_local_object_arg_info_with_effects,
            compute_object_effect_summaries, merge_local_object_arg_info,
        },
        evm::{ConstDataLower, legalize_evm_section},
    },
};
use sonatina_ir::{Module, module::FuncRef};

use super::{
    EvmBackend, LateCleanupProfile, PtrEscapeSummary, collect_unsupported_evm_multi_return,
    compute_ptr_escape_summaries, prepare_free_ptr_restore, validate_supported_lowering_ir,
};

pub(crate) struct EvmPipelineArtifacts {
    pub(crate) funcs: Vec<FuncRef>,
    pub(crate) ptr_escape: FxHashMap<FuncRef, PtrEscapeSummary>,
}

pub(crate) struct EvmPipeline<'a> {
    backend: &'a EvmBackend,
}

struct EvmPipelineContext<'a> {
    backend: &'a EvmBackend,
    work: &'a SectionWorkModule,
    funcs: Vec<FuncRef>,
    func_behavior_dirty: bool,
    synthetic_out_args: LocalObjectArgMap,
    local_object_args: Option<LocalObjectArgMap>,
    object_effects: Option<ObjectEffectSummaryMap>,
    ptr_escape: Option<FxHashMap<FuncRef, PtrEscapeSummary>>,
}

impl<'a> EvmPipeline<'a> {
    pub(crate) fn new(backend: &'a EvmBackend) -> Self {
        Self { backend }
    }

    pub(crate) fn run(&self, work: &'a SectionWorkModule) -> Result<EvmPipelineArtifacts, String> {
        let mut ctx = EvmPipelineContext {
            backend: self.backend,
            work,
            funcs: work.module().funcs(),
            func_behavior_dirty: true,
            synthetic_out_args: LocalObjectArgMap::default(),
            local_object_args: None,
            object_effects: None,
            ptr_escape: None,
        };
        let optional_cleanup = self.backend.late_cleanup_profile != LateCleanupProfile::Off;
        let _span = info_span!(
            "sonatina.codegen.evm.pipeline.run",
            funcs = ctx.funcs.len(),
            phases = if optional_cleanup { 9 } else { 5 }
        )
        .entered();

        ctx.run_phase(
            "enum_and_const_lowering",
            "mandatory",
            EvmPipelineContext::run_enum_and_const_lowering,
        )?;
        if optional_cleanup {
            ctx.run_phase(
                "object_combine",
                "optional",
                EvmPipelineContext::run_object_combine,
            )?;
        }
        ctx.run_phase(
            "object_aggregate_abi_lowering",
            "mandatory",
            EvmPipelineContext::run_object_aggregate_abi_lowering,
        )?;
        if optional_cleanup {
            ctx.run_phase(
                "object_cleanup",
                "optional",
                EvmPipelineContext::run_object_cleanup,
            )?;
        }
        ctx.run_phase(
            "object_abi_and_type_lowering",
            "mandatory",
            EvmPipelineContext::run_object_abi_and_type_lowering,
        )?;
        if optional_cleanup {
            ctx.run_phase(
                "aggregate_cleanup",
                "optional",
                EvmPipelineContext::run_aggregate_cleanup,
            )?;
        }
        ctx.run_phase(
            "validate_lowering_ir",
            "mandatory",
            EvmPipelineContext::run_validate_lowering_ir,
        )?;
        ctx.run_phase(
            "memory_legalization",
            "mandatory",
            EvmPipelineContext::run_memory_legalization,
        )?;
        if optional_cleanup {
            ctx.run_phase(
                "raw_memory_cleanup",
                "optional",
                EvmPipelineContext::run_raw_memory_cleanup,
            )?;
        }

        Ok(EvmPipelineArtifacts {
            funcs: ctx.funcs,
            ptr_escape: ctx
                .ptr_escape
                .ok_or_else(|| "missing ptr escape summaries after EVM pipeline".to_string())?,
        })
    }
}

impl EvmPipelineContext<'_> {
    fn module(&self) -> &Module {
        self.work.module()
    }

    fn run_phase<F>(
        &mut self,
        name: &'static str,
        kind: &'static str,
        phase: F,
    ) -> Result<(), String>
    where
        F: FnOnce(&mut Self) -> Result<(), String>,
    {
        let _span = debug_span!(
            "sonatina.codegen.evm.pipeline.phase",
            phase = name,
            kind = kind
        )
        .entered();
        phase(self)
    }

    fn run_pass_round(
        &mut self,
        mode: &'static str,
        passes: &[Pass],
        local_object_args: bool,
        object_effects: bool,
    ) {
        let _span = debug_span!(
            "sonatina.codegen.evm.pipeline.optimize",
            mode = mode,
            pass_count = passes.len()
        )
        .entered();
        let local_object_args = if local_object_args {
            self.local_object_args.as_ref()
        } else {
            None
        };
        let object_effects = if object_effects {
            self.object_effects.as_ref()
        } else {
            None
        };
        run_function_pass_round(
            self.work.module(),
            passes,
            &mut self.func_behavior_dirty,
            FuncPassOverrides {
                funcs: Some(self.funcs.as_slice()),
                local_object_args,
                object_effects,
            },
        );
        if object_effects.is_some() {
            self.object_effects = None;
        }
    }

    fn run_enum_and_const_lowering(&mut self) -> Result<(), String> {
        let module = self.module();
        crate::transform::aggregate::EnumLowerToProduct.run(module);
        ConstDataLower::default().run(module);
        self.func_behavior_dirty = true;
        Ok(())
    }

    fn run_object_combine(&mut self) -> Result<(), String> {
        self.run_pass_round("default", &[Pass::AggregateCombine], false, false);
        Ok(())
    }

    fn run_object_aggregate_abi_lowering(&mut self) -> Result<(), String> {
        self.synthetic_out_args =
            ObjectAggregateAbi::default().run_with_synthetic_out_args(self.module())?;
        self.func_behavior_dirty = true;
        Ok(())
    }

    fn run_object_cleanup(&mut self) -> Result<(), String> {
        let object_effects = compute_object_effect_summaries(self.module());
        let mut local_object_args =
            collect_local_object_arg_info_with_effects(self.module(), &object_effects);
        merge_local_object_arg_info(&mut local_object_args, &self.synthetic_out_args);
        self.object_effects = Some(object_effects);
        self.local_object_args = Some(local_object_args);

        self.run_pass_round("object_facts", &[Pass::ObjectLoadStore], true, true);
        Ok(())
    }

    fn run_object_abi_and_type_lowering(&mut self) -> Result<(), String> {
        let module = self.module();
        ObjectLowerToMemory.run(module);
        AggregateExpandAbi::default().run(module);
        legalize_evm_section(module, &self.funcs);
        self.func_behavior_dirty = true;
        Ok(())
    }

    fn run_aggregate_cleanup(&mut self) -> Result<(), String> {
        self.run_pass_round(
            "local_object_args",
            &[
                Pass::CfgCleanup,
                Pass::AggregateCombine,
                Pass::AggregateScalarize,
            ],
            true,
            false,
        );
        run_dead_arg_elim(self.work.module(), DeadArgElimConfig::default());
        self.func_behavior_dirty = true;
        self.run_pass_round(
            "default",
            &[
                Pass::CfgCleanup,
                Pass::BranchCanonicalize,
                Pass::LoadStore,
                Pass::ScalarCanonicalize,
                Pass::KnownBitsSimplify,
                Pass::Sccp,
                Pass::BranchCanonicalize,
                Pass::CfgCleanup,
            ],
            false,
            false,
        );
        Ok(())
    }

    fn run_validate_lowering_ir(&mut self) -> Result<(), String> {
        let membership = self.work.membership();
        self.funcs = self.work.function_emission_order(&membership);

        if let Some((_, message)) =
            collect_unsupported_evm_multi_return(self.module(), &self.funcs, None)
                .into_iter()
                .next()
        {
            return Err(message);
        }

        for &func in &self.funcs {
            self.module().func_store.view(func, |function| {
                validate_supported_lowering_ir(func, function)
            })?;
        }
        Ok(())
    }

    fn run_memory_legalization(&mut self) -> Result<(), String> {
        self.ptr_escape = Some(compute_ptr_escape_summaries(
            self.module(),
            &self.funcs,
            &self.backend.isa,
        ));
        let ptr_escape = self
            .ptr_escape
            .as_ref()
            .ok_or_else(|| "missing ptr escape summaries before free-ptr restore".to_string())?;
        for &func in &self.funcs {
            let _span = trace_span!(
                "sonatina.codegen.evm.prepare_free_ptr_restore.func",
                func_ref = func.as_u32()
            )
            .entered();
            self.module().func_store.modify(func, |function| {
                prepare_free_ptr_restore(function, &self.module().ctx, self.backend, ptr_escape);
            });
        }
        self.func_behavior_dirty = true;

        for &func in &self.funcs {
            let _span = trace_span!(
                "sonatina.codegen.evm.aggregate_legalize.func",
                func_ref = func.as_u32()
            )
            .entered();
            self.module().func_store.modify(func, |function| {
                AggregateLowerToMemoryLegalize::default().run(function, &self.module().ctx);
                assert_aggregate_legalized(function, &self.module().ctx);
            });
        }
        self.func_behavior_dirty = true;
        Ok(())
    }

    fn run_raw_memory_cleanup(&mut self) -> Result<(), String> {
        self.run_pass_round(
            "default",
            &[
                Pass::CfgCleanup,
                Pass::BranchCanonicalize,
                Pass::ScalarCanonicalize,
                Pass::Gvn,
                Pass::Licm,
                Pass::CfgCleanup,
            ],
            false,
            false,
        );
        self.run_pass_round(
            "default",
            &[
                Pass::BranchCanonicalize,
                Pass::LoadStore,
                Pass::CheckedArithElim,
                Pass::Sccp,
                Pass::LoopStrengthReduce,
                Pass::ScalarCanonicalize,
                Pass::LoadStore,
                Pass::Sccp,
                Pass::BranchCanonicalize,
                Pass::CfgCleanup,
            ],
            false,
            false,
        );
        Ok(())
    }
}
