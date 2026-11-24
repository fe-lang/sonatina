use std::iter;

use tracing::{debug_span, info_span, trace_span};

use crate::{
    machinst::lower::SectionWorkModule,
    optim::{
        constref_specialize::specialize_private_constrefs,
        dead_arg::{DeadArgElimConfig, run_dead_arg_elim},
        dead_ret::{DeadRetElimConfig, run_dead_ret_elim},
        forwarded_ret::{ForwardedRetElimConfig, run_forwarded_ret_elim},
        pipeline::{Pass, run_function_pass_round},
        uniform_const_arg::run_uniform_const_arg_binding,
    },
    transform::{
        aggregate::{
            AggregateExpandAbi, AggregateLowerToMemoryLegalize, ObjectAggregateAbi,
            assert_aggregate_legalized, check_fresh_aggregates_folded,
            cleanup_dead_aggregate_alloca_trees, fresh::fold_fresh_aggregates_in,
        },
        evm::{
            ConstDataLower, erase_unit_values, legalize_evm_section, lower_keccak256_words,
            reuse_terminal_word_buffers,
        },
    },
};
use sonatina_ir::{Module, module::FuncRef};

use super::{
    EvmBackend, LateCleanupProfile, PtrEscapeSummaries, collect_unsupported_evm_calls,
    compute_ptr_escape_summaries, promote_local_mallocs, validate_supported_lowering_ir,
};

pub(crate) struct EvmPipelineArtifacts {
    pub(crate) funcs: Vec<FuncRef>,
    pub(crate) ptr_escape: PtrEscapeSummaries,
}

pub(crate) struct EvmPipeline<'a> {
    backend: &'a EvmBackend,
}

struct EvmPipelineContext<'a> {
    backend: &'a EvmBackend,
    work: &'a SectionWorkModule,
    funcs: Vec<FuncRef>,
    roots: Vec<FuncRef>,
    func_behavior_dirty: bool,
    ptr_escape: Option<PtrEscapeSummaries>,
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
            roots: iter::once(work.entry())
                .chain(work.includes().iter().copied())
                .collect(),
            func_behavior_dirty: true,
            ptr_escape: None,
        };
        let optional_cleanup = self.backend.late_cleanup_profile != LateCleanupProfile::Off;
        let _span = info_span!(
            "sonatina.codegen.evm.pipeline.run",
            funcs = ctx.funcs.len(),
            phases = if optional_cleanup { 10 } else { 7 }
        )
        .entered();

        ctx.run_phase(
            "const_lowering",
            "mandatory",
            EvmPipelineContext::run_const_lowering,
        )?;
        if optional_cleanup {
            ctx.run_phase(
                "object_combine",
                "optional",
                EvmPipelineContext::run_object_combine,
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
        ctx.run_phase(
            "fold_fresh_aggregates",
            "mandatory",
            EvmPipelineContext::run_fold_fresh_aggregates,
        )?;
        ctx.run_phase(
            "keccak_words_lowering",
            "mandatory",
            EvmPipelineContext::run_keccak_words_lowering,
        )?;
        ctx.run_phase(
            "unit_erasure",
            "mandatory",
            EvmPipelineContext::run_unit_erasure,
        )?;
        ctx.run_phase(
            "check_fresh_aggregates_folded",
            "mandatory",
            EvmPipelineContext::run_check_fresh_aggregates_folded,
        )?;

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

    fn run_pass_round(&mut self, mode: &'static str, passes: &[Pass]) {
        let _span = debug_span!(
            "sonatina.codegen.evm.pipeline.optimize",
            mode = mode,
            pass_count = passes.len()
        )
        .entered();
        run_function_pass_round(
            self.work.module(),
            passes,
            &mut self.func_behavior_dirty,
            Some(self.funcs.as_slice()),
            None,
        );
    }

    fn refresh_section_funcs(&mut self) {
        let (membership, removed) = self.work.prune_unreachable_defined_funcs();
        self.funcs = self.work.function_emission_order(&membership);
        if removed != 0 {
            self.func_behavior_dirty = true;
        }
    }

    fn ensure_only_section_funcs_remain(&self) -> Result<(), String> {
        let mut expected = self.funcs.clone();
        expected.sort_unstable();
        let actual = self.module().funcs();
        if actual == expected {
            return Ok(());
        }

        Err(format!(
            "EVM section module still contains non-section functions before legalization: \
             expected {expected:?}, found {actual:?}"
        ))
    }

    fn run_const_lowering(&mut self) -> Result<(), String> {
        let stats = specialize_private_constrefs(self.module(), &self.funcs);
        if stats.changed {
            run_dead_arg_elim(self.module(), &self.roots, DeadArgElimConfig::default());
            self.refresh_section_funcs();
            self.func_behavior_dirty = true;
            self.run_pass_round("constref_specialize", &[Pass::Sccp, Pass::CfgCleanup]);
            self.refresh_section_funcs();
        }
        ConstDataLower::default().run(self.module());
        self.func_behavior_dirty = true;
        Ok(())
    }

    fn run_object_combine(&mut self) -> Result<(), String> {
        self.run_pass_round("default", &[Pass::AggregateCombine]);
        Ok(())
    }

    fn run_object_abi_and_type_lowering(&mut self) -> Result<(), String> {
        ObjectAggregateAbi::default().lower_to_memory(
            self.module(),
            self.backend.late_cleanup_profile != LateCleanupProfile::Off,
        )?;
        AggregateExpandAbi::default().run(self.module());
        self.refresh_section_funcs();
        self.ensure_only_section_funcs_remain()?;
        legalize_evm_section(self.module(), &self.funcs);
        self.func_behavior_dirty = true;
        if self.backend.late_cleanup_profile == LateCleanupProfile::Off {
            self.run_pass_round("post_evm_legalize", &[Pass::CfgCleanup]);
        }
        Ok(())
    }

    fn run_aggregate_cleanup(&mut self) -> Result<(), String> {
        self.run_pass_round(
            "aggregate_cleanup",
            &[
                Pass::CfgCleanup,
                Pass::AggregateCombine,
                Pass::AggregateScalarize,
            ],
        );
        self.run_pass_round(
            "uniform_const_arg_canonicalize",
            &[
                Pass::CfgCleanup,
                Pass::ScalarCanonicalize,
                Pass::KnownBitsSimplify,
                Pass::Sccp,
                Pass::CfgCleanup,
            ],
        );
        run_uniform_const_arg_binding(self.work.module(), &self.funcs);
        run_dead_arg_elim(
            self.work.module(),
            &self.roots,
            DeadArgElimConfig::default(),
        );
        // Return lanes that only echo an argument, or that no caller reads, are
        // the result-side twin of dead arguments. Dropping them can leave
        // arguments dead again, so dead-argument elimination runs once more.
        let forwarded = run_forwarded_ret_elim(
            self.work.module(),
            &self.roots,
            ForwardedRetElimConfig::default(),
        );
        let dead = run_dead_ret_elim(
            self.work.module(),
            &self.roots,
            DeadRetElimConfig::default(),
        );
        if forwarded.removed_rets + dead.removed_rets > 0 {
            run_dead_arg_elim(
                self.work.module(),
                &self.roots,
                DeadArgElimConfig::default(),
            );
        }
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
        );
        Ok(())
    }

    fn run_validate_lowering_ir(&mut self) -> Result<(), String> {
        self.refresh_section_funcs();

        if let Some((_, message)) = collect_unsupported_evm_calls(self.module(), &self.funcs, None)
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
        {
            let module = self.module();
            let module_ctx = &module.ctx;
            for &func in &self.funcs {
                let _span = trace_span!(
                    "sonatina.codegen.evm.aggregate_legalize.func",
                    func_ref = func.as_u32()
                )
                .entered();
                module.func_store.modify(func, |function| {
                    AggregateLowerToMemoryLegalize::default().run(function, module_ctx);
                    assert_aggregate_legalized(function, module_ctx);
                });
            }
        }
        // Later memory planning reads summaries against the lowered call signatures.
        self.ptr_escape = Some(compute_ptr_escape_summaries(
            self.module(),
            &self.funcs,
            &self.backend.isa,
        ));
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
        );
        self.run_pass_round(
            "default",
            &[
                Pass::BranchCanonicalize,
                Pass::LoadStore,
                Pass::CheckedArithElim,
                Pass::MergeIndexChecks,
                Pass::RangeBranchSimplify,
                Pass::Sccp,
                Pass::LoopStrengthReduce,
                Pass::ScalarCanonicalize,
                Pass::LoadStore,
                Pass::Sccp,
                Pass::BranchCanonicalize,
                Pass::CfgCleanup,
            ],
        );
        let mut terminal_payloads_changed = false;
        {
            let module = self.module();
            let module_ctx = &module.ctx;
            for &func in &self.funcs {
                let _span = trace_span!(
                    "sonatina.codegen.evm.aggregate_scratch_cleanup.func",
                    func_ref = func.as_u32()
                )
                .entered();
                terminal_payloads_changed |= module.func_store.modify(func, |function| {
                    cleanup_dead_aggregate_alloca_trees(function, module_ctx);
                    assert_aggregate_legalized(function, module_ctx);
                    reuse_terminal_word_buffers(function)
                });
            }
        }
        if terminal_payloads_changed {
            self.func_behavior_dirty = true;
            self.run_pass_round("terminal_payload", &[Pass::Sccp, Pass::LoadStore]);
            self.ptr_escape = Some(compute_ptr_escape_summaries(
                self.module(),
                &self.funcs,
                &self.backend.isa,
            ));
        }
        Ok(())
    }

    /// Folds the fresh insert chains the IR passes made into `agg.make`s.
    /// Runs after the last IR pass; the phases after it make no such chain.
    fn run_fold_fresh_aggregates(&mut self) -> Result<(), String> {
        for &func in &self.funcs {
            self.module()
                .func_store
                .modify(func, fold_fresh_aggregates_in);
        }
        Ok(())
    }

    /// Word hashes stay pure values through every optimization round above;
    /// only now do they become the memory hash the EVM executes, before
    /// memory planning places the preimages.
    fn run_keccak_words_lowering(&mut self) -> Result<(), String> {
        let mut changed = false;
        {
            let module = self.module();
            for &func in &self.funcs {
                changed |= module.func_store.modify(func, lower_keccak256_words);
            }
        }
        let summaries = match self.ptr_escape.take() {
            Some(summaries) if !changed => summaries,
            _ => compute_ptr_escape_summaries(self.module(), &self.funcs, &self.backend.isa),
        };
        let promoted = promote_local_mallocs(self.module(), &self.funcs, self.backend, &summaries);
        if changed || promoted {
            self.func_behavior_dirty = true;
        }
        self.ptr_escape = Some(if promoted {
            compute_ptr_escape_summaries(self.module(), &self.funcs, &self.backend.isa)
        } else {
            summaries
        });
        Ok(())
    }

    /// Checks the IR this pipeline leaves has no fresh insert chain.
    fn run_check_fresh_aggregates_folded(&mut self) -> Result<(), String> {
        let module = self.module();
        for &func in &self.funcs {
            module
                .func_store
                .view(func, check_fresh_aggregates_folded)
                .map_err(|error| {
                    let name = module.ctx.func_sig(func, |sig| sig.name().to_string());
                    format!(
                        "function %{name} has an unfolded fresh aggregate after the EVM \
                         pipeline: {error}"
                    )
                })?;
        }
        Ok(())
    }

    /// Runs last, so that no pass can make a unit value after it. It only
    /// removes instructions that move no pointer, so the pointer escape
    /// summaries stay valid.
    fn run_unit_erasure(&mut self) -> Result<(), String> {
        for &func in &self.funcs {
            self.module().func_store.modify(func, erase_unit_values);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        isa::evm::test_util::{osaka_backend, prepare_root},
        test_support::{lookup_func, parse_test_module},
    };

    /// The fixture `unit_values.sntn` compiles and runs with late cleanup
    /// `Off`. Fixtures reach `Speed` and `Size` only after the generic
    /// optimizer, which removes these unit values first, so this runs those
    /// late cleanup passes over them directly. Machine lowering rejects a unit
    /// value, so compiling shows none survived.
    #[test]
    fn late_cleanup_profiles_compile_unit_values() {
        let module = parse_test_module(include_str!("../../../test_files/evm/unit_values.sntn"));
        let entry = lookup_func(&module, "entry");
        for profile in [LateCleanupProfile::Speed, LateCleanupProfile::Size] {
            let backend = osaka_backend().with_late_cleanup_profile(profile);
            if let Err(err) = prepare_root(&module, &backend, entry) {
                panic!("{profile:?}: {err}");
            }
        }
    }
}
