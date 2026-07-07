use cranelift_entity::SecondaryMap;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::FxHashMap;
use sonatina_ir::{
    AccessKind, AccessLoc, BlockId, Function, InstId, InstSetExt, MemoryAccess, Module, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::inst_set::EvmInstKind,
    isa::{
        Isa,
        evm::{Evm, space::MEMORY},
    },
    module::{FuncRef, ModuleCtx},
};

use super::{
    immediate_u32,
    memory_plan::{
        BackendSpillReserve, FuncPreAnalysis, ObjLoc, ProgramMemoryPlan, SemanticFuncPlan,
        WORD_BYTES, compute_abs_clobber_words_with_extra,
    },
    ptr_provenance::Provenance,
};
use crate::{liveness::InstLiveness, module_analysis::CallGraphSchedule};

pub(crate) fn compute_semantic_malloc_future_abs_words_with_extra(
    module: &Module,
    schedule: &CallGraphSchedule,
    plan: &ProgramMemoryPlan,
    analyses: &FxHashMap<FuncRef, FuncPreAnalysis>,
    isa: &Evm,
    extra_clobber_words: &FxHashMap<FuncRef, BackendSpillReserve>,
) -> FxHashMap<FuncRef, FxHashMap<InstId, u32>> {
    compute_malloc_future_abs_words_with_analysis(
        module,
        schedule,
        plan,
        analyses,
        isa,
        extra_clobber_words,
        |analysis| FutureBoundsAnalysis {
            cfg: &analysis.cfg,
            inst_liveness: &analysis.inst_liveness,
            canonicalize: &analysis.value_aliases,
            prov_conservative: &analysis.prov_conservative_value,
        },
    )
}

fn compute_malloc_future_abs_words_with_analysis<A>(
    module: &Module,
    schedule: &CallGraphSchedule,
    plan: &ProgramMemoryPlan,
    analyses: &FxHashMap<FuncRef, A>,
    isa: &Evm,
    extra_clobber_words: &FxHashMap<FuncRef, BackendSpillReserve>,
    analysis_view: impl Fn(&A) -> FutureBoundsAnalysis<'_> + Sync,
) -> FxHashMap<FuncRef, FxHashMap<InstId, u32>>
where
    A: Sync,
{
    let abs_clobber_words =
        compute_abs_clobber_words_with_extra(schedule, plan, extra_clobber_words);
    let mut results: Vec<_> = schedule
        .funcs()
        .par_iter()
        .copied()
        .map(|f| {
            let func_plan = plan
                .funcs
                .get(&f)
                .unwrap_or_else(|| panic!("missing memory plan for func {}", f.as_u32()));
            let analysis = analyses
                .get(&f)
                .unwrap_or_else(|| panic!("missing analysis for func {}", f.as_u32()));
            let analysis = analysis_view(analysis);
            let map = module.func_store.view(f, |function| {
                let ctx = FutureBoundsCtx {
                    module: &module.ctx,
                    isa,
                    plan,
                    func_plan,
                    abs_clobber_words: &abs_clobber_words,
                    analysis,
                };
                compute_future_bounds_for_func(function, &ctx)
            });
            (f, map)
        })
        .collect();
    results.sort_unstable_by_key(|(func, _)| func.as_u32());

    let mut out: FxHashMap<FuncRef, FxHashMap<InstId, u32>> = FxHashMap::default();
    for (func, map) in results {
        out.insert(func, map);
    }
    out
}

struct FutureBoundsAnalysis<'a> {
    cfg: &'a ControlFlowGraph,
    inst_liveness: &'a InstLiveness,
    canonicalize: &'a SecondaryMap<ValueId, Option<ValueId>>,
    /// Deliberately computed with all-conservative callee summaries: heap
    /// bounds must hold regardless of callee escape behavior.
    prov_conservative: &'a SecondaryMap<ValueId, Provenance>,
}

struct FutureBoundsCtx<'a> {
    module: &'a ModuleCtx,
    isa: &'a Evm,
    plan: &'a ProgramMemoryPlan,
    func_plan: &'a SemanticFuncPlan,
    abs_clobber_words: &'a FxHashMap<FuncRef, u32>,
    analysis: FutureBoundsAnalysis<'a>,
}

fn compute_future_bounds_for_func(
    function: &Function,
    ctx: &FutureBoundsCtx<'_>,
) -> FxHashMap<InstId, u32> {
    let cfg = ctx.analysis.cfg;
    let prov = ctx.analysis.prov_conservative;

    let mut alloca_end_words: FxHashMap<InstId, u32> = FxHashMap::default();
    for (&inst, &loc) in &ctx.func_plan.alloca_loc {
        let data = ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst));
        let EvmInstKind::Alloca(alloca) = data else {
            continue;
        };

        let Some(base_word) = absolute_base_word_for_loc(ctx.func_plan, loc) else {
            continue;
        };
        let size_bytes: u32 = ctx
            .isa
            .type_layout()
            .size_of(*alloca.ty(), ctx.module)
            .expect("alloca has invalid type") as u32;
        let size_words = size_bytes.div_ceil(WORD_BYTES);
        let end_words = base_word
            .checked_add(size_words)
            .expect("alloca end words overflow");
        alloca_end_words.insert(inst, end_words);
    }

    let mut value_alloca_bound: SecondaryMap<ValueId, u32> = SecondaryMap::new();
    for value in function.dfg.value_ids() {
        let _ = &mut value_alloca_bound[value];
    }

    for value in function.dfg.value_ids() {
        let mut max_end: u32 = 0;
        for base in prov[value].alloca_insts() {
            if let Some(end) = alloca_end_words.get(&base) {
                max_end = max_end.max(*end);
            }
        }
        value_alloca_bound[value] = max_end;
    }

    fn call_bound(ctx: &FutureBoundsCtx<'_>, function: &Function, inst: InstId) -> u32 {
        let Some(call) = function.dfg.call_info(inst) else {
            return 0;
        };
        let callee = call.callee();
        let callee_plan = ctx.plan.funcs.get(&callee).unwrap_or_else(|| {
            panic!(
                "missing memory plan for callee {} in heap bounds analysis",
                callee.as_u32()
            )
        });
        let callee_bound = ctx
            .abs_clobber_words
            .get(&callee)
            .copied()
            .unwrap_or_else(|| callee_plan.abs_words_end());
        callee_bound.max(call_preserve_bound(ctx.func_plan, inst))
    }

    fn live_bound(
        analysis: &FutureBoundsAnalysis<'_>,
        value_alloca_bound: &SecondaryMap<ValueId, u32>,
        inst: InstId,
    ) -> u32 {
        analysis
            .inst_liveness
            .live_out(inst)
            .iter()
            .map(|v| super::canonicalize_alias_value(analysis.canonicalize, v))
            .map(|v| value_alloca_bound[v])
            .max()
            .unwrap_or(0)
    }

    fn static_write_bound(
        function: &Function,
        ctx: &FutureBoundsCtx<'_>,
        prov: &SecondaryMap<ValueId, Provenance>,
        alloca_end_words: &FxHashMap<InstId, u32>,
        inst: InstId,
    ) -> u32 {
        function
            .dfg
            .effects(inst)
            .accesses
            .iter()
            .filter(|access| access.kind == AccessKind::Write && access.space == MEMORY)
            .map(|access| static_write_access_bound(ctx.func_plan, prov, alloca_end_words, access))
            .max()
            .unwrap_or(0)
    }

    let mut block_in: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    let mut block_local: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    let mut block_static_in: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    let mut block_static_local: SecondaryMap<BlockId, u32> = SecondaryMap::new();
    for block in function.layout.iter_block() {
        let _ = &mut block_in[block];
        let _ = &mut block_local[block];
        let _ = &mut block_static_in[block];
        let _ = &mut block_static_local[block];
    }

    for block in function.layout.iter_block() {
        let mut bound = ctx.func_plan.entry_abs_words;
        let mut static_bound = 0;
        for inst in function.layout.iter_inst(block) {
            bound = bound.max(call_bound(ctx, function, inst));
            bound = bound.max(live_bound(&ctx.analysis, &value_alloca_bound, inst));
            static_bound = static_bound.max(static_write_bound(
                function,
                ctx,
                prov,
                &alloca_end_words,
                inst,
            ));
        }
        block_local[block] = bound;
        block_static_local[block] = static_bound;
    }

    let blocks: Vec<BlockId> = cfg.post_order().collect();
    let mut changed = true;
    while changed {
        changed = false;

        for &block in &blocks {
            let out = cfg.succs_of(block).map(|b| block_in[*b]).max().unwrap_or(0);
            let bound = out.max(block_local[block]);

            if bound > block_in[block] {
                block_in[block] = bound;
                changed = true;
            }

            let static_out = cfg
                .succs_of(block)
                .map(|b| block_static_in[*b])
                .max()
                .unwrap_or(0);
            let static_bound = static_out.max(block_static_local[block]);
            if static_bound > block_static_in[block] {
                block_static_in[block] = static_bound;
                changed = true;
            }
        }
    }

    let mut malloc_bounds: FxHashMap<InstId, u32> = FxHashMap::default();
    for block in function.layout.iter_block() {
        let out = cfg.succs_of(block).map(|b| block_in[*b]).max().unwrap_or(0);
        let mut bound = out.max(ctx.func_plan.entry_abs_words);
        let mut static_bound = cfg
            .succs_of(block)
            .map(|b| block_static_in[*b])
            .max()
            .unwrap_or(0);

        let insts: Vec<InstId> = function.layout.iter_inst(block).collect();
        for inst in insts.into_iter().rev() {
            bound = bound.max(call_bound(ctx, function, inst));
            bound = bound.max(live_bound(&ctx.analysis, &value_alloca_bound, inst));

            if matches!(
                ctx.isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                EvmInstKind::EvmMalloc(_)
            ) {
                let mut malloc_bound = bound;
                if !ctx.func_plan.transient_mallocs.contains(&inst) {
                    malloc_bound = malloc_bound.max(static_bound);
                }
                malloc_bounds.insert(inst, malloc_bound);
            }

            static_bound = static_bound.max(static_write_bound(
                function,
                ctx,
                prov,
                &alloca_end_words,
                inst,
            ));
        }
    }

    malloc_bounds
}

fn static_write_access_bound(
    func_plan: &SemanticFuncPlan,
    prov: &SecondaryMap<ValueId, Provenance>,
    alloca_end_words: &FxHashMap<InstId, u32>,
    access: &MemoryAccess,
) -> u32 {
    match &access.loc {
        AccessLoc::LinearExact { addr, .. } | AccessLoc::LinearRange { addr, .. } => {
            let addr_prov = &prov[*addr];
            let alloca_bound = addr_prov
                .alloca_insts()
                .filter_map(|base| alloca_end_words.get(&base).copied())
                .max()
                .unwrap_or(0);
            if addr_prov.is_unknown_ptr() {
                alloca_bound.max(func_plan.abs_words_end())
            } else {
                alloca_bound
            }
        }
        AccessLoc::LinearExactImm { addr, bytes, .. } => {
            immediate_write_bound(func_plan, *addr, *bytes)
        }
        AccessLoc::WholeSpace | AccessLoc::Unknown => func_plan.abs_words_end(),
        AccessLoc::KeyedExact { .. } => 0,
    }
}

fn immediate_write_bound(
    func_plan: &SemanticFuncPlan,
    addr: sonatina_ir::Immediate,
    bytes: u32,
) -> u32 {
    if bytes == 0 {
        return 0;
    }
    let Some(addr) = immediate_u32(addr) else {
        return func_plan.abs_words_end();
    };
    let Some(end) = addr.checked_add(bytes) else {
        return func_plan.abs_words_end();
    };
    if end <= func_plan.arena_base {
        return 0;
    }
    end.checked_sub(func_plan.arena_base)
        .and_then(|bytes| bytes.checked_add(WORD_BYTES - 1))
        .map(|bytes| bytes / WORD_BYTES)
        .unwrap_or_else(|| func_plan.abs_words_end())
}

fn absolute_base_word_for_loc(func_plan: &SemanticFuncPlan, loc: ObjLoc) -> Option<u32> {
    match loc {
        ObjLoc::ScratchAbs(off) => Some(off),
        ObjLoc::StableAbs(off) => func_plan
            .stable_base_word()
            .and_then(|base| base.checked_add(off)),
        ObjLoc::StableFrame(_) => None,
    }
}

fn call_preserve_bound(func_plan: &SemanticFuncPlan, inst: InstId) -> u32 {
    let Some(plan) = func_plan.call_preserve.get(&inst) else {
        return 0;
    };
    let (shadow_obj, runs) = (&plan.shadow_obj, &plan.runs);
    let Some(loc) = func_plan.obj_loc.get(shadow_obj).copied() else {
        panic!(
            "call preserve shadow object {} is not placed",
            shadow_obj.as_u32()
        );
    };
    let Some(start_word) = absolute_base_word_for_loc(func_plan, loc) else {
        return 0;
    };
    let shadow_words = runs
        .iter()
        .map(|run| {
            run.shadow_dst_word
                .checked_add(run.len_words)
                .expect("call preserve shadow run end overflow")
        })
        .max()
        .unwrap_or(0);

    start_word
        .checked_add(shadow_words)
        .expect("call preserve shadow bound overflow")
}

#[cfg(test)]
mod tests {
    use cranelift_entity::SecondaryMap;
    use rustc_hash::{FxHashMap, FxHashSet};
    use smallvec::smallvec;
    use sonatina_ir::{ValueId, cfg::ControlFlowGraph, isa::evm::Evm, module::FuncRef};
    use sonatina_parser::parse_module;
    use sonatina_triple::{Architecture, EvmVersion, OperatingSystem, TargetTriple, Vendor};

    use super::*;
    use crate::{
        isa::evm::{
            STATIC_BASE,
            memory_plan::{CallPreservePlan, SaveRun, StableMode},
            static_arena_alloc::StackObjId,
        },
        liveness::{InstLiveness, Liveness},
    };

    struct TestAnalysis {
        cfg: ControlFlowGraph,
        inst_liveness: InstLiveness,
        value_aliases: SecondaryMap<ValueId, Option<ValueId>>,
        prov_conservative: SecondaryMap<ValueId, Provenance>,
    }

    fn compute_test_analysis(module: &ModuleCtx, isa: &Evm, function: &Function) -> TestAnalysis {
        let mut cfg = ControlFlowGraph::new();
        cfg.compute(function);

        let mut liveness = Liveness::new();
        liveness.compute(function, &cfg);

        let mut inst_liveness = InstLiveness::new();
        inst_liveness.compute(function, &cfg, &liveness);

        let mut value_aliases = SecondaryMap::new();
        for value in function.dfg.value_ids() {
            let _ = &mut value_aliases[value];
        }

        let prov_conservative = crate::isa::evm::ptr_provenance::compute_value_provenance(
            function,
            module,
            isa,
            |callee| {
                crate::isa::evm::ptr_escape::PtrEscapeSummary::conservative_unknown_ctx(
                    module, callee,
                )
            },
        );

        TestAnalysis {
            cfg,
            inst_liveness,
            value_aliases,
            prov_conservative,
        }
    }

    fn empty_func_plan() -> SemanticFuncPlan {
        SemanticFuncPlan {
            arena_base: STATIC_BASE,
            scratch_words: 0,
            stable_words: 0,
            stable_mode: StableMode::None,
            entry_abs_words: 0,
            obj_loc: FxHashMap::default(),
            alloca_loc: FxHashMap::default(),
            call_preserve: FxHashMap::default(),
            malloc_future_abs_words: FxHashMap::default(),
            transient_mallocs: FxHashSet::default(),
            malloc_escape_kinds: FxHashMap::default(),
            return_escape_caller_abs_words: 0,
        }
    }

    #[test]
    fn malloc_future_bound_includes_call_preserve_shadow_slots() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func private %callee() -> i256 {
block0:
    return 7.i256;
}

func public %caller() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.i256 = call %callee;
    return v1;
}
"#,
        )
        .expect("module parses");
        let funcs = parsed.module.funcs();
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });

        let mut names: FxHashMap<String, FuncRef> = FxHashMap::default();
        let mut analyses: FxHashMap<FuncRef, TestAnalysis> = FxHashMap::default();
        for &func in &funcs {
            let name = parsed
                .module
                .ctx
                .func_sig(func, |sig| sig.name().to_string());
            names.insert(name, func);
            parsed.module.func_store.view(func, |function| {
                analyses.insert(
                    func,
                    compute_test_analysis(&parsed.module.ctx, &isa, function),
                );
            });
        }
        let caller = names["caller"];
        let callee = names["callee"];

        let (malloc_inst, call_inst) = parsed.module.func_store.view(caller, |function| {
            let mut malloc_inst = None;
            let mut call_inst = None;
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    if matches!(
                        isa.inst_set().resolve_inst(function.dfg.inst(inst)),
                        EvmInstKind::EvmMalloc(_)
                    ) {
                        malloc_inst = Some(inst);
                    }
                    if function.dfg.call_info(inst).is_some() {
                        call_inst = Some(inst);
                    }
                }
            }
            (
                malloc_inst.expect("missing malloc"),
                call_inst.expect("missing call"),
            )
        });

        let shadow_obj = StackObjId::from_u32(0);
        let mut caller_plan = empty_func_plan();
        caller_plan.scratch_words = 1;
        caller_plan.stable_words = 2;
        caller_plan.stable_mode = StableMode::StableAbs { base_word: 2 };
        caller_plan.entry_abs_words = 2;
        caller_plan.obj_loc.insert(shadow_obj, ObjLoc::StableAbs(0));
        caller_plan.call_preserve.insert(
            call_inst,
            CallPreservePlan {
                shadow_obj,
                runs: smallvec![SaveRun {
                    scratch_src_word: 0,
                    shadow_dst_word: 0,
                    len_words: 2,
                }],
                result_count: 1,
            },
        );

        let mut plan = ProgramMemoryPlan {
            arena_base: STATIC_BASE,
            scratch_peak_words: 1,
            stable_chain_peak_words: 2,
            global_dyn_base: STATIC_BASE + 96,
            funcs: FxHashMap::default(),
        };
        plan.funcs.insert(caller, caller_plan);
        plan.funcs.insert(callee, empty_func_plan());

        let bounds = compute_malloc_future_abs_words_with_analysis(
            &parsed.module,
            &crate::module_analysis::CallGraphSchedule::compute(&parsed.module, &funcs),
            &plan,
            &analyses,
            &isa,
            &FxHashMap::default(),
            |analysis| FutureBoundsAnalysis {
                cfg: &analysis.cfg,
                inst_liveness: &analysis.inst_liveness,
                canonicalize: &analysis.value_aliases,
                prov_conservative: &analysis.prov_conservative,
            },
        );

        assert_eq!(bounds[&caller][&malloc_inst], 4);
    }

    #[test]
    fn persistent_malloc_future_bound_includes_later_static_writes() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %main() -> i256 {
block0:
    v0.*i8 = evm_malloc 32.i256;
    v1.*i256 = alloca i256;
    mstore v1 7.i256 i256;
    v2.i256 = ptr_to_int v0 i256;
    return v2;
}
"#,
        )
        .expect("module parses");
        let funcs = parsed.module.funcs();
        let func = funcs[0];
        let isa = Evm::new(TargetTriple {
            architecture: Architecture::Evm,
            vendor: Vendor::Ethereum,
            operating_system: OperatingSystem::Evm(EvmVersion::Osaka),
        });
        let analysis = parsed.module.func_store.view(func, |function| {
            compute_test_analysis(&parsed.module.ctx, &isa, function)
        });
        let analyses = FxHashMap::from_iter([(func, analysis)]);

        let (malloc_inst, alloca_inst) = parsed.module.func_store.view(func, |function| {
            let mut malloc_inst = None;
            let mut alloca_inst = None;
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    match isa.inst_set().resolve_inst(function.dfg.inst(inst)) {
                        EvmInstKind::EvmMalloc(_) => malloc_inst = Some(inst),
                        EvmInstKind::Alloca(_) => alloca_inst = Some(inst),
                        _ => {}
                    }
                }
            }
            (
                malloc_inst.expect("missing malloc"),
                alloca_inst.expect("missing alloca"),
            )
        });

        let mut func_plan = empty_func_plan();
        func_plan.scratch_words = 4;
        func_plan
            .alloca_loc
            .insert(alloca_inst, ObjLoc::ScratchAbs(3));

        let mut plan = ProgramMemoryPlan {
            arena_base: STATIC_BASE,
            scratch_peak_words: 4,
            stable_chain_peak_words: 0,
            global_dyn_base: STATIC_BASE + 4 * WORD_BYTES,
            funcs: FxHashMap::default(),
        };
        plan.funcs.insert(func, func_plan);

        let bounds = compute_malloc_future_abs_words_with_analysis(
            &parsed.module,
            &crate::module_analysis::CallGraphSchedule::compute(&parsed.module, &funcs),
            &plan,
            &analyses,
            &isa,
            &FxHashMap::default(),
            |analysis| FutureBoundsAnalysis {
                cfg: &analysis.cfg,
                inst_liveness: &analysis.inst_liveness,
                canonicalize: &analysis.value_aliases,
                prov_conservative: &analysis.prov_conservative,
            },
        );

        assert_eq!(bounds[&func][&malloc_inst], 4);
    }
}
