use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Linkage, Module,
    inst::{SideEffect, data, downcast},
    module::{FuncHints, FuncRef},
};

use crate::{cfg_scc::CfgSccAnalysis, module_analysis::ModuleInfo};

use super::{
    super::aggregate::{LocalObjectArgMap, ObjectEffectSummaryMap, ObjectReturnEffect},
    InlinerConfig,
};

#[derive(Debug, Clone, Copy)]
pub(super) enum InlineSkipReason {
    NoBody,
    RecursiveScc,
    Budget,
    Cost,
    NoInlineHint,
}

#[derive(Debug, Clone, Copy)]
pub(super) enum InlineDecision {
    Inline(InlinePlan),
    Skip(InlineSkipReason),
}

#[derive(Debug, Clone, Copy)]
pub(super) struct InlinePlan {
    pub summary: InlineeSummary,
    pub score: i32,
    pub predicted_growth: usize,
    pub forced: bool,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct InlineeSummary {
    pub has_body: bool,
    pub blocks: usize,
    pub insts: usize,
    pub calls: usize,
    pub phis: usize,
    pub returns: usize,
    pub has_loop: bool,
    pub base_cost: i32,
    pub object: ObjectOptimizationSummary,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct ObjectOptimizationSummary {
    pub local_object_arg_count: usize,
    pub fresh_object_return_count: usize,
    pub object_store_count: usize,
    pub object_load_count: usize,
    pub object_slice_count: usize,
    pub enum_object_op_count: usize,
    pub likely_scalarizable: bool,
    pub scalarization_unlock_score: i32,
}

impl ObjectOptimizationSummary {
    fn tracked_root_count(self) -> usize {
        self.local_object_arg_count + self.fresh_object_return_count
    }

    fn object_op_count(self) -> usize {
        self.object_store_count
            + self.object_load_count
            + self.object_slice_count
            + self.enum_object_op_count
    }

    fn qualifies_for_helper_budget(self) -> bool {
        self.likely_scalarizable && self.tracked_root_count() > 0 && self.object_op_count() > 0
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct InlineRequest {
    pub callee_ref: FuncRef,
    pub callee_call_count: usize,
    pub caller_growth: usize,
    pub total_growth: usize,
    pub callee_depth: usize,
    pub call_has_result: bool,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct InlineDecisionContext<'a> {
    pub module_info: &'a ModuleInfo,
    pub local_object_args: Option<&'a LocalObjectArgMap>,
    pub object_effects: Option<&'a ObjectEffectSummaryMap>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum SummaryKey {
    Live(FuncRef),
    Snapshot(FuncRef),
}

pub(super) fn decide_inline(
    module: &Module,
    summary_cache: &mut FxHashMap<SummaryKey, InlineeSummary>,
    callee: Option<&Function>,
    recursive_callsite: bool,
    ctx: InlineDecisionContext<'_>,
    request: InlineRequest,
    config: &InlinerConfig,
) -> InlineDecision {
    let hints = module.ctx.func_hints(request.callee_ref);
    if hints.contains(FuncHints::NOINLINE) {
        return InlineDecision::Skip(InlineSkipReason::NoInlineHint);
    }

    if !module.ctx.func_linkage(request.callee_ref).has_definition() {
        return InlineDecision::Skip(InlineSkipReason::NoBody);
    }

    if recursive_callsite
        && !config.allow_inline_recursive
        && !hints.contains(FuncHints::ALWAYSINLINE)
    {
        return InlineDecision::Skip(InlineSkipReason::RecursiveScc);
    }

    let summary = get_inlinee_summary(
        module,
        summary_cache,
        request.callee_ref,
        callee,
        ctx.local_object_args,
        ctx.object_effects,
    );

    if !summary.has_body {
        return InlineDecision::Skip(InlineSkipReason::NoBody);
    }

    let mut predicted_growth = summary.insts;
    if request.call_has_result && summary.returns > 1 {
        predicted_growth = predicted_growth.saturating_add(1);
    }

    if hints.contains(FuncHints::ALWAYSINLINE) {
        return InlineDecision::Inline(InlinePlan {
            summary,
            score: i32::MIN,
            predicted_growth,
            forced: true,
        });
    }

    if exceeds_cap(summary.blocks, config.max_inlinee_blocks)
        || exceeds_cap(summary.insts, config.max_inlinee_insts)
    {
        return InlineDecision::Skip(InlineSkipReason::Budget);
    }

    if request.callee_call_count > 1
        && (exceeds_cap(summary.blocks, config.max_multi_use_inlinee_blocks)
            || exceeds_cap(summary.insts, config.max_multi_use_inlinee_insts))
        && !fits_object_helper_budget(module, summary, request, config)
    {
        return InlineDecision::Skip(InlineSkipReason::Budget);
    }

    let should_force_single_use =
        config.always_inline_single_use && request.callee_call_count == 1 && summary.blocks > 1;

    if exceeds_budget(
        request.caller_growth,
        predicted_growth,
        config.max_growth_per_caller,
    ) || exceeds_budget(
        request.total_growth,
        predicted_growth,
        config.max_total_growth,
    ) {
        return InlineDecision::Skip(InlineSkipReason::Budget);
    }

    if config.max_inline_depth > 0 && request.callee_depth + 1 > config.max_inline_depth {
        return InlineDecision::Skip(InlineSkipReason::Budget);
    }

    if should_force_single_use {
        return InlineDecision::Inline(InlinePlan {
            summary,
            score: i32::MIN + 1,
            predicted_growth,
            forced: true,
        });
    }

    let is_leaf = ctx
        .module_info
        .func_info
        .get(&request.callee_ref)
        .map(|info| info.is_leaf)
        .unwrap_or_else(|| {
            ctx.module_info
                .call_graph
                .is_leaf(&module.ctx, request.callee_ref)
        });

    let threshold = if summary.has_loop
        || summary.calls > 0
        || (summary.blocks > 1 && request.callee_call_count > 1)
    {
        config.inline_threshold_cold
    } else {
        config.inline_threshold
    };

    let mut score = summary.base_cost;
    score += summary.phis as i32;
    score += summary.returns.saturating_sub(1) as i32;
    if summary.has_loop {
        score += config.loop_penalty;
    }
    if summary.blocks > 1 && request.callee_call_count > 1 {
        score += config.multi_block_multi_use_penalty;
    }
    if request.callee_call_count == 1 {
        score -= config.single_use_bonus;
    }
    if is_leaf {
        score -= config.leaf_bonus;
    }
    if hints.contains(FuncHints::INLINEHINT) {
        score -= 2;
    }
    score -= summary
        .object
        .scalarization_unlock_score
        .min(config.object_scalarization_bonus_cap);
    score -= compute_object_helper_cluster_bonus(
        module,
        summary_cache,
        ctx,
        request.callee_ref,
        summary,
        config,
    );

    if score > threshold {
        InlineDecision::Skip(InlineSkipReason::Cost)
    } else {
        InlineDecision::Inline(InlinePlan {
            summary,
            score,
            predicted_growth,
            forced: false,
        })
    }
}

fn exceeds_cap(value: usize, cap: usize) -> bool {
    cap > 0 && value > cap
}

fn exceeds_budget(used: usize, growth: usize, cap: usize) -> bool {
    cap > 0 && used.saturating_add(growth) > cap
}

fn fits_object_helper_budget(
    module: &Module,
    summary: InlineeSummary,
    request: InlineRequest,
    config: &InlinerConfig,
) -> bool {
    module.ctx.func_linkage(request.callee_ref) == Linkage::Private
        && request.callee_call_count <= config.max_multi_use_object_helper_call_count
        && summary.object.qualifies_for_helper_budget()
        && !exceeds_cap(summary.blocks, config.max_multi_use_object_helper_blocks)
        && !exceeds_cap(summary.insts, config.max_multi_use_object_helper_insts)
}

fn compute_object_helper_cluster_bonus(
    module: &Module,
    summary_cache: &mut FxHashMap<SummaryKey, InlineeSummary>,
    ctx: InlineDecisionContext<'_>,
    callee_ref: FuncRef,
    summary: InlineeSummary,
    config: &InlinerConfig,
) -> i32 {
    if config.object_helper_cluster_bonus <= 0
        || module.ctx.func_linkage(callee_ref) != Linkage::Private
        || !summary.object.qualifies_for_helper_budget()
    {
        return 0;
    }

    ctx.module_info
        .call_graph
        .callee_of(callee_ref)
        .iter()
        .copied()
        .filter(|&nested| {
            nested != callee_ref && module.ctx.func_linkage(nested) == Linkage::Private
        })
        .filter(|&nested| {
            get_inlinee_summary(
                module,
                summary_cache,
                nested,
                None,
                ctx.local_object_args,
                ctx.object_effects,
            )
            .object
            .qualifies_for_helper_budget()
        })
        .take(2)
        .count() as i32
        * config.object_helper_cluster_bonus
}

fn get_inlinee_summary(
    module: &Module,
    summary_cache: &mut FxHashMap<SummaryKey, InlineeSummary>,
    callee_ref: FuncRef,
    callee: Option<&Function>,
    local_object_args: Option<&LocalObjectArgMap>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> InlineeSummary {
    *summary_cache
        .entry(match callee {
            Some(_) => SummaryKey::Snapshot(callee_ref),
            None => SummaryKey::Live(callee_ref),
        })
        .or_insert_with(|| {
            callee.map_or_else(
                || {
                    module
                        .func_store
                        .try_view(callee_ref, |func| {
                            compute_inlinee_summary(
                                callee_ref,
                                func,
                                local_object_args,
                                object_effects,
                            )
                        })
                        .unwrap_or_default()
                },
                |func| compute_inlinee_summary(callee_ref, func, local_object_args, object_effects),
            )
        })
}

fn compute_inlinee_summary(
    func_ref: FuncRef,
    func: &Function,
    local_object_args: Option<&LocalObjectArgMap>,
    object_effects: Option<&ObjectEffectSummaryMap>,
) -> InlineeSummary {
    let Some(_entry) = func.layout.entry_block() else {
        return InlineeSummary {
            has_body: false,
            ..Default::default()
        };
    };

    let mut cfg = ControlFlowGraph::default();
    cfg.compute(func);

    let mut reachable_rpo: Vec<BlockId> = cfg.post_order().collect();
    reachable_rpo.reverse();

    let mut blocks = 0usize;
    let mut insts = 0usize;
    let mut calls = 0usize;
    let mut phis = 0usize;
    let mut returns = 0usize;
    let mut base_cost = 0i32;
    let mut object = ObjectOptimizationSummary {
        local_object_arg_count: local_object_args
            .and_then(|args| args.get(&func_ref))
            .map_or(0, |args| args.len()),
        fresh_object_return_count: object_effects
            .and_then(|effects| effects.get(&func_ref))
            .map_or(0, |summary| {
                matches!(summary.ret_effect, ObjectReturnEffect::FreshObject) as usize
            }),
        ..Default::default()
    };

    for block in reachable_rpo {
        blocks += 1;
        for inst_id in func.layout.iter_inst(block) {
            insts += 1;

            if downcast::<&data::ObjLoad>(func.inst_set(), func.dfg.inst(inst_id)).is_some() {
                object.object_load_count += 1;
            } else if downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
            {
                object.object_store_count += 1;
            } else if downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
                || downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
                || downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
            {
                object.object_slice_count += 1;
            } else if downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst_id))
                .is_some()
                || downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
                || downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst_id))
                    .is_some()
            {
                object.enum_object_op_count += 1;
            }

            if func.dfg.is_phi(inst_id) {
                phis += 1;
                base_cost += 1;
                continue;
            }

            if func.dfg.is_return(inst_id) {
                returns += 1;
            }

            if func.dfg.is_call(inst_id) {
                calls += 1;
                base_cost += 5;
                continue;
            }

            base_cost += match func.dfg.side_effect(inst_id) {
                SideEffect::None => 1,
                SideEffect::Read => 2,
                SideEffect::Write => 3,
                SideEffect::Control => {
                    if func.dfg.is_return(inst_id) {
                        1
                    } else {
                        2
                    }
                }
            };
        }
    }

    if blocks > 1 {
        base_cost += ((blocks - 1) * 3) as i32;
    }

    let mut cfg_scc = CfgSccAnalysis::new();
    cfg_scc.compute(&cfg);
    let has_loop = cfg_scc
        .topo_order()
        .iter()
        .any(|&scc| cfg_scc.scc_data(scc).is_cycle);
    object.likely_scalarizable = object.tracked_root_count() > 0 && object.object_op_count() > 0;
    object.scalarization_unlock_score = if object.likely_scalarizable {
        (object.local_object_arg_count as i32 * 4)
            + (object.fresh_object_return_count as i32 * 5)
            + (object.object_store_count.min(4) as i32 * 2)
            + object.object_load_count.min(4) as i32
            + object.object_slice_count.min(4) as i32
            + (object.enum_object_op_count.min(4) as i32 * 2)
    } else {
        0
    };

    InlineeSummary {
        has_body: true,
        blocks,
        insts,
        calls,
        phis,
        returns,
        has_loop,
        base_cost,
        object,
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashMap;

    use super::{InlineDecision, InlineDecisionContext, InlineRequest, decide_inline};
    use crate::{
        module_analysis,
        optim::{
            aggregate::{
                collect_local_object_arg_info_with_effects, compute_object_effect_summaries,
            },
            inliner::InlinerConfig,
        },
    };

    #[test]
    fn cluster_bonus_flips_object_helper_wrapper_profitability() {
        let mut parsed = sonatina_parser::parse_module(
            r#"
target = "evm-ethereum-london"

type @pair = { i256, i256 };

func private %write_first(v0.objref<@pair>, v1.i256) {
    block0:
        v2.objref<i256> = obj.proj v0 0.i8;
        obj.store v2 v1;
        return;
}

func private %write_second(v0.objref<@pair>, v1.i256) {
    block0:
        v2.objref<i256> = obj.proj v0 1.i8;
        obj.store v2 v1;
        return;
}

func private %build(v0.objref<@pair>, v1.i256, v2.i256) -> i256 {
    block0:
        call %write_first v0 v1;
        call %write_second v0 v2;
        v3.objref<i256> = obj.proj v0 0.i8;
        v4.i256 = obj.load v3;
        return v4;
}

func private %caller(v0.objref<@pair>, v1.i256, v2.i256, v3.i256, v4.i256) -> i256 {
    block0:
        v5.i256 = call %build v0 v1 v2;
        v6.i256 = call %build v0 v3 v4;
        v7.i256 = add v5 v6;
        return v7;
}
"#,
        )
        .unwrap_or_else(|errs| panic!("parse failed: {errs:?}"));
        let module = &mut parsed.module;
        let analysis = module_analysis::analyze_module(module);
        let object_effects = compute_object_effect_summaries(module);
        let local_object_args = collect_local_object_arg_info_with_effects(module, &object_effects);
        let build = module
            .funcs()
            .into_iter()
            .find(|&func| module.ctx.func_sig(func, |sig| sig.name() == "build"))
            .expect("build should exist");
        let request = InlineRequest {
            callee_ref: build,
            callee_call_count: 2,
            caller_growth: 0,
            total_growth: 0,
            callee_depth: 0,
            call_has_result: true,
        };

        let disabled = decide_inline(
            module,
            &mut FxHashMap::default(),
            None,
            false,
            InlineDecisionContext {
                module_info: &analysis,
                local_object_args: Some(&local_object_args),
                object_effects: Some(&object_effects),
            },
            request,
            &InlinerConfig {
                enable_full_inliner: true,
                always_inline_single_use: false,
                max_inlinee_blocks: 64,
                max_inlinee_insts: 1024,
                max_multi_use_inlinee_blocks: 1,
                max_multi_use_inlinee_insts: 6,
                max_growth_per_caller: 4096,
                max_total_growth: 1 << 20,
                inline_threshold: 1000,
                inline_threshold_cold: 4,
                object_scalarization_bonus_cap: 4,
                object_helper_cluster_bonus: 0,
                ..InlinerConfig::default()
            },
        );
        assert!(matches!(
            disabled,
            InlineDecision::Skip(super::InlineSkipReason::Cost)
        ));

        let enabled = decide_inline(
            module,
            &mut FxHashMap::default(),
            None,
            false,
            InlineDecisionContext {
                module_info: &analysis,
                local_object_args: Some(&local_object_args),
                object_effects: Some(&object_effects),
            },
            request,
            &InlinerConfig {
                enable_full_inliner: true,
                always_inline_single_use: false,
                max_inlinee_blocks: 64,
                max_inlinee_insts: 1024,
                max_multi_use_inlinee_blocks: 1,
                max_multi_use_inlinee_insts: 6,
                max_growth_per_caller: 4096,
                max_total_growth: 1 << 20,
                inline_threshold: 1000,
                inline_threshold_cold: 4,
                object_scalarization_bonus_cap: 4,
                object_helper_cluster_bonus: 3,
                ..InlinerConfig::default()
            },
        );
        assert!(matches!(enabled, InlineDecision::Inline(_)));
    }
}
