use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Linkage, Module,
    inst::{control_flow, data, downcast},
    module::{FuncHints, FuncRef},
};

use crate::{cfg_scc::CfgSccAnalysis, module_analysis::ModuleInfo, transform::aggregate::shape};

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
    pub scalarization: ScalarizationBenefitSummary,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct ScalarizationBenefitSummary {
    pub local_object_arg_count: usize,
    pub fresh_object_return_count: usize,
    pub object_store_count: usize,
    pub object_load_count: usize,
    pub object_slice_count: usize,
    pub enum_object_op_count: usize,
    pub aggregate_insert_count: usize,
    pub aggregate_extract_count: usize,
    pub aggregate_return_count: usize,
    pub score: i32,
}

impl ScalarizationBenefitSummary {
    fn tracked_object_root_count(self) -> usize {
        self.local_object_arg_count + self.fresh_object_return_count
    }

    fn object_op_count(self) -> usize {
        self.object_store_count
            + self.object_load_count
            + self.object_slice_count
            + self.enum_object_op_count
    }

    fn aggregate_value_op_count(self) -> usize {
        self.aggregate_insert_count + self.aggregate_extract_count
    }

    fn has_object_opportunity(self) -> bool {
        self.tracked_object_root_count() > 0 && self.object_op_count() > 0
    }

    fn has_aggregate_value_opportunity(self) -> bool {
        self.aggregate_value_op_count() > 0
    }

    fn has_opportunity(self) -> bool {
        self.has_object_opportunity() || self.has_aggregate_value_opportunity()
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) struct InlineRequest {
    pub callee_ref: FuncRef,
    pub callee_call_count: usize,
    pub caller_growth: usize,
    pub total_growth: usize,
    pub callee_depth: usize,
    pub call_arg_count: usize,
    pub call_result_count: usize,
    pub call_returns_to_caller: bool,
    pub call_callee_may_commit: bool,
    pub call_continuation_may_commit: bool,
    pub known_arg_mask: u128,
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

    let mut predicted_growth = summary.insts.saturating_sub(1);
    if request.call_result_count > 0 && summary.returns > 1 {
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

    // A plain inline hint is a strong preference: bypass the local inlinee and
    // cost heuristics once the callsite has cleared hard legality, recursion,
    // growth, and depth constraints.
    if hints.contains(FuncHints::INLINEHINT) {
        return InlineDecision::Inline(InlinePlan {
            summary,
            score: i32::MIN + 2,
            predicted_growth,
            forced: true,
        });
    }

    if exceeds_cap(summary.blocks, config.max_inlinee_blocks)
        || exceeds_cap(summary.insts, config.max_inlinee_insts)
    {
        return InlineDecision::Skip(InlineSkipReason::Budget);
    }

    let should_force_single_use = config.always_inline_single_use
        && request.callee_call_count == 1
        && summary.blocks > 1
        && (request.call_continuation_may_commit
            || (!request.call_returns_to_caller && request.call_callee_may_commit));

    if should_force_single_use {
        return InlineDecision::Inline(InlinePlan {
            summary,
            score: i32::MIN + 1,
            predicted_growth,
            forced: true,
        });
    }

    let should_force_small_cleanup_helper = request.call_continuation_may_commit
        && is_multi_block_small_leaf_helper(summary, config)
        && (request.known_arg_mask != 0
            || (config.scalarization_bonus_cap > 0 && summary.scalarization.has_opportunity()));

    if should_force_small_cleanup_helper {
        return InlineDecision::Inline(InlinePlan {
            summary,
            score: i32::MIN + 2,
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

    let threshold = if summary.has_loop || summary.calls > 0 {
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
    if request.callee_call_count == 1 {
        score -= config.single_use_bonus;
    }
    if is_leaf {
        score -= config.leaf_bonus;
    }
    // Small leaf helpers often shrink after the next simplification round; avoid
    // letting the multi-use code-size model dominate those callsites too early.
    if config.small_function_bonus > 0 && is_small_leaf_helper(summary, config) {
        score -= config.small_function_bonus;
    }
    score -= compute_call_overhead_bonus(request, config);
    // Known actual arguments can expose constant branches, allocation sizes, and
    // return fields once the callee body is in the caller.
    score -= compute_callsite_known_arg_bonus(module, callee, request, config);
    if request.callee_call_count > 1 && summary.blocks > 1 {
        score += summary.blocks.saturating_sub(1) as i32 * config.duplicated_block_penalty;
    }
    if request.callee_call_count > 1 {
        score += summary
            .insts
            .saturating_sub(config.multi_use_inst_free_allowance) as i32
            * request.callee_call_count.saturating_sub(1) as i32
            * config.multi_use_excess_inst_penalty;
    }
    if hints.contains(FuncHints::INLINEHINT) {
        score -= 2;
    }
    score -= summary
        .scalarization
        .score
        .min(config.scalarization_bonus_cap);
    score -= compute_scalarization_helper_cluster_bonus(
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

fn is_small_leaf_helper(summary: InlineeSummary, config: &InlinerConfig) -> bool {
    summary.calls == 0
        && !summary.has_loop
        && !exceeds_cap(summary.blocks, config.small_function_block_limit)
        && !exceeds_cap(summary.insts, config.small_function_inst_limit)
}

fn is_multi_block_small_leaf_helper(summary: InlineeSummary, config: &InlinerConfig) -> bool {
    summary.blocks > 1 && is_small_leaf_helper(summary, config)
}

fn compute_scalarization_helper_cluster_bonus(
    module: &Module,
    summary_cache: &mut FxHashMap<SummaryKey, InlineeSummary>,
    ctx: InlineDecisionContext<'_>,
    callee_ref: FuncRef,
    summary: InlineeSummary,
    config: &InlinerConfig,
) -> i32 {
    if config.scalarization_helper_cluster_bonus <= 0
        || module.ctx.func_linkage(callee_ref) != Linkage::Private
        || !summary.scalarization.has_opportunity()
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
            .scalarization
            .has_opportunity()
        })
        .take(2)
        .count() as i32
        * config.scalarization_helper_cluster_bonus
}

fn compute_callsite_known_arg_bonus(
    module: &Module,
    callee: Option<&Function>,
    request: InlineRequest,
    config: &InlinerConfig,
) -> i32 {
    if request.known_arg_mask == 0
        || config.callsite_known_arg_use_bonus <= 0
        || config.callsite_known_arg_bonus_cap <= 0
    {
        return 0;
    }

    let use_score = callee.map_or_else(
        || {
            module
                .func_store
                .try_view(request.callee_ref, |func| {
                    known_arg_use_score(func, request.known_arg_mask)
                })
                .unwrap_or(0)
        },
        |func| known_arg_use_score(func, request.known_arg_mask),
    );

    (use_score as i32 * config.callsite_known_arg_use_bonus)
        .min(config.callsite_known_arg_bonus_cap)
}

fn compute_call_overhead_bonus(request: InlineRequest, config: &InlinerConfig) -> i32 {
    let mut bonus = config.call_overhead_bonus.max(0);
    if !request.call_returns_to_caller || !request.call_continuation_may_commit {
        return bonus;
    }

    bonus += config.call_return_overhead_bonus.max(0);
    if request.call_arg_count > 0 {
        bonus += config.call_arg_shuffle_bonus.max(0);
    }
    bonus + request.call_result_count as i32 * config.call_result_shuffle_bonus.max(0)
}

fn known_arg_use_score(func: &Function, known_arg_mask: u128) -> usize {
    func.arg_values
        .iter()
        .enumerate()
        .filter(|(index, _)| {
            *index < u128::BITS as usize && known_arg_mask & (1u128 << *index) != 0
        })
        .map(|(_, &arg)| func.dfg.users_num(arg).min(4))
        .sum()
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
    let mut scalarization = ScalarizationBenefitSummary {
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
                scalarization.object_load_count += 1;
            } else if downcast::<&data::ObjStore>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
            {
                scalarization.object_store_count += 1;
            } else if downcast::<&data::ObjProj>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
                || downcast::<&data::ObjIndex>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
                || downcast::<&data::EnumProj>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
            {
                scalarization.object_slice_count += 1;
            } else if downcast::<&data::EnumGetTag>(func.inst_set(), func.dfg.inst(inst_id))
                .is_some()
                || downcast::<&data::EnumSetTag>(func.inst_set(), func.dfg.inst(inst_id)).is_some()
                || downcast::<&data::EnumWriteVariant>(func.inst_set(), func.dfg.inst(inst_id))
                    .is_some()
            {
                scalarization.enum_object_op_count += 1;
            } else if let Some(insert) =
                downcast::<&data::InsertValue>(func.inst_set(), func.dfg.inst(inst_id))
                && is_scalarizable_aggregate_value(func, *insert.dest())
            {
                scalarization.aggregate_insert_count += 1;
            } else if let Some(extract) =
                downcast::<&data::ExtractValue>(func.inst_set(), func.dfg.inst(inst_id))
                && is_scalarizable_aggregate_value(func, *extract.dest())
            {
                scalarization.aggregate_extract_count += 1;
            }

            if func.dfg.is_phi(inst_id) {
                phis += 1;
                base_cost += 1;
                continue;
            }

            if func.dfg.is_return(inst_id) {
                returns += 1;
                if let Some(ret) =
                    downcast::<&control_flow::Return>(func.inst_set(), func.dfg.inst(inst_id))
                {
                    scalarization.aggregate_return_count += ret
                        .args()
                        .iter()
                        .filter(|&&arg| is_scalarizable_aggregate_value(func, arg))
                        .count();
                }
            }

            if func.dfg.is_call(inst_id) {
                calls += 1;
                base_cost += 5;
                continue;
            }

            base_cost += func.dfg.effect_cost_class(inst_id).base_cost();
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
    scalarization.score = compute_scalarization_benefit_score(scalarization);

    InlineeSummary {
        has_body: true,
        blocks,
        insts,
        calls,
        phis,
        returns,
        has_loop,
        base_cost,
        scalarization,
    }
}

fn is_scalarizable_aggregate_value(func: &Function, value: sonatina_ir::ValueId) -> bool {
    shape::is_supported_scalar_shape_ty(func.ctx(), func.dfg.value_ty(value))
}

fn compute_scalarization_benefit_score(summary: ScalarizationBenefitSummary) -> i32 {
    let mut score = 0;
    if summary.has_object_opportunity() {
        score += (summary.local_object_arg_count as i32 * 4)
            + (summary.fresh_object_return_count as i32 * 5)
            + (summary.object_store_count.min(4) as i32 * 2)
            + summary.object_load_count.min(4) as i32
            + summary.object_slice_count.min(4) as i32
            + (summary.enum_object_op_count.min(4) as i32 * 2);
    }
    if summary.has_aggregate_value_opportunity() {
        score += (summary.aggregate_insert_count.min(6) as i32 * 2)
            + summary.aggregate_extract_count.min(6) as i32
            + (summary.aggregate_return_count.min(2) as i32 * 5);
    }
    score
}
