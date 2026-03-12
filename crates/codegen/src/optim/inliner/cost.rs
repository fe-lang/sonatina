use rustc_hash::FxHashMap;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Module,
    inst::SideEffect,
    module::{FuncHints, FuncRef},
};

use crate::{cfg_scc::CfgSccAnalysis, module_analysis::ModuleInfo};

use super::InlinerConfig;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum SummaryKey {
    Live(FuncRef),
    Snapshot(FuncRef),
}

pub(super) fn decide_inline(
    module: &Module,
    module_info: &ModuleInfo,
    summary_cache: &mut FxHashMap<SummaryKey, InlineeSummary>,
    callee: Option<&Function>,
    recursive_callsite: bool,
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

    let summary = *summary_cache
        .entry(match callee {
            Some(_) => SummaryKey::Snapshot(request.callee_ref),
            None => SummaryKey::Live(request.callee_ref),
        })
        .or_insert_with(|| {
            callee.map_or_else(
                || {
                    module
                        .func_store
                        .try_view(request.callee_ref, compute_inlinee_summary)
                        .unwrap_or_default()
                },
                compute_inlinee_summary,
            )
        });

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

    let is_leaf = module_info
        .func_info
        .get(&request.callee_ref)
        .map(|info| info.is_leaf)
        .unwrap_or_else(|| {
            module_info
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

fn compute_inlinee_summary(func: &Function) -> InlineeSummary {
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

    for block in reachable_rpo {
        blocks += 1;
        for inst_id in func.layout.iter_inst(block) {
            insts += 1;

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

    InlineeSummary {
        has_body: true,
        blocks,
        insts,
        calls,
        phis,
        returns,
        has_loop,
        base_cost,
    }
}
