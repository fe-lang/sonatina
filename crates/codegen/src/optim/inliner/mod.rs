use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, InstDowncast, InstId, Module, inst::control_flow,
    module::FuncRef,
};

use crate::module_analysis;

mod cost;
mod full;
mod rewrite;
mod trivial;

#[derive(Clone, Copy)]
struct CallSite {
    call_inst: InstId,
    callee: FuncRef,
    has_result: bool,
}

#[derive(Clone, Copy, Debug)]
pub struct InlinerConfig {
    pub enable_noop: bool,
    pub enable_return_alias: bool,
    pub enable_wrapper_rewrite: bool,
    pub enable_single_block_splice: bool,

    pub splice_max_insts: usize,
    pub splice_require_pure: bool,

    pub enable_full_inliner: bool,

    pub max_inlinee_blocks: usize,
    pub max_inlinee_insts: usize,
    pub max_growth_per_caller: usize,
    pub max_total_growth: usize,
    pub max_inline_depth: usize,
    pub allow_inline_recursive: bool,

    pub always_inline_single_use: bool,
    pub multi_block_multi_use_penalty: i32,

    pub inline_threshold: i32,
    pub inline_threshold_cold: i32,
    pub single_use_bonus: i32,
    pub leaf_bonus: i32,
    pub loop_penalty: i32,
}

impl Default for InlinerConfig {
    fn default() -> Self {
        Self {
            enable_noop: true,
            enable_return_alias: true,
            enable_wrapper_rewrite: true,
            enable_single_block_splice: true,

            splice_max_insts: 6,
            splice_require_pure: false,

            enable_full_inliner: false,

            max_inlinee_blocks: 0,
            max_inlinee_insts: 0,
            max_growth_per_caller: 0,
            max_total_growth: 0,
            max_inline_depth: 8,
            allow_inline_recursive: false,

            always_inline_single_use: true,
            multi_block_multi_use_penalty: 12,

            inline_threshold: 24,
            inline_threshold_cold: 12,
            single_use_bonus: 12,
            leaf_bonus: 4,
            loop_penalty: 20,
        }
    }
}

#[derive(Default)]
pub struct InlineStats {
    pub calls_removed: usize,
    pub calls_rewritten: usize,
    pub calls_spliced: usize,
    pub skipped_no_body: usize,
    pub skipped_multi_block: usize,
    pub skipped_non_straight_line: usize,
    pub skipped_not_pure: usize,
    pub skipped_effectful: usize,
    pub skipped_too_large: usize,

    pub full_calls_inlined: usize,
    pub full_blocks_cloned: usize,
    pub full_insts_cloned: usize,
    pub full_phi_fixups: usize,
    pub skipped_recursive_scc: usize,
    pub skipped_budget: usize,
    pub skipped_cost: usize,
    pub skipped_sig_mismatch: usize,
    pub skipped_callsite_unreachable: usize,
}

pub struct Inliner {
    pub config: InlinerConfig,
}

impl Inliner {
    pub fn new(config: InlinerConfig) -> Self {
        Self { config }
    }

    pub fn run(&mut self, module: &mut Module) -> InlineStats {
        const MAX_ITERS: usize = 8;
        let mut stats = InlineStats::default();

        let mut total_growth = 0usize;
        let mut inline_depth_by_func: FxHashMap<FuncRef, usize> = FxHashMap::default();
        let mut growth_by_caller: FxHashMap<FuncRef, usize> = FxHashMap::default();

        let mut iter = 0;
        while iter < MAX_ITERS {
            let funcs = module.funcs();
            let (sites_by_caller, call_counts) = collect_iteration_call_data(module, &funcs);
            let analysis = module_analysis::analyze_module(module);
            let mut inlinee_summaries: FxHashMap<FuncRef, cost::InlineeSummary> =
                FxHashMap::default();

            let mut changed = false;
            for caller_ref in funcs {
                let mut reachable_blocks: Option<FxHashSet<BlockId>> = None;
                let sites = sites_by_caller
                    .get(&caller_ref)
                    .cloned()
                    .unwrap_or_default();

                for site in sites {
                    if site.callee == caller_ref && !self.config.allow_inline_recursive {
                        stats.skipped_recursive_scc += 1;
                        continue;
                    }

                    let callee_calls = call_counts.get(&site.callee).copied().unwrap_or(0);

                    let trivial_plan = module.func_store.view(site.callee, |callee| {
                        trivial::analyze_callee(
                            module,
                            site.callee,
                            callee,
                            callee_calls,
                            &self.config,
                            &mut stats,
                        )
                    });
                    let did_trivial = if let Some(plan_summary) = trivial_plan {
                        let plan = module.func_store.view(site.callee, |callee| {
                            trivial::materialize_plan(callee, &plan_summary)
                        });
                        module.func_store.modify(caller_ref, |caller| {
                            trivial::apply_plan(caller, site.call_inst, plan, &mut stats)
                        })
                    } else {
                        false
                    };
                    if did_trivial {
                        changed = true;
                        // Trivial inlining may change the caller CFG; drop cached reachability.
                        reachable_blocks = None;
                        continue;
                    }

                    if !self.config.enable_full_inliner {
                        continue;
                    }

                    // Avoid nested `view` + `modify` locks. With DashMap sharding, those can
                    // deadlock when caller/callee hash to the same shard.
                    if site.callee == caller_ref {
                        stats.skipped_recursive_scc += 1;
                        continue;
                    }

                    let decision = cost::decide_inline(
                        module,
                        &analysis,
                        &mut inlinee_summaries,
                        cost::InlineRequest {
                            caller_ref,
                            callee_ref: site.callee,
                            callee_call_count: callee_calls,
                            caller_growth: growth_by_caller.get(&caller_ref).copied().unwrap_or(0),
                            total_growth,
                            callee_depth: inline_depth_by_func
                                .get(&site.callee)
                                .copied()
                                .unwrap_or(0),
                            call_has_result: site.has_result,
                        },
                        &self.config,
                    );

                    let cost::InlineDecision::Inline(plan) = decision else {
                        apply_inline_skip(decision, &mut stats);
                        continue;
                    };

                    let Some(mut caller_func) = module.func_store.remove(caller_ref) else {
                        stats.skipped_no_body += 1;
                        continue;
                    };

                    let Some(call_block) = caller_func.layout.try_inst_block(site.call_inst) else {
                        module.func_store.restore(caller_ref, caller_func);
                        continue;
                    };

                    if !reachable_blocks
                        .get_or_insert_with(|| compute_reachable_blocks(&caller_func))
                        .contains(&call_block)
                    {
                        stats.skipped_callsite_unreachable += 1;
                        module.func_store.restore(caller_ref, caller_func);
                        continue;
                    }

                    let full_result = module.func_store.view(site.callee, |callee| {
                        full::try_inline_callsite_full(
                            module,
                            caller_ref,
                            &mut caller_func,
                            site.call_inst,
                            site.callee,
                            callee,
                            &self.config,
                        )
                    });
                    module.func_store.restore(caller_ref, caller_func);

                    match full_result {
                        Ok(result) => {
                            changed = true;
                            let _ = (plan.summary.blocks, plan.predicted_growth, plan.score);

                            stats.full_calls_inlined += 1;
                            stats.full_blocks_cloned += result.blocks_cloned;
                            stats.full_insts_cloned += result.insts_cloned;
                            stats.full_phi_fixups += result.phi_fixups;

                            *growth_by_caller.entry(caller_ref).or_insert(0) += result.net_growth;
                            total_growth += result.net_growth;

                            let callee_depth =
                                inline_depth_by_func.get(&site.callee).copied().unwrap_or(0);
                            let caller_depth =
                                inline_depth_by_func.get(&caller_ref).copied().unwrap_or(0);
                            inline_depth_by_func
                                .insert(caller_ref, caller_depth.max(callee_depth + 1));

                            let _ = plan.forced;

                            // Full inlining changes the CFG, so any cached reachable-set
                            // for this caller is now stale (new blocks inserted/split).
                            reachable_blocks = None;
                        }
                        Err(full::FullInlineFail::SignatureMismatch) => {
                            stats.skipped_sig_mismatch += 1;
                        }
                        Err(full::FullInlineFail::NoBody) => {
                            stats.skipped_no_body += 1;
                        }
                        Err(full::FullInlineFail::CallGone)
                        | Err(full::FullInlineFail::NotCall)
                        | Err(full::FullInlineFail::CalleeMismatch)
                        | Err(full::FullInlineFail::MalformedCallee) => {
                            // Conservatively drop reachability cache; malformed callee
                            // indicates we may have bailed out mid-transform.
                            reachable_blocks = None;
                        }
                    }
                }
            }

            if !changed {
                break;
            }

            iter += 1;
        }

        stats
    }
}

fn apply_inline_skip(decision: cost::InlineDecision, stats: &mut InlineStats) {
    let cost::InlineDecision::Skip(reason) = decision else {
        return;
    };

    match reason {
        cost::InlineSkipReason::NoBody => stats.skipped_no_body += 1,
        cost::InlineSkipReason::RecursiveScc => stats.skipped_recursive_scc += 1,
        cost::InlineSkipReason::Budget => stats.skipped_budget += 1,
        cost::InlineSkipReason::Cost => stats.skipped_cost += 1,
        cost::InlineSkipReason::NoInlineAttr => stats.skipped_cost += 1,
    }
}

fn collect_call_sites(func: &Function) -> Vec<CallSite> {
    let is = func.inst_set();
    let mut sites = Vec::new();

    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            let inst = func.dfg.inst(inst_id);
            let Some(call) = <&control_flow::Call as InstDowncast>::downcast(is, inst) else {
                continue;
            };

            sites.push(CallSite {
                call_inst: inst_id,
                callee: *call.callee(),
                has_result: func.dfg.inst_result(inst_id).is_some(),
            });
        }
    }

    sites
}

fn collect_iteration_call_data(
    module: &Module,
    funcs: &[FuncRef],
) -> (FxHashMap<FuncRef, Vec<CallSite>>, FxHashMap<FuncRef, usize>) {
    let mut sites_by_caller: FxHashMap<FuncRef, Vec<CallSite>> = FxHashMap::default();
    let mut counts: FxHashMap<FuncRef, usize> = FxHashMap::default();

    for &caller in funcs {
        let sites = module.func_store.view(caller, collect_call_sites);
        for site in &sites {
            *counts.entry(site.callee).or_insert(0) += 1;
        }
        sites_by_caller.insert(caller, sites);
    }

    (sites_by_caller, counts)
}

fn compute_reachable_blocks(func: &Function) -> FxHashSet<BlockId> {
    let mut cfg = ControlFlowGraph::default();
    cfg.compute(func);
    cfg.post_order().collect()
}
