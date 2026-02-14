//! Module-level inliner pass (single-block callees).
//!
//! This pass intentionally avoids CFG surgery: it only removes calls, rewrites
//! wrapper calls, or splices a straight-line single-block callee body into the
//! caller block. Purity filtering is optional (`splice_require_pure`).

use std::collections::BTreeMap;

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, GlobalVariableRef, Immediate, Inst, InstDowncast, InstId, Module, Type, Value,
    ValueId,
    inst::{SideEffect, control_flow},
    module::{FuncRef, ModuleCtx},
};

use crate::cfg_edit::{CfgEditor, CleanupMode};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueTemplate {
    Arg(usize),
    Imm(Immediate),
    Global(GlobalVariableRef),
    Undef(Type),
}

enum InlinePlan {
    /// Delete the call; optionally alias its result to a materialized value.
    RemoveCall { returned: Option<ValueTemplate> },
    /// Rewrite the call into a call to a different direct callee.
    RewriteCall {
        new_callee: FuncRef,
        new_args: Vec<ValueTemplate>,
    },
    /// Splice a pure, single-block body into caller before callsite.
    SpliceSingleBlock(SplicePlan),
    /// Splice a single-block callee that terminates the caller (e.g. `evm_revert`).
    SpliceSingleBlockTerminator(TerminatorSplicePlan),
}

struct TemplateInst {
    inst: Box<dyn Inst>,
    old_result: Option<(ValueId, Type)>,
}

#[derive(Clone, Copy)]
struct TemplateInstSummary {
    inst_id: InstId,
    old_result: Option<(ValueId, Type)>,
}

struct SplicePlan {
    callee_args: Vec<ValueId>,
    const_values: BTreeMap<ValueId, ValueTemplate>,
    body: Vec<TemplateInst>,
    ret_value: Option<ValueId>,
}

struct TerminatorSplicePlan {
    callee_args: Vec<ValueId>,
    const_values: BTreeMap<ValueId, ValueTemplate>,
    body: Vec<TemplateInst>,
    terminator: Box<dyn Inst>,
}

#[derive(Clone)]
struct SplicePlanSummary {
    callee_args: Vec<ValueId>,
    const_values: BTreeMap<ValueId, ValueTemplate>,
    body: Vec<TemplateInstSummary>,
    ret_value: Option<ValueId>,
}

#[derive(Clone)]
struct TerminatorSplicePlanSummary {
    callee_args: Vec<ValueId>,
    const_values: BTreeMap<ValueId, ValueTemplate>,
    body: Vec<TemplateInstSummary>,
    term_inst_id: InstId,
}

#[derive(Clone)]
enum InlinePlanSummary {
    RemoveCall {
        returned: Option<ValueTemplate>,
    },
    RewriteCall {
        new_callee: FuncRef,
        new_args: Vec<ValueTemplate>,
    },
    SpliceSingleBlock(SplicePlanSummary),
    SpliceSingleBlockTerminator(TerminatorSplicePlanSummary),
}

struct CollectedSpliceBody {
    const_values: BTreeMap<ValueId, ValueTemplate>,
    body: Vec<TemplateInstSummary>,
}

#[derive(Clone, Copy)]
struct CallSite {
    call_inst: InstId,
    callee: FuncRef,
}

#[derive(Clone, Copy)]
pub struct InlinerConfig {
    pub enable_noop: bool,
    pub enable_return_alias: bool,
    pub enable_wrapper_rewrite: bool,
    pub enable_single_block_splice: bool,

    pub splice_max_insts: usize,
    pub splice_require_pure: bool,

    // Future multi-block inlining knobs (kept for API continuity).
    pub max_inlinee_blocks: usize,
    pub max_inlinee_insts: usize,
    pub max_growth_per_caller: usize,
    pub allow_inline_recursive: bool,
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

            max_inlinee_blocks: 0,
            max_inlinee_insts: 0,
            max_growth_per_caller: 0,
            allow_inline_recursive: false,
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
    /// Aggregate of non-straight-line and not-pure skips.
    pub skipped_effectful: usize,
    pub skipped_too_large: usize,
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

        let mut iter = 0;
        while iter < MAX_ITERS {
            let mut changed = false;
            let funcs = module.funcs();
            let (sites_by_caller, call_counts) = collect_iteration_call_data(module, &funcs);
            let mut callee_summary_cache: FxHashMap<FuncRef, Option<InlinePlanSummary>> =
                FxHashMap::default();

            for caller in funcs {
                let sites = sites_by_caller.get(&caller).cloned().unwrap_or_default();
                let mut caller_changed = false;

                for site in sites {
                    if site.callee == caller && !self.config.allow_inline_recursive {
                        continue;
                    }

                    let plan_summary = if let Some(cached) = callee_summary_cache.get(&site.callee)
                    {
                        cached.clone()
                    } else {
                        let callee_call_count = call_counts.get(&site.callee).copied().unwrap_or(0);
                        let analyzed = module.func_store.view(site.callee, |callee_func| {
                            analyze_callee(
                                module,
                                site.callee,
                                callee_func,
                                callee_call_count,
                                &self.config,
                                &mut stats,
                            )
                        });
                        callee_summary_cache.insert(site.callee, analyzed.clone());
                        analyzed
                    };

                    let Some(plan_summary) = plan_summary else {
                        continue;
                    };
                    let plan = module.func_store.view(site.callee, |callee_func| {
                        materialize_plan(callee_func, &plan_summary)
                    });

                    let applied = module.func_store.modify(caller, |caller_func| {
                        apply_plan(caller_func, site.call_inst, plan, &mut stats)
                    });

                    changed |= applied;
                    caller_changed |= applied;
                    if applied {
                        callee_summary_cache.remove(&caller);
                    }
                }

                if caller_changed {
                    callee_summary_cache.remove(&caller);
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

fn analyze_callee(
    module: &Module,
    callee_ref: FuncRef,
    callee: &Function,
    callee_call_count: usize,
    config: &InlinerConfig,
    stats: &mut InlineStats,
) -> Option<InlinePlanSummary> {
    if !module.ctx.func_linkage(callee_ref).has_definition() {
        stats.skipped_no_body += 1;
        return None;
    }

    let mut blocks = callee.layout.iter_block();
    let Some(block) = blocks.next() else {
        let callee_name = module
            .ctx
            .func_sig(callee_ref, |sig| sig.name().to_string());
        panic!("inliner: defined function %{callee_name} ({callee_ref:?}) has empty body");
    };
    if blocks.next().is_some() {
        stats.skipped_multi_block += 1;
        return None;
    }

    let insts: Vec<_> = callee.layout.iter_inst(block).collect();
    let Some(&term_inst_id) = insts.last() else {
        let callee_name = module
            .ctx
            .func_sig(callee_ref, |sig| sig.name().to_string());
        panic!(
            "inliner: defined function %{callee_name} ({callee_ref:?}) has an empty entry block"
        );
    };
    if !callee.dfg.is_terminator(term_inst_id) {
        let callee_name = module
            .ctx
            .func_sig(callee_ref, |sig| sig.name().to_string());
        panic!(
            "inliner: defined function %{callee_name} ({callee_ref:?}) has a non-terminator last inst"
        );
    }

    let is = callee.inst_set();
    let Some(ret_inst) =
        <&control_flow::Return as InstDowncast>::downcast(is, callee.dfg.inst(term_inst_id))
    else {
        return analyze_terminator_splice(
            callee,
            callee_call_count,
            config,
            stats,
            term_inst_id,
            &insts,
        );
    };
    let ret_value = *ret_inst.arg();

    // Pattern A/B/C: single return-only block.
    if insts.len() == 1 {
        if ret_value.is_none() {
            if config.enable_noop {
                return Some(InlinePlanSummary::RemoveCall { returned: None });
            }
            return None;
        }

        if !config.enable_return_alias {
            return None;
        }

        let template = classify_value_template(callee, ret_value?)?;
        return Some(InlinePlanSummary::RemoveCall {
            returned: Some(template),
        });
    }

    // Pattern D: wrapper forwarding (call; return).
    if insts.len() == 2 && config.enable_wrapper_rewrite {
        let call_inst_id = insts[0];
        let Some(call_inst) =
            <&control_flow::Call as InstDowncast>::downcast(is, callee.dfg.inst(call_inst_id))
        else {
            // Not a wrapper; fall through to splicing.
            return analyze_splice(callee, callee_call_count, config, stats, ret_value, &insts);
        };

        let call_res = callee.dfg.inst_result(call_inst_id);
        if call_res != ret_value {
            return None;
        }

        // Signature sanity: wrapper signature equals inner callee signature.
        if !signatures_match(&module.ctx, callee_ref, *call_inst.callee()) {
            return None;
        }

        let new_args = call_inst
            .args()
            .iter()
            .map(|&arg| classify_value_template(callee, arg))
            .collect::<Option<Vec<_>>>()?;

        return Some(InlinePlanSummary::RewriteCall {
            new_callee: *call_inst.callee(),
            new_args,
        });
    }

    analyze_splice(callee, callee_call_count, config, stats, ret_value, &insts)
}

fn analyze_splice(
    callee: &Function,
    callee_call_count: usize,
    config: &InlinerConfig,
    stats: &mut InlineStats,
    ret_value: Option<ValueId>,
    insts: &[InstId],
) -> Option<InlinePlanSummary> {
    if !config.enable_single_block_splice {
        return None;
    }

    let (_, body_insts) = insts.split_last()?;
    let mut collected = collect_splice_body(callee, callee_call_count, config, stats, body_insts)?;

    if let Some(ret_value) = ret_value
        && let Some(tpl) = classify_value_template(callee, ret_value)
    {
        record_const_value(&mut collected.const_values, ret_value, tpl);
    }

    let callee_args: Vec<ValueId> = callee.arg_values.iter().copied().collect();
    let plan = SplicePlanSummary {
        callee_args,
        const_values: collected.const_values,
        body: collected.body,
        ret_value,
    };

    Some(InlinePlanSummary::SpliceSingleBlock(plan))
}

fn analyze_terminator_splice(
    callee: &Function,
    callee_call_count: usize,
    config: &InlinerConfig,
    stats: &mut InlineStats,
    term_inst_id: InstId,
    insts: &[InstId],
) -> Option<InlinePlanSummary> {
    if !config.enable_single_block_splice {
        return None;
    }

    // Can't remap/split CFG here; only inline "exit" terminators.
    if callee.dfg.is_branch(term_inst_id) {
        return None;
    }

    let (_, body_insts) = insts.split_last()?;
    let mut collected = collect_splice_body(callee, callee_call_count, config, stats, body_insts)?;

    extend_const_values_from_inst_operands(callee, term_inst_id, &mut collected.const_values);
    let callee_args: Vec<ValueId> = callee.arg_values.iter().copied().collect();
    let plan = TerminatorSplicePlanSummary {
        callee_args,
        const_values: collected.const_values,
        body: collected.body,
        term_inst_id,
    };

    Some(InlinePlanSummary::SpliceSingleBlockTerminator(plan))
}

fn collect_splice_body(
    callee: &Function,
    callee_call_count: usize,
    config: &InlinerConfig,
    stats: &mut InlineStats,
    body_insts: &[InstId],
) -> Option<CollectedSpliceBody> {
    let is_single_use = callee_call_count == 1;
    if !is_single_use && body_insts.len() > config.splice_max_insts {
        stats.skipped_too_large += 1;
        return None;
    }

    let mut const_values: BTreeMap<ValueId, ValueTemplate> = BTreeMap::new();
    let mut body: Vec<TemplateInstSummary> = Vec::with_capacity(body_insts.len());
    let is = callee.inst_set();
    for &inst_id in body_insts {
        if callee.dfg.is_phi(inst_id)
            || callee.dfg.is_branch(inst_id)
            || callee.dfg.is_terminator(inst_id)
        {
            stats.skipped_non_straight_line += 1;
            stats.skipped_effectful += 1;
            return None;
        }

        if config.splice_require_pure
            && (callee.dfg.side_effect(inst_id) != SideEffect::None
                || <&control_flow::Call as InstDowncast>::downcast(is, callee.dfg.inst(inst_id))
                    .is_some())
        {
            stats.skipped_not_pure += 1;
            stats.skipped_effectful += 1;
            return None;
        }
        extend_const_values_from_inst_operands(callee, inst_id, &mut const_values);
        let old_result = callee
            .dfg
            .inst_result(inst_id)
            .map(|res| (res, callee.dfg.value_ty(res)));
        body.push(TemplateInstSummary {
            inst_id,
            old_result,
        });
    }

    Some(CollectedSpliceBody { const_values, body })
}

fn materialize_plan(callee: &Function, summary: &InlinePlanSummary) -> InlinePlan {
    match summary {
        InlinePlanSummary::RemoveCall { returned } => InlinePlan::RemoveCall {
            returned: *returned,
        },
        InlinePlanSummary::RewriteCall {
            new_callee,
            new_args,
        } => InlinePlan::RewriteCall {
            new_callee: *new_callee,
            new_args: new_args.clone(),
        },
        InlinePlanSummary::SpliceSingleBlock(summary) => {
            InlinePlan::SpliceSingleBlock(SplicePlan {
                callee_args: summary.callee_args.clone(),
                const_values: summary.const_values.clone(),
                body: materialize_body_templates(callee, &summary.body),
                ret_value: summary.ret_value,
            })
        }
        InlinePlanSummary::SpliceSingleBlockTerminator(summary) => {
            InlinePlan::SpliceSingleBlockTerminator(TerminatorSplicePlan {
                callee_args: summary.callee_args.clone(),
                const_values: summary.const_values.clone(),
                body: materialize_body_templates(callee, &summary.body),
                terminator: callee.dfg.clone_inst(summary.term_inst_id),
            })
        }
    }
}

fn materialize_body_templates(
    callee: &Function,
    body: &[TemplateInstSummary],
) -> Vec<TemplateInst> {
    body.iter()
        .map(|summary| TemplateInst {
            inst: callee.dfg.clone_inst(summary.inst_id),
            old_result: summary.old_result,
        })
        .collect()
}

fn apply_plan(
    caller: &mut Function,
    call_inst_id: InstId,
    plan: InlinePlan,
    stats: &mut InlineStats,
) -> bool {
    if !caller.layout.is_inst_inserted(call_inst_id) {
        return false;
    }

    let is = caller.inst_set();
    let Some((call_args, original_callee)) =
        <&control_flow::Call as InstDowncast>::downcast(is, caller.dfg.inst(call_inst_id))
            .map(|call_inst| (call_inst.args().clone(), *call_inst.callee()))
    else {
        return false;
    };
    let call_res = caller.dfg.inst_result(call_inst_id);

    match plan {
        InlinePlan::RemoveCall { returned } => {
            if call_res.is_some() && returned.is_none() {
                return false;
            }

            if let Some((call_res, tpl)) = call_res.zip(returned.as_ref()) {
                let Some(alias) = materialize(tpl, caller, &call_args) else {
                    return false;
                };
                debug_assert_alias_type_match(caller, call_res, alias);
                caller.dfg.change_to_alias(call_res, alias);
            }

            caller.dfg.untrack_inst(call_inst_id);
            caller.layout.remove_inst(call_inst_id);
            stats.calls_removed += 1;
            true
        }
        InlinePlan::RewriteCall {
            new_callee,
            new_args,
        } => {
            let Some(args) = new_args
                .iter()
                .map(|tpl| materialize(tpl, caller, &call_args))
                .collect::<Option<SmallVec<[ValueId; 8]>>>()
            else {
                return false;
            };
            if original_callee == new_callee && call_args.as_slice() == args.as_slice() {
                return false;
            }

            let has_call = caller
                .inst_set()
                .has_call()
                .expect("target ISA must support `call`");
            let new_call = control_flow::Call::new(has_call, new_callee, args);
            caller.dfg.replace_inst(call_inst_id, Box::new(new_call));
            stats.calls_rewritten += 1;
            true
        }
        InlinePlan::SpliceSingleBlock(splice_plan) => apply_splice_single_block(
            caller,
            call_inst_id,
            &call_args,
            call_res,
            splice_plan,
            stats,
        ),
        InlinePlan::SpliceSingleBlockTerminator(splice_plan) => {
            apply_splice_single_block_terminator(
                caller,
                call_inst_id,
                &call_args,
                call_res,
                splice_plan,
                stats,
            )
        }
    }
}

fn apply_splice_single_block(
    caller: &mut Function,
    call_inst_id: InstId,
    call_args: &[ValueId],
    call_res: Option<ValueId>,
    splice_plan: SplicePlan,
    stats: &mut InlineStats,
) -> bool {
    if call_res.is_some() && splice_plan.ret_value.is_none() {
        return false;
    }

    let Some(mut value_map) = build_splice_value_map(
        &splice_plan.callee_args,
        &splice_plan.const_values,
        caller,
        call_args,
    ) else {
        return false;
    };

    if !validate_splice_value_flow(&splice_plan.body, splice_plan.ret_value, None, &value_map) {
        return false;
    }

    apply_splice_body(splice_plan.body, &mut value_map, |new_inst, result_ty| {
        let new_inst_id = caller.dfg.make_inst_dyn(new_inst);
        caller.layout.insert_inst_before(new_inst_id, call_inst_id);
        result_ty.map(|ty| {
            let new_res = caller.dfg.make_value(Value::Inst {
                inst: new_inst_id,
                ty,
            });
            caller.dfg.attach_result(new_inst_id, new_res);
            new_res
        })
    });

    if let Some((old_ret, call_res)) = splice_plan.ret_value.zip(call_res) {
        let new_ret = *value_map
            .get(&old_ret)
            .expect("validated splice return value must be mapped");
        debug_assert_alias_type_match(caller, call_res, new_ret);
        caller.dfg.change_to_alias(call_res, new_ret);
    }

    caller.dfg.untrack_inst(call_inst_id);
    caller.layout.remove_inst(call_inst_id);
    stats.calls_spliced += 1;
    true
}

fn apply_splice_single_block_terminator(
    caller: &mut Function,
    call_inst_id: InstId,
    call_args: &[ValueId],
    call_res: Option<ValueId>,
    splice_plan: TerminatorSplicePlan,
    stats: &mut InlineStats,
) -> bool {
    if call_res.is_some() {
        return false;
    }

    let call_block = caller.layout.inst_block(call_inst_id);
    let Some(caller_term_inst) = caller.layout.last_inst_of(call_block) else {
        return false;
    };

    // Can't fix up successor phis. Only inline a terminating callee
    // into a caller block that already has no successors.
    if caller.dfg.is_branch(caller_term_inst) {
        return false;
    }

    let Some(mut value_map) = build_splice_value_map(
        &splice_plan.callee_args,
        &splice_plan.const_values,
        caller,
        call_args,
    ) else {
        return false;
    };

    if !validate_splice_value_flow(
        &splice_plan.body,
        None,
        Some(splice_plan.terminator.as_ref()),
        &value_map,
    ) {
        return false;
    }

    let mut editor = CfgEditor::new(caller, CleanupMode::Strict);
    let call_block = editor.truncate_block_from_inst(call_inst_id);
    apply_splice_body(splice_plan.body, &mut value_map, |new_inst, result_ty| {
        let (_, new_result) = editor.append_inst_with_result(call_block, new_inst, result_ty);
        new_result
    });

    let mut new_term = splice_plan.terminator;
    rewrite_inst_values_checked(new_term.as_mut(), &value_map);
    editor.append_inst_with_result(call_block, new_term, None);
    editor.recompute_cfg();

    stats.calls_spliced += 1;
    true
}

fn build_splice_value_map(
    callee_args: &[ValueId],
    const_values: &BTreeMap<ValueId, ValueTemplate>,
    caller: &mut Function,
    call_args: &[ValueId],
) -> Option<FxHashMap<ValueId, ValueId>> {
    if callee_args.len() != call_args.len() {
        return None;
    }

    let mut value_map: FxHashMap<ValueId, ValueId> = FxHashMap::default();
    value_map.extend(callee_args.iter().copied().zip(call_args.iter().copied()));
    for (old_value, tpl) in const_values {
        let new_value = materialize(tpl, caller, call_args)?;
        value_map.insert(*old_value, new_value);
    }

    Some(value_map)
}

fn apply_splice_body(
    body: Vec<TemplateInst>,
    value_map: &mut FxHashMap<ValueId, ValueId>,
    mut insert: impl FnMut(Box<dyn Inst>, Option<Type>) -> Option<ValueId>,
) {
    for template_inst in body {
        let mut new_inst = template_inst.inst;
        rewrite_inst_values_checked(new_inst.as_mut(), value_map);
        let inserted_result = insert(new_inst, template_inst.old_result.map(|(_, ty)| ty));

        if let Some((old_res, _)) = template_inst.old_result {
            let new_res =
                inserted_result.expect("instruction result type provided when old result exists");
            value_map.insert(old_res, new_res);
        }
    }
}

fn validate_splice_value_flow(
    body: &[TemplateInst],
    required_value: Option<ValueId>,
    trailing_inst: Option<&dyn Inst>,
    initial_map: &FxHashMap<ValueId, ValueId>,
) -> bool {
    let mut available: FxHashSet<ValueId> = initial_map.keys().copied().collect();
    for template_inst in body {
        if !inst_values_available(template_inst.inst.as_ref(), &available) {
            return false;
        }
        if let Some((old_res, _)) = template_inst.old_result {
            available.insert(old_res);
        }
    }

    if let Some(required_value) = required_value
        && !available.contains(&required_value)
    {
        return false;
    }

    if let Some(trailing_inst) = trailing_inst
        && !inst_values_available(trailing_inst, &available)
    {
        return false;
    }

    true
}

fn inst_values_available(inst: &dyn Inst, available: &FxHashSet<ValueId>) -> bool {
    let mut all_available = true;
    inst.for_each_value(&mut |value| {
        if !available.contains(&value) {
            all_available = false;
        }
    });
    all_available
}

fn rewrite_inst_values_checked(inst: &mut dyn Inst, value_map: &FxHashMap<ValueId, ValueId>) {
    assert!(
        rewrite_inst_values(inst, value_map),
        "validated splice instruction had unmapped operand"
    );
}

fn materialize(
    template: &ValueTemplate,
    caller: &mut Function,
    call_args: &[ValueId],
) -> Option<ValueId> {
    match template {
        ValueTemplate::Arg(i) => call_args.get(*i).copied(),
        ValueTemplate::Imm(imm) => Some(caller.dfg.make_imm_value(*imm)),
        ValueTemplate::Global(gv) => Some(caller.dfg.make_global_value(*gv)),
        ValueTemplate::Undef(ty) => Some(caller.dfg.make_undef_value(*ty)),
    }
}

fn classify_value_template(func: &Function, value: ValueId) -> Option<ValueTemplate> {
    match func.dfg.value(value) {
        Value::Arg { idx, .. } => Some(ValueTemplate::Arg(*idx)),
        Value::Immediate { imm, .. } => Some(ValueTemplate::Imm(*imm)),
        Value::Global { gv, .. } => Some(ValueTemplate::Global(*gv)),
        Value::Undef { ty } => Some(ValueTemplate::Undef(*ty)),
        Value::Inst { .. } => None,
    }
}

fn signatures_match(ctx: &ModuleCtx, a: FuncRef, b: FuncRef) -> bool {
    ctx.func_sig(a, |a_sig| {
        ctx.func_sig(b, |b_sig| {
            a_sig.args() == b_sig.args() && a_sig.ret_ty() == b_sig.ret_ty()
        })
    })
}

fn extend_const_values_from_inst_operands(
    func: &Function,
    inst_id: InstId,
    const_values: &mut BTreeMap<ValueId, ValueTemplate>,
) {
    func.dfg.inst(inst_id).for_each_value(&mut |value| {
        if let Some(tpl) = classify_value_template(func, value) {
            record_const_value(const_values, value, tpl);
        }
    });
}

fn record_const_value(
    const_values: &mut BTreeMap<ValueId, ValueTemplate>,
    value_id: ValueId,
    template: ValueTemplate,
) {
    if matches!(
        template,
        ValueTemplate::Imm(..) | ValueTemplate::Global(..) | ValueTemplate::Undef(..)
    ) {
        const_values.entry(value_id).or_insert(template);
    }
}

fn debug_assert_alias_type_match(func: &Function, value: ValueId, alias: ValueId) {
    debug_assert_eq!(
        func.dfg.value_ty(value),
        func.dfg.value_ty(alias),
        "alias type mismatch: {value:?} and {alias:?}"
    );
}

fn rewrite_inst_values(inst: &mut dyn Inst, value_map: &FxHashMap<ValueId, ValueId>) -> bool {
    let mut all_mapped = true;
    inst.for_each_value_mut(&mut |value| {
        if let Some(&mapped) = value_map.get(value) {
            *value = mapped;
        } else {
            all_mapped = false;
        }
    });
    all_mapped
}
