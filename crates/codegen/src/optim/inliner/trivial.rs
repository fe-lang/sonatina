//! Trivial inliner (single-block, no multi-block CFG cloning).

use std::collections::BTreeMap;

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    Function, GlobalVariableRef, Immediate, Inst, InstDowncast, InstId, Module, Type, Value,
    ValueId,
    inst::{SideEffect, control_flow},
    module::FuncRef,
};

use crate::{
    cfg_edit::{CfgEditor, CleanupMode},
    optim::call_purity::is_removable_pure_call,
};

use super::{InlineStats, InlinerConfig};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueTemplate {
    Arg(usize),
    Imm(Immediate),
    Global(GlobalVariableRef),
    Undef(Type),
}

type ReturnedTemplates = SmallVec<[ValueTemplate; 2]>;
type ReturnedValues = SmallVec<[ValueId; 2]>;
type InstResultTemplates = SmallVec<[(ValueId, Type); 2]>;

#[allow(private_interfaces)]
pub(super) enum InlinePlan {
    /// Delete the call; optionally alias its result to a materialized value.
    RemoveCall { returned: ReturnedTemplates },
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
    old_results: InstResultTemplates,
}

#[derive(Clone)]
struct TemplateInstSummary {
    inst_id: InstId,
    old_results: InstResultTemplates,
}

struct SplicePlan {
    callee_args: Vec<ValueId>,
    const_values: BTreeMap<ValueId, ValueTemplate>,
    body: Vec<TemplateInst>,
    ret_values: ReturnedValues,
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
    ret_values: ReturnedValues,
}

#[derive(Clone)]
struct TerminatorSplicePlanSummary {
    callee_args: Vec<ValueId>,
    const_values: BTreeMap<ValueId, ValueTemplate>,
    body: Vec<TemplateInstSummary>,
    term_inst_id: InstId,
}

#[derive(Clone)]
#[allow(private_interfaces)]
pub(super) enum InlinePlanSummary {
    RemoveCall {
        returned: ReturnedTemplates,
    },
    RewriteCall {
        new_callee: FuncRef,
        new_args: Vec<ValueTemplate>,
    },
    SpliceSingleBlock(SplicePlanSummary),
    SpliceSingleBlockTerminator(TerminatorSplicePlanSummary),
}

pub(super) fn summary_changes_cfg(summary: &InlinePlanSummary) -> bool {
    matches!(summary, InlinePlanSummary::SpliceSingleBlockTerminator(_))
}

struct CollectedSpliceBody {
    const_values: BTreeMap<ValueId, ValueTemplate>,
    body: Vec<TemplateInstSummary>,
}

pub(super) fn analyze_callee(
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
    let ret_values: ReturnedValues = ret_inst.args().iter().copied().collect();

    // Pattern A/B/C: single return-only block.
    if insts.len() == 1 {
        if ret_values.is_empty() {
            if config.enable_noop {
                return Some(InlinePlanSummary::RemoveCall {
                    returned: SmallVec::new(),
                });
            }
            return None;
        }

        if !config.enable_return_alias {
            return None;
        }

        let returned = ret_values
            .iter()
            .map(|&ret_value| classify_value_template(callee, ret_value))
            .collect::<Option<ReturnedTemplates>>()?;
        return Some(InlinePlanSummary::RemoveCall { returned });
    }

    // Pattern D: wrapper forwarding (call; return).
    if insts.len() == 2 && config.enable_wrapper_rewrite {
        let call_inst_id = insts[0];
        let Some(call_inst) =
            <&control_flow::Call as InstDowncast>::downcast(is, callee.dfg.inst(call_inst_id))
        else {
            // Not a wrapper; fall through to splicing.
            return analyze_splice(
                callee,
                callee_call_count,
                config,
                stats,
                &ret_values,
                &insts,
            );
        };

        if callee.dfg.inst_results(call_inst_id) != ret_values.as_slice() {
            return None;
        }

        if !wrapper_call_signatures_compatible(module, callee, callee_ref, call_inst) {
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

    analyze_splice(
        callee,
        callee_call_count,
        config,
        stats,
        &ret_values,
        &insts,
    )
}

fn analyze_splice(
    callee: &Function,
    callee_call_count: usize,
    config: &InlinerConfig,
    stats: &mut InlineStats,
    ret_values: &[ValueId],
    insts: &[InstId],
) -> Option<InlinePlanSummary> {
    if !config.enable_single_block_splice {
        return None;
    }

    let (_, body_insts) = insts.split_last()?;
    let mut collected = collect_splice_body(callee, callee_call_count, config, stats, body_insts)?;

    for &ret_value in ret_values {
        if let Some(tpl) = classify_value_template(callee, ret_value) {
            record_const_value(&mut collected.const_values, ret_value, tpl);
        }
    }

    let callee_args: Vec<ValueId> = callee.arg_values.iter().copied().collect();
    let plan = SplicePlanSummary {
        callee_args,
        const_values: collected.const_values,
        body: collected.body,
        ret_values: ret_values.iter().copied().collect(),
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
    for &inst_id in body_insts {
        if callee.dfg.is_phi(inst_id)
            || callee.dfg.is_branch(inst_id)
            || callee.dfg.is_terminator(inst_id)
        {
            stats.skipped_non_straight_line += 1;
            stats.skipped_effectful += 1;
            return None;
        }

        if config.splice_require_pure && !is_pure_splice_inst(callee, inst_id) {
            stats.skipped_not_pure += 1;
            stats.skipped_effectful += 1;
            return None;
        }
        extend_const_values_from_inst_operands(callee, inst_id, &mut const_values);
        let old_results = callee
            .dfg
            .inst_results(inst_id)
            .iter()
            .map(|&res| (res, callee.dfg.value_ty(res)))
            .collect();
        body.push(TemplateInstSummary {
            inst_id,
            old_results,
        });
    }

    Some(CollectedSpliceBody { const_values, body })
}

fn is_pure_splice_inst(callee: &Function, inst_id: InstId) -> bool {
    if callee.dfg.call_info(inst_id).is_some() {
        return is_removable_pure_call(callee, inst_id);
    }

    callee.dfg.side_effect(inst_id) == SideEffect::None
}

pub(super) fn materialize_plan(callee: &Function, summary: &InlinePlanSummary) -> InlinePlan {
    match summary {
        InlinePlanSummary::RemoveCall { returned } => InlinePlan::RemoveCall {
            returned: returned.clone(),
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
                ret_values: summary.ret_values.clone(),
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
            old_results: summary.old_results.clone(),
        })
        .collect()
}

pub(super) fn apply_plan(
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
    let call_results: ReturnedValues = caller
        .dfg
        .inst_results(call_inst_id)
        .iter()
        .copied()
        .collect();

    match plan {
        InlinePlan::RemoveCall { returned } => {
            if call_results.len() != returned.len() {
                return false;
            }

            for (&call_res, tpl) in call_results.iter().zip(returned.iter()) {
                let Some(alias) = materialize(tpl, caller, &call_args) else {
                    return false;
                };
                debug_assert_alias_type_match(caller, call_res, alias);
                caller.dfg.change_to_alias(call_res, alias);
            }

            caller.layout.remove_inst(call_inst_id);
            caller.erase_inst(call_inst_id);
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
            &call_results,
            splice_plan,
            stats,
        ),
        InlinePlan::SpliceSingleBlockTerminator(splice_plan) => {
            apply_splice_single_block_terminator(
                caller,
                call_inst_id,
                &call_args,
                &call_results,
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
    call_results: &[ValueId],
    splice_plan: SplicePlan,
    stats: &mut InlineStats,
) -> bool {
    if call_results.len() != splice_plan.ret_values.len() {
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

    if !validate_splice_value_flow(&splice_plan.body, &splice_plan.ret_values, None, &value_map) {
        return false;
    }

    apply_splice_body(splice_plan.body, &mut value_map, |new_inst, result_tys| {
        let new_inst_id = caller.dfg.make_inst_dyn(new_inst);
        caller.layout.insert_inst_before(new_inst_id, call_inst_id);
        let new_results: SmallVec<[ValueId; 2]> = result_tys
            .iter()
            .enumerate()
            .map(|(result_idx, ty)| {
                caller.dfg.make_value(Value::Inst {
                    inst: new_inst_id,
                    result_idx: result_idx.try_into().expect("too many instruction results"),
                    ty: *ty,
                })
            })
            .collect();
        caller
            .dfg
            .attach_results(new_inst_id, new_results.as_slice());
        new_results
    });

    for (&old_ret, &call_res) in splice_plan.ret_values.iter().zip(call_results.iter()) {
        let new_ret = *value_map
            .get(&old_ret)
            .expect("validated splice return value must be mapped");
        debug_assert_alias_type_match(caller, call_res, new_ret);
        caller.dfg.change_to_alias(call_res, new_ret);
    }

    caller.layout.remove_inst(call_inst_id);
    caller.erase_inst(call_inst_id);
    stats.calls_spliced += 1;
    true
}

fn apply_splice_single_block_terminator(
    caller: &mut Function,
    call_inst_id: InstId,
    call_args: &[ValueId],
    call_results: &[ValueId],
    splice_plan: TerminatorSplicePlan,
    stats: &mut InlineStats,
) -> bool {
    if !call_results.is_empty() {
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
        &[],
        Some(splice_plan.terminator.as_ref()),
        &value_map,
    ) {
        return false;
    }

    let mut editor = CfgEditor::new(caller, CleanupMode::Strict);
    let call_block = editor.truncate_block_from_inst(call_inst_id);
    apply_splice_body(splice_plan.body, &mut value_map, |new_inst, result_tys| {
        let (_, new_results) = editor.append_inst_with_results(call_block, new_inst, result_tys);
        new_results
    });

    let mut new_term = splice_plan.terminator;
    rewrite_inst_values_checked(new_term.as_mut(), &value_map);
    editor.append_inst_with_results(call_block, new_term, &[]);
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
    mut insert: impl FnMut(Box<dyn Inst>, &[Type]) -> SmallVec<[ValueId; 2]>,
) {
    for template_inst in body {
        let mut new_inst = template_inst.inst;
        rewrite_inst_values_checked(new_inst.as_mut(), value_map);
        let result_tys: SmallVec<[Type; 2]> = template_inst
            .old_results
            .iter()
            .map(|(_, ty)| *ty)
            .collect();
        let inserted_results = insert(new_inst, result_tys.as_slice());
        assert_eq!(
            inserted_results.len(),
            template_inst.old_results.len(),
            "inserted result count did not match template result count"
        );

        for ((old_res, _), new_res) in template_inst
            .old_results
            .into_iter()
            .zip(inserted_results.into_iter())
        {
            value_map.insert(old_res, new_res);
        }
    }
}

fn validate_splice_value_flow(
    body: &[TemplateInst],
    required_values: &[ValueId],
    trailing_inst: Option<&dyn Inst>,
    initial_map: &FxHashMap<ValueId, ValueId>,
) -> bool {
    let mut available: FxHashSet<ValueId> = initial_map.keys().copied().collect();
    for template_inst in body {
        if !inst_values_available(template_inst.inst.as_ref(), &available) {
            return false;
        }
        for (old_res, _) in &template_inst.old_results {
            available.insert(*old_res);
        }
    }

    for &required_value in required_values {
        if !available.contains(&required_value) {
            return false;
        }
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

fn wrapper_call_signatures_compatible(
    module: &Module,
    wrapper: &Function,
    wrapper_ref: FuncRef,
    inner_call: &control_flow::Call,
) -> bool {
    let forwarded_args_match = module.ctx.func_sig(*inner_call.callee(), |inner_sig| {
        inner_sig.args().len() == inner_call.args().len()
            && inner_sig
                .args()
                .iter()
                .copied()
                .zip(inner_call.args().iter().copied())
                .all(|(expected_ty, arg)| wrapper.dfg.value_ty(arg) == expected_ty)
    });
    if !forwarded_args_match {
        return false;
    }

    module.ctx.func_sig(wrapper_ref, |wrapper_sig| {
        module.ctx.func_sig(*inner_call.callee(), |inner_sig| {
            wrapper_sig.ret_tys() == inner_sig.ret_tys()
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
