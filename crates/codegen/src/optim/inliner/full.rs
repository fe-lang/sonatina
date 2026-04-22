use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Inst, InstId, Module, Type, Value, ValueId,
    module::FuncRef, visitor::Visitor,
};
use sonatina_verifier::{VerifierConfig, verify_function};

use crate::cfg_edit::{CfgEditor, CleanupMode};

use super::{InlinerConfig, rewrite::OperandRewriter};

#[derive(Debug, Clone, Copy)]
pub(super) enum FullInlineFail {
    CallGone,
    NotCall,
    CalleeMismatch,
    NoBody,
    SignatureMismatch,
    MalformedCallee,
}

#[derive(Debug, Clone, Copy)]
pub(super) struct FullInlineResult {
    pub blocks_cloned: usize,
    pub insts_cloned: usize,
    pub phi_fixups: usize,
    pub net_growth: usize,
    pub cont_block: BlockId,
    pub cont_reachable: bool,
}

#[derive(Debug, Clone)]
struct ReturnSite {
    from_block: BlockId,
    values: SmallVec<[ValueId; 2]>,
}

#[derive(Debug, Clone, Copy)]
struct PhiFixupRecord {
    phi_inst: InstId,
    arg_index: usize,
    old_value: ValueId,
}

pub(super) fn try_inline_callsite_full(
    module: &Module,
    _caller_ref: FuncRef,
    caller: &mut Function,
    call_inst: InstId,
    callee_ref: FuncRef,
    callee: &Function,
    _config: &InlinerConfig,
) -> Result<FullInlineResult, FullInlineFail> {
    if !caller.layout.is_inst_inserted(call_inst) {
        return Err(FullInlineFail::CallGone);
    }

    let Some(call) = caller.dfg.cast_call(call_inst) else {
        return Err(FullInlineFail::NotCall);
    };
    if *call.callee() != callee_ref {
        return Err(FullInlineFail::CalleeMismatch);
    }

    if !module.ctx.func_linkage(callee_ref).has_definition() {
        return Err(FullInlineFail::NoBody);
    }

    let call_args = call.args().clone();
    let call_results: SmallVec<[ValueId; 2]> =
        caller.dfg.inst_results(call_inst).iter().copied().collect();

    if callee.arg_values.len() != call_args.len() {
        return Err(FullInlineFail::SignatureMismatch);
    }

    let sig_mismatch =
        module.ctx.func_sig(callee_ref, |sig| {
            if sig.args().len() != call_args.len() {
                return true;
            }
            if sig
                .args()
                .iter()
                .zip(call_args.iter())
                .any(|(expected_ty, &arg)| caller.dfg.value_ty(arg) != *expected_ty)
            {
                return true;
            }

            sig.ret_tys().len() != call_results.len()
                || sig.ret_tys().iter().zip(call_results.iter()).any(
                    |(expected_ty, &call_result)| caller.dfg.value_ty(call_result) != *expected_ty,
                )
        });
    if sig_mismatch {
        return Err(FullInlineFail::SignatureMismatch);
    }

    let Some(callee_entry) = callee.layout.entry_block() else {
        return Err(FullInlineFail::MalformedCallee);
    };

    let mut callee_cfg = ControlFlowGraph::default();
    callee_cfg.compute(callee);
    let mut rpo: Vec<BlockId> = callee_cfg.post_order().collect();
    rpo.reverse();
    if rpo.is_empty() {
        return Err(FullInlineFail::MalformedCallee);
    }

    let reachable: FxHashSet<BlockId> = rpo.iter().copied().collect();
    validate_full_inline_callee_rewriteability(module, callee_ref, callee, &rpo, &reachable)?;

    let mut editor = CfgEditor::new(caller, CleanupMode::Strict);
    let (callsite_block, cont_block) = editor.split_block_at(call_inst);

    let mut block_map: FxHashMap<BlockId, BlockId> = FxHashMap::default();
    let mut insert_after = callsite_block;
    for block in callee.layout.iter_block() {
        if !reachable.contains(&block) {
            continue;
        }

        let new_block = editor.func_mut().dfg.make_block();
        editor
            .func_mut()
            .layout
            .insert_block_after(new_block, insert_after);
        insert_after = new_block;
        block_map.insert(block, new_block);
    }

    let entry_new = *block_map
        .get(&callee_entry)
        .expect("validated callee entry should be mapped");

    let mut value_map: FxHashMap<ValueId, ValueId> = FxHashMap::default();
    for (old_arg, new_arg) in callee
        .arg_values
        .iter()
        .copied()
        .zip(call_args.iter().copied())
    {
        value_map.insert(old_arg, new_arg);
    }

    let mut phi_fixups = Vec::new();
    let mut returns = Vec::new();
    let mut inserted_insts = 0usize;

    for old_block in rpo {
        let new_block = block_map[&old_block];
        let inst_ids: Vec<InstId> = callee.layout.iter_inst(old_block).collect();
        if inst_ids.is_empty() {
            continue;
        }

        let term_id = *inst_ids.last().expect("block has at least one inst");
        let body = &inst_ids[..inst_ids.len() - 1];

        for &old_inst in body {
            let old_results = callee.dfg.inst_results(old_inst);
            let result_tys: SmallVec<[Type; 2]> = old_results
                .iter()
                .map(|&value| callee.dfg.value_ty(value))
                .collect();

            let mut cloned: Box<dyn Inst> = callee.dfg.clone_inst(old_inst);
            let is_phi = callee.dfg.is_phi(old_inst);

            let fixups = {
                let rewriter =
                    OperandRewriter::new(callee, editor.func_mut(), &mut value_map, &block_map);
                rewriter
                    .rewrite_inst_operands(cloned.as_mut(), is_phi)
                    .expect("validated callee should be rewriteable")
            };

            let (new_inst, new_results) =
                editor.append_inst_with_results(new_block, cloned, result_tys.as_slice());
            inserted_insts += 1;

            assert_eq!(
                old_results.len(),
                new_results.len(),
                "cloned instruction results should match source instruction results"
            );
            for (&old_result, &new_result) in old_results.iter().zip(new_results.iter()) {
                value_map.insert(old_result, new_result);
            }

            if is_phi {
                for fixup in fixups {
                    phi_fixups.push(PhiFixupRecord {
                        phi_inst: new_inst,
                        arg_index: fixup.arg_index,
                        old_value: fixup.old_value,
                    });
                }
            }
        }

        if callee.dfg.is_return(term_id) {
            let ret_values = callee
                .dfg
                .return_args(term_id)
                .map(|args| {
                    args.iter()
                        .map(|&value| {
                            map_or_materialize(callee, editor.func_mut(), &mut value_map, value)
                                .expect("verified return value should rewrite")
                        })
                        .collect()
                })
                .unwrap_or_default();

            let jump = editor.func_mut().dfg.make_jump(cont_block);
            editor.append_inst_with_result(new_block, Box::new(jump), None);
            inserted_insts += 1;

            returns.push(ReturnSite {
                from_block: new_block,
                values: ret_values,
            });
        } else {
            let mut term = callee.dfg.clone_inst(term_id);
            {
                let rewriter =
                    OperandRewriter::new(callee, editor.func_mut(), &mut value_map, &block_map);
                rewriter
                    .rewrite_inst_operands(term.as_mut(), false)
                    .expect("validated callee should be rewriteable");
            }
            editor.append_inst_with_result(new_block, term, None);
            inserted_insts += 1;
        }
    }

    for fixup in &phi_fixups {
        let mapped = *value_map
            .get(&fixup.old_value)
            .expect("verified phi fixup should resolve");

        let func = editor.func_mut();
        func.dfg.untrack_inst(fixup.phi_inst);
        if let Some(phi) = func.dfg.cast_phi_mut(fixup.phi_inst)
            && fixup.arg_index < phi.args().len()
        {
            phi.args_mut()[fixup.arg_index].0 = mapped;
        }
        func.dfg.attach_user(fixup.phi_inst);
    }

    {
        let func = editor.func_mut();
        let term = func
            .layout
            .last_inst_of(callsite_block)
            .expect("split_block_at inserts a terminator in the callsite block");
        func.dfg
            .rewrite_branch_edges_to_block(term, cont_block, entry_new);
    }

    if !call_results.is_empty() {
        let func = editor.func_mut();

        for (result_idx, &call_result) in call_results.iter().enumerate() {
            let call_result_ty = func.dfg.value_ty(call_result);

            match returns.len() {
                0 => {
                    let undef = func.dfg.make_undef_value(call_result_ty);
                    func.dfg.change_to_alias(call_result, undef);
                }
                1 => {
                    let value = returns[0]
                        .values
                        .get(result_idx)
                        .copied()
                        .filter(|&value| func.dfg.value_ty(value) == call_result_ty)
                        .unwrap_or_else(|| func.dfg.make_undef_value(call_result_ty));
                    func.dfg.change_to_alias(call_result, value);
                }
                _ => {
                    let mut args = Vec::with_capacity(returns.len());
                    for return_site in &returns {
                        let value = return_site
                            .values
                            .get(result_idx)
                            .copied()
                            .filter(|&value| func.dfg.value_ty(value) == call_result_ty)
                            .unwrap_or_else(|| func.dfg.make_undef_value(call_result_ty));
                        args.push((value, return_site.from_block));
                    }

                    let phi = func.dfg.make_phi(args);
                    let phi_inst = func.dfg.make_inst(phi);
                    func.layout.prepend_inst(phi_inst, cont_block);

                    let phi_value = func.dfg.make_value(Value::Inst {
                        inst: phi_inst,
                        result_idx: 0,
                        ty: call_result_ty,
                    });
                    func.dfg.attach_result(phi_inst, phi_value);
                    func.dfg.change_to_alias(call_result, phi_value);
                    inserted_insts += 1;
                }
            }
        }
    }

    if editor.func().layout.is_inst_inserted(call_inst) {
        let func = editor.func_mut();
        func.layout.remove_inst(call_inst);
        func.erase_inst(call_inst);
    }

    editor.recompute_cfg();
    let cont_reachable = !returns.is_empty();

    Ok(FullInlineResult {
        blocks_cloned: block_map.len(),
        insts_cloned: inserted_insts,
        phi_fixups: phi_fixups.len(),
        net_growth: inserted_insts.saturating_sub(1),
        cont_block,
        cont_reachable,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValueValidationMode {
    RequireMapped,
    AllowForwardRefsInPhi,
}

struct OperandValidator<'a> {
    callee: &'a Function,
    reachable: &'a FxHashSet<BlockId>,
    arg_values: &'a FxHashSet<ValueId>,
    seen_values: &'a FxHashSet<ValueId>,
    mode: ValueValidationMode,
    ok: bool,
}

impl OperandValidator<'_> {
    fn validate_value(&mut self, value: ValueId) {
        match self.callee.dfg.value(value) {
            Value::Immediate { .. } | Value::Global { .. } | Value::Undef { .. } => {}
            Value::Arg { .. } => {
                if !self.arg_values.contains(&value) {
                    self.ok = false;
                }
            }
            Value::Inst { .. } => match self.mode {
                ValueValidationMode::RequireMapped => {
                    if !self.seen_values.contains(&value) {
                        self.ok = false;
                    }
                }
                ValueValidationMode::AllowForwardRefsInPhi => {}
            },
        }
    }
}

impl Visitor for OperandValidator<'_> {
    fn visit_value_id(&mut self, item: ValueId) {
        self.validate_value(item);
    }

    fn visit_block_id(&mut self, item: BlockId) {
        if !self.reachable.contains(&item) {
            self.ok = false;
        }
    }
}

fn validate_full_inline_callee_rewriteability(
    module: &Module,
    callee_ref: FuncRef,
    callee: &Function,
    rpo: &[BlockId],
    reachable: &FxHashSet<BlockId>,
) -> Result<(), FullInlineFail> {
    if verify_function(
        &module.ctx,
        callee_ref,
        callee,
        &VerifierConfig {
            check_dominance: true,
            ..VerifierConfig::default()
        },
    )
    .has_errors()
    {
        return Err(FullInlineFail::MalformedCallee);
    }

    let layout_blocks: FxHashSet<BlockId> = callee.layout.iter_block().collect();
    let arg_values: FxHashSet<ValueId> = callee.arg_values.iter().copied().collect();
    let mut seen_values: FxHashSet<ValueId> = arg_values.clone();

    for &block in rpo {
        if !layout_blocks.contains(&block) {
            return Err(FullInlineFail::MalformedCallee);
        }

        let inst_ids: Vec<InstId> = callee.layout.iter_inst(block).collect();
        let Some(&term_id) = inst_ids.last() else {
            return Err(FullInlineFail::MalformedCallee);
        };
        if !callee.dfg.is_terminator(term_id) {
            return Err(FullInlineFail::MalformedCallee);
        }

        let body = &inst_ids[..inst_ids.len().saturating_sub(1)];
        for &inst_id in body {
            let inst = callee.dfg.inst(inst_id);
            let is_phi = callee.dfg.is_phi(inst_id);

            let mut v = OperandValidator {
                callee,
                reachable,
                arg_values: &arg_values,
                seen_values: &seen_values,
                mode: if is_phi {
                    ValueValidationMode::AllowForwardRefsInPhi
                } else {
                    ValueValidationMode::RequireMapped
                },
                ok: true,
            };
            inst.accept(&mut v);
            if !v.ok {
                return Err(FullInlineFail::MalformedCallee);
            }

            for &result in callee.dfg.inst_results(inst_id) {
                seen_values.insert(result);
            }
        }

        let inst = callee.dfg.inst(term_id);
        let mut v = OperandValidator {
            callee,
            reachable,
            arg_values: &arg_values,
            seen_values: &seen_values,
            mode: ValueValidationMode::RequireMapped,
            ok: true,
        };
        inst.accept(&mut v);
        if !v.ok {
            return Err(FullInlineFail::MalformedCallee);
        }
    }

    Ok(())
}

fn map_or_materialize(
    callee: &Function,
    caller: &mut Function,
    value_map: &mut FxHashMap<ValueId, ValueId>,
    old: ValueId,
) -> Option<ValueId> {
    if let Some(&mapped) = value_map.get(&old) {
        return Some(mapped);
    }

    let mapped = match callee.dfg.value(old) {
        Value::Immediate { imm, .. } => caller.dfg.make_imm_value(*imm),
        Value::Global { gv, .. } => caller.dfg.make_global_value(*gv),
        Value::Undef { ty } => caller.dfg.make_undef_value(*ty),
        Value::Arg { .. } | Value::Inst { .. } => return None,
    };

    value_map.insert(old, mapped);
    Some(mapped)
}
