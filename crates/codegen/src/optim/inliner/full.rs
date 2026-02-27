use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Inst, InstId, Module, Value, ValueId, module::FuncRef,
    visitor::Visitor,
};

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

#[derive(Debug, Clone, Copy)]
struct ReturnSite {
    from_block: BlockId,
    value: Option<ValueId>,
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
    let call_res = caller.dfg.inst_result(call_inst);

    if callee.arg_values.len() != call_args.len() {
        return Err(FullInlineFail::SignatureMismatch);
    }

    let sig_mismatch = module.ctx.func_sig(callee_ref, |sig| {
        if sig.args().len() != call_args.len() {
            return true;
        }

        if sig.ret_ty().is_unit() {
            call_res.is_some()
        } else {
            let Some(call_res) = call_res else {
                return true;
            };
            sig.ret_ty() != caller.dfg.value_ty(call_res)
        }
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
    validate_full_inline_callee_rewriteability(callee, &rpo, &reachable)?;

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
            let old_result = callee.dfg.inst_result(old_inst);
            let result_ty = old_result.map(|value| callee.dfg.value_ty(value));

            let mut cloned: Box<dyn Inst> = callee.dfg.clone_inst(old_inst);
            let is_phi = callee.dfg.is_phi(old_inst);

            let fixups = {
                let rewriter =
                    OperandRewriter::new(callee, editor.func_mut(), &mut value_map, &block_map);
                rewriter
                    .rewrite_inst_operands(cloned.as_mut(), is_phi)
                    .expect("validated callee should be rewriteable")
            };

            let (new_inst, new_result) =
                editor.append_inst_with_result(new_block, cloned, result_ty);
            inserted_insts += 1;

            if let Some(old_result) = old_result
                && let Some(new_result) = new_result
            {
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
            let ret_value = callee
                .dfg
                .return_args(term_id)
                .and_then(|args| args.first().copied())
                .and_then(|value| map_or_materialize(callee, editor.func_mut(), &mut value_map, value));

            let jump = editor.func_mut().dfg.make_jump(cont_block);
            editor.append_inst_with_result(new_block, Box::new(jump), None);
            inserted_insts += 1;

            returns.push(ReturnSite {
                from_block: new_block,
                value: ret_value,
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
        let mapped = if let Some(&mapped) = value_map.get(&fixup.old_value) {
            mapped
        } else {
            let ty = callee.dfg.value_ty(fixup.old_value);
            editor.func_mut().dfg.make_undef_value(ty)
        };

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
        func.dfg.rewrite_branch_dest(term, cont_block, entry_new);
    }

    if let Some(call_res) = call_res {
        let func = editor.func_mut();
        let call_res_ty = func.dfg.value_ty(call_res);

        match returns.len() {
            0 => {
                let undef = func.dfg.make_undef_value(call_res_ty);
                func.dfg.change_to_alias(call_res, undef);
            }
            1 => {
                let value = match returns[0].value {
                    Some(value) if func.dfg.value_ty(value) == call_res_ty => value,
                    _ => func.dfg.make_undef_value(call_res_ty),
                };
                func.dfg.change_to_alias(call_res, value);
            }
            _ => {
                let mut args = Vec::with_capacity(returns.len());
                for return_site in &returns {
                    let value = match return_site.value {
                        Some(value) if func.dfg.value_ty(value) == call_res_ty => value,
                        _ => func.dfg.make_undef_value(call_res_ty),
                    };
                    args.push((value, return_site.from_block));
                }

                let phi = func.dfg.make_phi(args);
                let phi_inst = func.dfg.make_inst(phi);
                func.layout.prepend_inst(phi_inst, cont_block);

                let phi_value = func.dfg.make_value(Value::Inst {
                    inst: phi_inst,
                    result_idx: 0,
                    ty: call_res_ty,
                });
                func.dfg.attach_result(phi_inst, phi_value);
                func.dfg.change_to_alias(call_res, phi_value);
                inserted_insts += 1;
            }
        }
    }

    if editor.func().layout.is_inst_inserted(call_inst) {
        let func = editor.func_mut();
        func.dfg.untrack_inst(call_inst);
        func.layout.remove_inst(call_inst);
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
    callee: &Function,
    rpo: &[BlockId],
    reachable: &FxHashSet<BlockId>,
) -> Result<(), FullInlineFail> {
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

            if let Some(res) = callee.dfg.inst_result(inst_id) {
                seen_values.insert(res);
            }
        }

        if !callee.dfg.is_return(term_id) {
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
