use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{BlockId, Module, module::FuncRef};

use crate::machinst::{
    lower::{LoweredFunction, SectionCodeUnit},
    vcode::{Label, SectionCodeUnitId, VCode, VCodeFixup, VCodeInst},
};

use super::{
    is_plain_inst, is_push_opcode,
    late_block_merge::{
        FixupKey, InstKey, block_insts, inst_estimated_size, inst_key, is_non_fallthrough_terminal,
        layout_fallthrough_targets, replace_block_insts, sequence_summary,
    },
    opcode::OpCode,
    referenced_insn_label_targets,
};

pub(super) fn run_late_section_terminal_outline(
    module: &Module,
    lowered: &mut [(FuncRef, LoweredFunction<OpCode>)],
) -> Vec<SectionCodeUnit<OpCode>> {
    let mut section_units = Vec::new();
    let mut helpers_by_key: FxHashMap<Vec<InstKey>, SectionCodeUnitId> = FxHashMap::default();
    let mut next_helper_id = 0_u32;

    while let Some(candidate) = select_best_group(module, lowered, &helpers_by_key) {
        let helper_id = candidate.helper_id.unwrap_or_else(|| {
            let id = SectionCodeUnitId(next_helper_id);
            next_helper_id = next_helper_id
                .checked_add(1)
                .expect("section helper id overflow");
            let donor = candidate
                .donor
                .as_ref()
                .expect("new helper candidate must include donor");
            section_units.push(build_section_helper(id, donor, lowered));
            helpers_by_key.insert(candidate.key.clone(), id);
            id
        });

        let mut actions = candidate.actions;
        actions.sort_by(|a, b| {
            a.func_idx
                .cmp(&b.func_idx)
                .then_with(|| b.order_idx.cmp(&a.order_idx))
        });

        for action in actions {
            let (_, lowered) = &mut lowered[action.func_idx];
            match action.kind {
                GroupActionKind::Direct => {
                    rewrite_block_labels_to_section_unit(
                        &mut lowered.vcode,
                        action.block,
                        helper_id,
                    );
                    let removed = lowered.block_order.remove(action.order_idx);
                    debug_assert_eq!(removed, action.block);
                }
                GroupActionKind::Unlock(unlock) => {
                    apply_unlock_to_section_helper(
                        &mut lowered.vcode,
                        &mut lowered.block_order,
                        helper_id,
                        unlock,
                    );
                }
            }
        }
    }

    section_units
}

#[derive(Clone)]
struct TerminalOccurrence {
    func_idx: usize,
    block: BlockId,
    order_idx: usize,
    key: Vec<InstKey>,
    semantic_insts: Vec<VCodeInst>,
    block_size: usize,
    helper_size: usize,
}

#[derive(Clone)]
struct HelperDonor {
    func_idx: usize,
    semantic_insts: Vec<VCodeInst>,
}

#[derive(Clone)]
struct GroupCandidate {
    key: Vec<InstKey>,
    helper_id: Option<SectionCodeUnitId>,
    donor: Option<HelperDonor>,
    actions: Vec<GroupAction>,
    total_savings: isize,
}

#[derive(Clone)]
struct GroupAction {
    func_idx: usize,
    block: BlockId,
    order_idx: usize,
    kind: GroupActionKind,
}

#[derive(Clone)]
enum GroupActionKind {
    Direct,
    Unlock(SectionUnlock),
}

#[derive(Clone, Copy)]
struct SectionUnlock {
    pred: BlockId,
    fallthrough: BlockId,
    other_succ: BlockId,
    push: VCodeInst,
    has_trailing_iszero: bool,
    order_idx: usize,
}

struct FuncSectionAux {
    entry_block: BlockId,
    fallthrough_targets: FxHashSet<BlockId>,
    order_index: FxHashMap<BlockId, usize>,
    label_targets: FxHashSet<VCodeInst>,
}

fn select_best_group(
    module: &Module,
    lowered: &[(FuncRef, LoweredFunction<OpCode>)],
    helpers_by_key: &FxHashMap<Vec<InstKey>, SectionCodeUnitId>,
) -> Option<GroupCandidate> {
    let func_aux = build_func_aux(module, lowered);
    let mut occurrences_by_key: FxHashMap<Vec<InstKey>, Vec<TerminalOccurrence>> =
        FxHashMap::default();

    for (func_idx, (_, lowered)) in lowered.iter().enumerate() {
        for (order_idx, &block) in lowered.block_order.iter().enumerate() {
            let Some(occurrence) =
                analyze_terminal_occurrence(func_idx, &lowered.vcode, block, order_idx)
            else {
                continue;
            };
            occurrences_by_key
                .entry(occurrence.key.clone())
                .or_default()
                .push(occurrence);
        }
    }

    occurrences_by_key
        .into_iter()
        .filter_map(|(key, occurrences)| {
            if occurrences.len() < 2 && !helpers_by_key.contains_key(&key) {
                return None;
            }

            let mut actions = Vec::new();
            let mut gross_savings = 0_isize;
            for occurrence in &occurrences {
                let aux = &func_aux[occurrence.func_idx];
                let action = if occurrence.block != aux.entry_block
                    && !aux.fallthrough_targets.contains(&occurrence.block)
                {
                    gross_savings += occurrence.block_size as isize;
                    Some(GroupAction {
                        func_idx: occurrence.func_idx,
                        block: occurrence.block,
                        order_idx: occurrence.order_idx,
                        kind: GroupActionKind::Direct,
                    })
                } else {
                    analyze_unlock(
                        &lowered[occurrence.func_idx].1.vcode,
                        &lowered[occurrence.func_idx].1.block_order,
                        aux,
                        occurrence.block,
                        occurrence.block_size,
                    )
                    .map(|(unlock, savings)| {
                        gross_savings += savings;
                        GroupAction {
                            func_idx: occurrence.func_idx,
                            block: occurrence.block,
                            order_idx: occurrence.order_idx,
                            kind: GroupActionKind::Unlock(unlock),
                        }
                    })
                };
                if let Some(action) = action {
                    actions.push(action);
                }
            }

            if actions.is_empty() {
                return None;
            }

            let helper_id = helpers_by_key.get(&key).copied();
            let helper_cost = helper_id.map_or(occurrences[0].helper_size as isize, |_| 0);
            let total_savings = gross_savings - helper_cost;
            (total_savings > 0).then_some(GroupCandidate {
                helper_id,
                donor: helper_id.is_none().then(|| HelperDonor {
                    func_idx: occurrences[0].func_idx,
                    semantic_insts: occurrences[0].semantic_insts.clone(),
                }),
                key,
                actions,
                total_savings,
            })
        })
        .max_by(|a, b| a.total_savings.cmp(&b.total_savings))
}

fn build_func_aux(
    module: &Module,
    lowered: &[(FuncRef, LoweredFunction<OpCode>)],
) -> Vec<FuncSectionAux> {
    lowered
        .iter()
        .map(|(func, lowered)| FuncSectionAux {
            entry_block: module
                .func_store
                .view(*func, |function| function.layout.entry_block())
                .expect("lowered function must have entry block"),
            fallthrough_targets: layout_fallthrough_targets(&lowered.vcode, &lowered.block_order),
            order_index: lowered
                .block_order
                .iter()
                .copied()
                .enumerate()
                .map(|(idx, block)| (block, idx))
                .collect(),
            label_targets: referenced_insn_label_targets(&lowered.vcode),
        })
        .collect()
}

fn analyze_terminal_occurrence(
    func_idx: usize,
    vcode: &VCode<OpCode>,
    block: BlockId,
    order_idx: usize,
) -> Option<TerminalOccurrence> {
    let insts = block_insts(vcode, block);
    if insts.is_empty() {
        return None;
    }

    let semantic_start = usize::from((vcode.insts[insts[0]] as u8) == (OpCode::JUMPDEST as u8));
    let semantic_insts = insts.get(semantic_start..)?.to_vec();
    if semantic_insts.is_empty()
        || semantic_insts
            .iter()
            .copied()
            .any(|inst| (vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8))
    {
        return None;
    }

    let &last = semantic_insts.last()?;
    if !is_non_fallthrough_terminal(vcode.insts[last]) {
        return None;
    }

    let mut key = Vec::with_capacity(semantic_insts.len());
    let mut helper_size = 1_usize;
    for &inst in &semantic_insts {
        let key_part = inst_key(vcode, inst)?;
        if matches!(
            key_part.fixup,
            FixupKey::Block(_) | FixupKey::SectionCodeUnit(_)
        ) {
            return None;
        }
        helper_size += inst_estimated_size(vcode, inst);
        key.push(key_part);
    }

    let summary = sequence_summary(vcode, &semantic_insts);
    if summary.min_before != 0 {
        return None;
    }

    Some(TerminalOccurrence {
        func_idx,
        block,
        order_idx,
        key,
        semantic_insts,
        block_size: insts
            .iter()
            .copied()
            .map(|inst| inst_estimated_size(vcode, inst))
            .sum(),
        helper_size,
    })
}

fn analyze_unlock(
    vcode: &VCode<OpCode>,
    block_order: &[BlockId],
    aux: &FuncSectionAux,
    fallthrough: BlockId,
    block_size: usize,
) -> Option<(SectionUnlock, isize)> {
    let order_idx = aux.order_index[&fallthrough];
    if order_idx == 0 || order_idx + 1 >= block_order.len() {
        return None;
    }

    let pred = block_order[order_idx - 1];
    let other_succ = block_order[order_idx + 1];
    let insts = block_insts(vcode, pred);
    if insts.len() < 2 {
        return None;
    }

    let jumpi = *insts.last()?;
    let push = insts[insts.len() - 2];
    if !is_plain_inst(vcode, &aux.label_targets, jumpi)
        || (vcode.insts[jumpi] as u8) != (OpCode::JUMPI as u8)
        || aux.label_targets.contains(&push)
        || !is_push_opcode(vcode.insts[push])
    {
        return None;
    }

    let Some((_, VCodeFixup::Label(label))) = vcode.fixups.get(push) else {
        return None;
    };
    let Label::Block(target) = vcode.labels[*label] else {
        return None;
    };
    if target != other_succ {
        return None;
    }

    let trailing = insts.get(insts.len().saturating_sub(3)).copied();
    let has_trailing_iszero = match trailing {
        Some(inst) if (vcode.insts[inst] as u8) == (OpCode::ISZERO as u8) => {
            if !is_plain_inst(vcode, &aux.label_targets, inst) {
                return None;
            }
            true
        }
        _ => false,
    };

    let savings = block_size as isize + if has_trailing_iszero { 1 } else { -1 };
    (savings > 0).then_some((
        SectionUnlock {
            pred,
            fallthrough,
            other_succ,
            push,
            has_trailing_iszero,
            order_idx,
        },
        savings,
    ))
}

fn build_section_helper(
    id: SectionCodeUnitId,
    donor: &HelperDonor,
    lowered: &[(FuncRef, LoweredFunction<OpCode>)],
) -> SectionCodeUnit<OpCode> {
    let block = BlockId(0);
    let mut vcode = VCode::<OpCode>::default();
    vcode.add_inst_to_block(OpCode::JUMPDEST, None, block);
    let donor_vcode = &lowered[donor.func_idx].1.vcode;
    for &inst in &donor.semantic_insts {
        clone_inst(&mut vcode, donor_vcode, inst, block);
    }

    SectionCodeUnit {
        id,
        name: format!("__evm_shared_tail_{}", id.0),
        vcode,
        block_order: vec![block],
    }
}

fn clone_inst(dst: &mut VCode<OpCode>, src: &VCode<OpCode>, inst: VCodeInst, block: BlockId) {
    let new_inst = dst.add_inst_to_block(src.insts[inst], None, block);
    if let Some((_, bytes)) = src.inst_imm_bytes.get(inst) {
        dst.inst_imm_bytes.insert((new_inst, bytes.clone()));
    }
    if let Some((_, fixup)) = src.fixups.get(inst) {
        let cloned_fixup = match fixup {
            VCodeFixup::Label(label) => {
                let cloned = dst.labels.push(src.labels[*label]);
                VCodeFixup::Label(cloned)
            }
            VCodeFixup::Sym(sym) => VCodeFixup::Sym(sym.clone()),
        };
        dst.fixups.insert((new_inst, cloned_fixup));
    }
}

fn rewrite_block_labels_to_section_unit(
    vcode: &mut VCode<OpCode>,
    block: BlockId,
    helper_id: SectionCodeUnitId,
) {
    for label in vcode.labels.keys().collect::<Vec<_>>() {
        if vcode.labels[label] == Label::Block(block) {
            vcode.labels[label] = Label::SectionCodeUnit(helper_id);
        }
    }
}

fn apply_unlock_to_section_helper(
    vcode: &mut VCode<OpCode>,
    block_order: &mut Vec<BlockId>,
    helper_id: SectionCodeUnitId,
    unlock: SectionUnlock,
) {
    debug_assert_eq!(block_order[unlock.order_idx - 1], unlock.pred);
    debug_assert_eq!(block_order[unlock.order_idx], unlock.fallthrough);
    debug_assert_eq!(block_order[unlock.order_idx + 1], unlock.other_succ);

    let insts = block_insts(vcode, unlock.pred);
    let prefix_len = insts.len() - usize::from(unlock.has_trailing_iszero) - 2;
    let mut rebuilt = insts[..prefix_len].to_vec();
    if !unlock.has_trailing_iszero {
        rebuilt.push(vcode.add_inst_to_block(OpCode::ISZERO, None, unlock.pred));
    }

    let label = vcode.labels.push(Label::SectionCodeUnit(helper_id));
    vcode.fixups.insert((unlock.push, VCodeFixup::Label(label)));
    rebuilt.push(unlock.push);
    rebuilt.push(*insts.last().expect("unlock predecessor missing jumpi"));
    replace_block_insts(vcode, unlock.pred, &rebuilt);

    rewrite_block_labels_to_section_unit(vcode, unlock.fallthrough, helper_id);
    let removed = block_order.remove(unlock.order_idx);
    debug_assert_eq!(removed, unlock.fallthrough);
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_parser::parse_module;

    fn test_module() -> (Module, FxHashMap<String, FuncRef>) {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-osaka"

func public %a() {
block0:
    return;
}

func public %b() {
block0:
    return;
}
"#,
        )
        .unwrap();

        let mut names = FxHashMap::default();
        for func in parsed.module.funcs() {
            let name = parsed
                .module
                .ctx
                .func_sig(func, |sig| sig.name().to_string());
            names.insert(name, func);
        }
        (parsed.module, names)
    }

    fn push_block(vcode: &mut VCode<OpCode>, block: BlockId, dest: BlockId) -> VCodeInst {
        let inst = vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        let label = vcode.labels.push(Label::Block(dest));
        vcode.fixups.insert((inst, VCodeFixup::Label(label)));
        inst
    }

    fn build_revert_block(vcode: &mut VCode<OpCode>, block: BlockId) {
        vcode.add_inst_to_block(OpCode::JUMPDEST, None, block);
        vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        vcode.add_inst_to_block(OpCode::REVERT, None, block);
    }

    fn build_unique_stop_block(vcode: &mut VCode<OpCode>, block: BlockId, tag: u8) {
        vcode.add_inst_to_block(OpCode::JUMPDEST, None, block);
        let inst = vcode.add_inst_to_block(OpCode::PUSH1, None, block);
        vcode
            .inst_imm_bytes
            .insert((inst, smallvec::smallvec![tag]));
        vcode.add_inst_to_block(OpCode::STOP, None, block);
    }

    fn block_label_kinds(vcode: &VCode<OpCode>, block: BlockId) -> Vec<Label> {
        block_insts(vcode, block)
            .into_iter()
            .filter_map(|inst| match vcode.fixups.get(inst) {
                Some((_, VCodeFixup::Label(label))) => Some(vcode.labels[*label]),
                _ => None,
            })
            .collect()
    }

    #[test]
    fn section_outline_retargets_nonfallthrough_duplicates() {
        let (module, names) = test_module();
        let mut lowered = Vec::new();

        for func in [names["a"], names["b"]] {
            let mut vcode = VCode::<OpCode>::default();
            push_block(&mut vcode, BlockId(0), BlockId(1));
            vcode.add_inst_to_block(OpCode::JUMP, None, BlockId(0));
            build_revert_block(&mut vcode, BlockId(1));
            lowered.push((
                func,
                LoweredFunction {
                    vcode,
                    block_order: vec![BlockId(0), BlockId(1)],
                },
            ));
        }

        let helpers = run_late_section_terminal_outline(&module, &mut lowered);
        assert_eq!(helpers.len(), 1, "expected one shared helper");
        assert_eq!(helpers[0].block_order, vec![BlockId(0)]);

        for (_, lowered) in &lowered {
            assert_eq!(lowered.block_order, vec![BlockId(0)]);
            assert!(
                block_label_kinds(&lowered.vcode, BlockId(0))
                    .iter()
                    .all(|label| matches!(label, Label::SectionCodeUnit(SectionCodeUnitId(0))))
            );
        }
    }

    #[test]
    fn section_outline_unlocks_fallthrough_duplicates() {
        let (module, names) = test_module();
        let mut lowered = Vec::new();

        for (func, tag) in [(names["a"], 0_u8), (names["b"], 1_u8)] {
            let mut vcode = VCode::<OpCode>::default();
            vcode.add_inst_to_block(OpCode::PUSH0, None, BlockId(0));
            push_block(&mut vcode, BlockId(0), BlockId(2));
            vcode.add_inst_to_block(OpCode::JUMPI, None, BlockId(0));
            build_revert_block(&mut vcode, BlockId(1));
            build_unique_stop_block(&mut vcode, BlockId(2), tag);
            lowered.push((
                func,
                LoweredFunction {
                    vcode,
                    block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
                },
            ));
        }

        let helpers = run_late_section_terminal_outline(&module, &mut lowered);
        assert_eq!(helpers.len(), 1, "expected one shared helper");

        for (_, lowered) in &lowered {
            assert_eq!(lowered.block_order, vec![BlockId(0), BlockId(2)]);
            let ops: Vec<_> = block_insts(&lowered.vcode, BlockId(0))
                .into_iter()
                .map(|inst| lowered.vcode.insts[inst] as u8)
                .collect();
            assert_eq!(
                ops,
                vec![
                    OpCode::PUSH0 as u8,
                    OpCode::ISZERO as u8,
                    OpCode::PUSH0 as u8,
                    OpCode::JUMPI as u8,
                ]
            );
            assert!(
                block_label_kinds(&lowered.vcode, BlockId(0))
                    .iter()
                    .all(|label| matches!(label, Label::SectionCodeUnit(SectionCodeUnitId(0))))
            );
        }
    }

    #[test]
    fn section_outline_skips_local_block_fixup_terminals() {
        let (module, names) = test_module();
        let mut lowered = Vec::new();

        for (func, tag) in [(names["a"], 0_u8), (names["b"], 1_u8)] {
            let mut vcode = VCode::<OpCode>::default();
            push_block(&mut vcode, BlockId(0), BlockId(1));
            vcode.add_inst_to_block(OpCode::JUMP, None, BlockId(0));
            push_block(&mut vcode, BlockId(1), BlockId(2));
            vcode.add_inst_to_block(OpCode::JUMP, None, BlockId(1));
            build_unique_stop_block(&mut vcode, BlockId(2), tag);
            lowered.push((
                func,
                LoweredFunction {
                    vcode,
                    block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
                },
            ));
        }

        let helpers = run_late_section_terminal_outline(&module, &mut lowered);
        assert!(helpers.is_empty(), "local block fixups must stay local");
        for (_, lowered) in &lowered {
            assert_eq!(
                lowered.block_order,
                vec![BlockId(0), BlockId(1), BlockId(2)]
            );
        }
    }
}
