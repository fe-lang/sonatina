use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{BlockId, Module, module::FuncRef};

use crate::machinst::{
    lower::{LoweredFunction, SectionCodeUnit},
    vcode::{Label, SectionCodeUnitId, VCode, VCodeFixup, VCodeInst},
};

use super::{
    LateCleanupProfile, is_plain_inst, is_push_opcode,
    late_block_merge::{
        FixupKey, InstKey, StackSummary, block_insts, inst_estimated_size, inst_key,
        is_non_fallthrough_terminal, layout_fallthrough_targets, replace_block_insts,
        sequence_summary,
    },
    opcode::OpCode,
    referenced_insn_label_targets,
};

pub(super) fn run_late_section_terminal_outline(
    module: &Module,
    lowered: &mut [(FuncRef, LoweredFunction<OpCode>)],
    profile: LateCleanupProfile,
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

    run_parameterized_terminal_payload_outline(
        lowered,
        profile,
        &mut section_units,
        &mut next_helper_id,
    );

    section_units
}

const MAX_PARAMETERIZED_PAYLOAD_PARAMS: usize = 4;
const MIN_PARAMETERIZED_PAYLOAD_SAVINGS: isize = 1;
const SECTION_HELPER_FIXUP_SIZE: usize = 5;

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

#[derive(Clone)]
struct LiteralSegment {
    start: usize,
    insts: Vec<VCodeInst>,
    key: Vec<InstKey>,
    estimated_size: usize,
}

#[derive(Clone)]
struct PayloadStore {
    value: LiteralSegment,
    address: LiteralSegment,
}

#[derive(Clone)]
struct PayloadOccurrence {
    func_idx: usize,
    block: BlockId,
    order_idx: usize,
    leading_jumpdest: Option<VCodeInst>,
    stores: Vec<PayloadStore>,
    terminal_len: LiteralSegment,
    terminal_offset: LiteralSegment,
    terminal_op: OpCode,
    block_size: usize,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct PayloadLayoutKey {
    terminal_op: u8,
    terminal_len: Vec<InstKey>,
    terminal_offset: Vec<InstKey>,
    store_addresses: Vec<Vec<InstKey>>,
}

struct PayloadGroupCandidate {
    donor: PayloadOccurrence,
    actions: Vec<PayloadRewriteAction>,
    param_store_idxs: Vec<usize>,
    total_savings: isize,
}

#[derive(Clone)]
struct PayloadRewriteAction {
    func_idx: usize,
    block: BlockId,
    order_idx: usize,
    leading_jumpdest: Option<VCodeInst>,
    param_values: Vec<LiteralSegment>,
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

fn run_parameterized_terminal_payload_outline(
    lowered: &mut [(FuncRef, LoweredFunction<OpCode>)],
    profile: LateCleanupProfile,
    section_units: &mut Vec<SectionCodeUnit<OpCode>>,
    next_helper_id: &mut u32,
) {
    if profile == LateCleanupProfile::Off {
        return;
    }

    while let Some(candidate) = select_best_parameterized_payload_group(lowered, profile) {
        let helper_id = SectionCodeUnitId(*next_helper_id);
        *next_helper_id = next_helper_id
            .checked_add(1)
            .expect("section helper id overflow");

        section_units.push(build_parameterized_payload_helper(
            helper_id,
            &candidate.donor,
            &candidate.param_store_idxs,
            lowered,
        ));

        let mut actions = candidate.actions;
        actions.sort_by(|a, b| {
            a.func_idx
                .cmp(&b.func_idx)
                .then_with(|| a.order_idx.cmp(&b.order_idx))
        });

        for action in actions {
            let (_, lowered) = &mut lowered[action.func_idx];
            rewrite_parameterized_payload_stub(&mut lowered.vcode, action, helper_id);
        }
    }
}

fn select_best_parameterized_payload_group(
    lowered: &[(FuncRef, LoweredFunction<OpCode>)],
    profile: LateCleanupProfile,
) -> Option<PayloadGroupCandidate> {
    let allow_return = profile == LateCleanupProfile::Size;
    let label_targets: Vec<_> = lowered
        .iter()
        .map(|(_, lowered)| referenced_insn_label_targets(&lowered.vcode))
        .collect();
    let mut occurrences_by_layout: FxHashMap<PayloadLayoutKey, Vec<PayloadOccurrence>> =
        FxHashMap::default();

    for (func_idx, (_, lowered)) in lowered.iter().enumerate() {
        for (order_idx, &block) in lowered.block_order.iter().enumerate() {
            if let Some(occurrence) = analyze_payload_occurrence(
                func_idx,
                &lowered.vcode,
                block,
                order_idx,
                &label_targets[func_idx],
                allow_return,
            ) {
                occurrences_by_layout
                    .entry(payload_layout_key(&occurrence))
                    .or_default()
                    .push(occurrence);
            }
        }
    }

    occurrences_by_layout
        .into_values()
        .filter_map(build_payload_group_candidate)
        .max_by(|a, b| a.total_savings.cmp(&b.total_savings))
}

fn build_payload_group_candidate(
    occurrences: Vec<PayloadOccurrence>,
) -> Option<PayloadGroupCandidate> {
    if occurrences.len() < 2 {
        return None;
    }

    let param_store_idxs = parameterized_store_indexes(&occurrences)?;
    if param_store_idxs.is_empty() || param_store_idxs.len() > MAX_PARAMETERIZED_PAYLOAD_PARAMS {
        return None;
    }

    let old_size = occurrences
        .iter()
        .map(|occurrence| occurrence.block_size)
        .sum::<usize>();
    let helper_size = parameterized_helper_estimated_size(&occurrences[0], &param_store_idxs);
    let actions = occurrences
        .iter()
        .map(|occurrence| PayloadRewriteAction {
            func_idx: occurrence.func_idx,
            block: occurrence.block,
            order_idx: occurrence.order_idx,
            leading_jumpdest: occurrence.leading_jumpdest,
            param_values: param_store_idxs
                .iter()
                .map(|&idx| occurrence.stores[idx].value.clone())
                .collect(),
        })
        .collect::<Vec<_>>();
    let stub_size = actions
        .iter()
        .map(parameterized_stub_estimated_size)
        .sum::<usize>();
    let total_savings = isize::try_from(old_size).expect("payload size overflow")
        - isize::try_from(helper_size + stub_size).expect("payload size overflow");

    (total_savings >= MIN_PARAMETERIZED_PAYLOAD_SAVINGS).then_some(PayloadGroupCandidate {
        donor: occurrences[0].clone(),
        actions,
        param_store_idxs,
        total_savings,
    })
}

fn parameterized_store_indexes(occurrences: &[PayloadOccurrence]) -> Option<Vec<usize>> {
    let first = occurrences.first()?;
    let store_count = first.stores.len();
    if occurrences
        .iter()
        .any(|occurrence| occurrence.stores.len() != store_count)
    {
        return None;
    }

    Some(
        (0..store_count)
            .filter(|&idx| {
                occurrences.iter().any(|occurrence| {
                    occurrence.stores[idx].value.key != first.stores[idx].value.key
                })
            })
            .collect(),
    )
}

fn parameterized_helper_estimated_size(
    occurrence: &PayloadOccurrence,
    param_store_idxs: &[usize],
) -> usize {
    let stores_size = occurrence
        .stores
        .iter()
        .enumerate()
        .map(|(idx, store)| {
            if param_store_idxs.contains(&idx) {
                store.address.estimated_size + 1
            } else {
                store.value.estimated_size + store.address.estimated_size + 1
            }
        })
        .sum::<usize>();

    1 + stores_size
        + occurrence.terminal_len.estimated_size
        + occurrence.terminal_offset.estimated_size
        + 1
}

fn parameterized_stub_estimated_size(action: &PayloadRewriteAction) -> usize {
    usize::from(action.leading_jumpdest.is_some())
        + action
            .param_values
            .iter()
            .map(|segment| segment.estimated_size)
            .sum::<usize>()
        + SECTION_HELPER_FIXUP_SIZE
        + 1
}

fn payload_layout_key(occurrence: &PayloadOccurrence) -> PayloadLayoutKey {
    PayloadLayoutKey {
        terminal_op: occurrence.terminal_op as u8,
        terminal_len: occurrence.terminal_len.key.clone(),
        terminal_offset: occurrence.terminal_offset.key.clone(),
        store_addresses: occurrence
            .stores
            .iter()
            .map(|store| store.address.key.clone())
            .collect(),
    }
}

fn analyze_payload_occurrence(
    func_idx: usize,
    vcode: &VCode<OpCode>,
    block: BlockId,
    order_idx: usize,
    label_targets: &FxHashSet<VCodeInst>,
    allow_return: bool,
) -> Option<PayloadOccurrence> {
    let insts = block_insts(vcode, block);
    let leading_jumpdest = insts
        .first()
        .copied()
        .filter(|&inst| (vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8));
    let semantic_start = usize::from(leading_jumpdest.is_some());
    let semantic_insts = insts.get(semantic_start..)?;
    if semantic_insts.is_empty()
        || semantic_insts.iter().copied().any(|inst| {
            (vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8) || label_targets.contains(&inst)
        })
    {
        return None;
    }

    let &last = semantic_insts.last()?;
    let terminal_op = vcode.insts[last];
    if (terminal_op as u8) != (OpCode::REVERT as u8)
        && (!allow_return || (terminal_op as u8) != (OpCode::RETURN as u8))
    {
        return None;
    }

    let terminal_offset = parse_literal_segment(
        vcode,
        label_targets,
        semantic_insts,
        semantic_insts.len() - 1,
    )?;
    let terminal_len =
        parse_literal_segment(vcode, label_targets, semantic_insts, terminal_offset.start)?;
    let mut stores = Vec::new();
    let mut cursor = terminal_len.start;
    while cursor > 0 {
        let mstore_idx = cursor.checked_sub(1)?;
        if (vcode.insts[semantic_insts[mstore_idx]] as u8) != (OpCode::MSTORE as u8) {
            return None;
        }
        let address = parse_literal_segment(vcode, label_targets, semantic_insts, mstore_idx)?;
        let value = parse_literal_segment(vcode, label_targets, semantic_insts, address.start)?;
        cursor = value.start;
        stores.push(PayloadStore { value, address });
    }
    if stores.is_empty() {
        return None;
    }
    stores.reverse();

    Some(PayloadOccurrence {
        func_idx,
        block,
        order_idx,
        leading_jumpdest,
        stores,
        terminal_len,
        terminal_offset,
        terminal_op,
        block_size: insts
            .iter()
            .copied()
            .map(|inst| inst_estimated_size(vcode, inst))
            .sum(),
    })
}

fn parse_literal_segment(
    vcode: &VCode<OpCode>,
    label_targets: &FxHashSet<VCodeInst>,
    insts: &[VCodeInst],
    end: usize,
) -> Option<LiteralSegment> {
    for start in (0..end).rev() {
        let segment = &insts[start..end];
        if is_pure_literal_segment(vcode, label_targets, segment) {
            let mut key = Vec::with_capacity(segment.len());
            let mut estimated_size = 0;
            for &inst in segment {
                key.push(inst_key(vcode, inst)?);
                estimated_size += inst_estimated_size(vcode, inst);
            }
            return Some(LiteralSegment {
                start,
                insts: segment.to_vec(),
                key,
                estimated_size,
            });
        }
    }

    None
}

fn is_pure_literal_segment(
    vcode: &VCode<OpCode>,
    label_targets: &FxHashSet<VCodeInst>,
    insts: &[VCodeInst],
) -> bool {
    !insts.is_empty()
        && insts
            .iter()
            .copied()
            .all(|inst| is_pure_literal_inst(vcode, label_targets, inst))
        && sequence_summary(vcode, insts)
            == StackSummary {
                min_before: 0,
                delta: 1,
            }
}

fn is_pure_literal_inst(
    vcode: &VCode<OpCode>,
    label_targets: &FxHashSet<VCodeInst>,
    inst: VCodeInst,
) -> bool {
    if label_targets.contains(&inst) || vcode.fixups.get(inst).is_some() {
        return false;
    }

    let op = vcode.insts[inst];
    if is_push_opcode(op) {
        return if (op as u8) == (OpCode::PUSH0 as u8) {
            vcode.inst_imm_bytes.get(inst).is_none()
        } else {
            vcode.inst_imm_bytes.get(inst).is_some()
        };
    }
    if vcode.inst_imm_bytes.get(inst).is_some() {
        return false;
    }

    matches!(
        op,
        OpCode::ADD
            | OpCode::MUL
            | OpCode::SUB
            | OpCode::DIV
            | OpCode::SDIV
            | OpCode::MOD
            | OpCode::SMOD
            | OpCode::ADDMOD
            | OpCode::MULMOD
            | OpCode::EXP
            | OpCode::SIGNEXTEND
            | OpCode::LT
            | OpCode::GT
            | OpCode::SLT
            | OpCode::SGT
            | OpCode::EQ
            | OpCode::ISZERO
            | OpCode::AND
            | OpCode::OR
            | OpCode::XOR
            | OpCode::NOT
            | OpCode::BYTE
            | OpCode::SHL
            | OpCode::SHR
            | OpCode::SAR
            | OpCode::CLZ
    )
}

fn build_parameterized_payload_helper(
    id: SectionCodeUnitId,
    donor: &PayloadOccurrence,
    param_store_idxs: &[usize],
    lowered: &[(FuncRef, LoweredFunction<OpCode>)],
) -> SectionCodeUnit<OpCode> {
    let block = BlockId(0);
    let mut vcode = VCode::<OpCode>::default();
    let donor_vcode = &lowered[donor.func_idx].1.vcode;
    vcode.add_inst_to_block(OpCode::JUMPDEST, None, block);

    for (idx, store) in donor.stores.iter().enumerate() {
        if !param_store_idxs.contains(&idx) {
            clone_segment(&mut vcode, donor_vcode, &store.value, block);
        }
        clone_segment(&mut vcode, donor_vcode, &store.address, block);
        vcode.add_inst_to_block(OpCode::MSTORE, None, block);
    }
    clone_segment(&mut vcode, donor_vcode, &donor.terminal_len, block);
    clone_segment(&mut vcode, donor_vcode, &donor.terminal_offset, block);
    vcode.add_inst_to_block(donor.terminal_op, None, block);

    SectionCodeUnit {
        id,
        name: format!("__evm_shared_tail_{}", id.0),
        vcode,
        block_order: vec![block],
    }
}

fn clone_segment(
    dst: &mut VCode<OpCode>,
    src: &VCode<OpCode>,
    segment: &LiteralSegment,
    block: BlockId,
) {
    for &inst in &segment.insts {
        clone_inst(dst, src, inst, block);
    }
}

fn rewrite_parameterized_payload_stub(
    vcode: &mut VCode<OpCode>,
    action: PayloadRewriteAction,
    helper_id: SectionCodeUnitId,
) {
    let mut rebuilt = Vec::new();
    if let Some(jumpdest) = action.leading_jumpdest {
        rebuilt.push(jumpdest);
    }

    for segment in action.param_values.iter().rev() {
        for &inst in &segment.insts {
            let cloned = clone_inst_in_place(vcode, inst, action.block);
            rebuilt.push(cloned);
        }
    }

    let push = vcode.add_inst_to_block(OpCode::PUSH0, None, action.block);
    let label = vcode.labels.push(Label::SectionCodeUnit(helper_id));
    vcode.fixups.insert((push, VCodeFixup::Label(label)));
    rebuilt.push(push);
    rebuilt.push(vcode.add_inst_to_block(OpCode::JUMP, None, action.block));
    replace_block_insts(vcode, action.block, &rebuilt);
}

fn clone_inst_in_place(vcode: &mut VCode<OpCode>, inst: VCodeInst, block: BlockId) -> VCodeInst {
    let op = vcode.insts[inst];
    let source_insn = vcode.inst_ir[inst].expand();
    let imm = vcode
        .inst_imm_bytes
        .get(inst)
        .map(|(_, bytes)| bytes.clone());
    let fixup = vcode.fixups.get(inst).map(|(_, fixup)| fixup.clone());
    let new_inst = vcode.add_inst_to_block(op, source_insn, block);
    if let Some(bytes) = imm {
        vcode.inst_imm_bytes.insert((new_inst, bytes));
    }
    if let Some(fixup) = fixup {
        let cloned_fixup = match fixup {
            VCodeFixup::Label(label) => {
                let cloned = vcode.labels.push(vcode.labels[label]);
                VCodeFixup::Label(cloned)
            }
            VCodeFixup::Sym(sym) => VCodeFixup::Sym(sym),
        };
        vcode.fixups.insert((new_inst, cloned_fixup));
    }
    new_inst
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

    fn push_bytes(vcode: &mut VCode<OpCode>, block: BlockId, bytes: &[u8]) -> VCodeInst {
        let op = match bytes.len() {
            1 => OpCode::PUSH1,
            4 => OpCode::PUSH4,
            32 => OpCode::PUSH32,
            len => panic!("test helper does not support PUSH{len}"),
        };
        let inst = vcode.add_inst_to_block(op, None, block);
        vcode.inst_imm_bytes.insert((inst, bytes.into()));
        inst
    }

    fn push_u8(vcode: &mut VCode<OpCode>, block: BlockId, value: u8) -> VCodeInst {
        push_bytes(vcode, block, &[value])
    }

    fn build_parameterized_payload_block(
        vcode: &mut VCode<OpCode>,
        block: BlockId,
        value_byte: u8,
        terminal: OpCode,
        leading_jumpdest: bool,
        dynamic_address: bool,
    ) {
        if leading_jumpdest {
            vcode.add_inst_to_block(OpCode::JUMPDEST, None, block);
        }

        push_bytes(vcode, block, &[0xde, 0xad, 0xbe, 0xef]);
        push_u8(vcode, block, 0x80);
        vcode.add_inst_to_block(OpCode::MSTORE, None, block);
        push_bytes(vcode, block, &[value_byte; 32]);
        if dynamic_address {
            vcode.add_inst_to_block(OpCode::CALLVALUE, None, block);
        } else {
            push_u8(vcode, block, 0xa0);
        }
        vcode.add_inst_to_block(OpCode::MSTORE, None, block);
        vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        push_u8(vcode, block, 0xc0);
        vcode.add_inst_to_block(OpCode::MSTORE, None, block);
        push_u8(vcode, block, 0x60);
        push_u8(vcode, block, 0x80);
        vcode.add_inst_to_block(terminal, None, block);
    }

    fn block_ops(vcode: &VCode<OpCode>, block: BlockId) -> Vec<u8> {
        block_insts(vcode, block)
            .into_iter()
            .map(|inst| vcode.insts[inst] as u8)
            .collect()
    }

    fn helper_ops(helper: &SectionCodeUnit<OpCode>) -> Vec<u8> {
        block_insts(&helper.vcode, BlockId(0))
            .into_iter()
            .map(|inst| helper.vcode.insts[inst] as u8)
            .collect()
    }

    fn helper_contains_imm(helper: &SectionCodeUnit<OpCode>, bytes: &[u8]) -> bool {
        helper
            .vcode
            .inst_imm_bytes
            .values()
            .any(|(_, imm)| imm.as_slice() == bytes)
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

        let helpers =
            run_late_section_terminal_outline(&module, &mut lowered, LateCleanupProfile::Speed);
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

        let helpers =
            run_late_section_terminal_outline(&module, &mut lowered, LateCleanupProfile::Speed);
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

        let helpers =
            run_late_section_terminal_outline(&module, &mut lowered, LateCleanupProfile::Speed);
        assert!(helpers.is_empty(), "local block fixups must stay local");
        for (_, lowered) in &lowered {
            assert_eq!(
                lowered.block_order,
                vec![BlockId(0), BlockId(1), BlockId(2)]
            );
        }
    }

    #[test]
    fn parameterized_revert_payload_outlines_different_literal_words() {
        let (module, names) = test_module();
        let mut lowered = Vec::new();

        for (func, value_byte) in [(names["a"], 0x11), (names["b"], 0x22)] {
            let mut vcode = VCode::<OpCode>::default();
            build_parameterized_payload_block(
                &mut vcode,
                BlockId(0),
                value_byte,
                OpCode::REVERT,
                true,
                false,
            );
            lowered.push((
                func,
                LoweredFunction {
                    vcode,
                    block_order: vec![BlockId(0)],
                },
            ));
        }

        let helpers =
            run_late_section_terminal_outline(&module, &mut lowered, LateCleanupProfile::Speed);
        assert_eq!(helpers.len(), 1, "expected one shared payload helper");
        assert!(
            !helper_contains_imm(&helpers[0], &[0x11; 32])
                && !helper_contains_imm(&helpers[0], &[0x22; 32]),
            "parameter words should stay in caller stubs"
        );
        assert_eq!(
            helper_ops(&helpers[0]),
            vec![
                OpCode::JUMPDEST as u8,
                OpCode::PUSH4 as u8,
                OpCode::PUSH1 as u8,
                OpCode::MSTORE as u8,
                OpCode::PUSH1 as u8,
                OpCode::MSTORE as u8,
                OpCode::PUSH0 as u8,
                OpCode::PUSH1 as u8,
                OpCode::MSTORE as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::REVERT as u8,
            ]
        );

        for (_, lowered) in &lowered {
            assert_eq!(
                block_ops(&lowered.vcode, BlockId(0)),
                vec![
                    OpCode::JUMPDEST as u8,
                    OpCode::PUSH32 as u8,
                    OpCode::PUSH0 as u8,
                    OpCode::JUMP as u8,
                ]
            );
            assert!(matches!(
                block_label_kinds(&lowered.vcode, BlockId(0)).as_slice(),
                [Label::SectionCodeUnit(SectionCodeUnitId(0))]
            ));
        }
    }

    #[test]
    fn parameterized_revert_payload_keeps_fallthrough_stub_in_layout() {
        let (module, names) = test_module();
        let mut lowered = Vec::new();

        for (func, value_byte) in [(names["a"], 0x33), (names["b"], 0x44)] {
            let mut vcode = VCode::<OpCode>::default();
            vcode.add_inst_to_block(OpCode::PUSH0, None, BlockId(0));
            push_block(&mut vcode, BlockId(0), BlockId(2));
            vcode.add_inst_to_block(OpCode::JUMPI, None, BlockId(0));
            build_parameterized_payload_block(
                &mut vcode,
                BlockId(1),
                value_byte,
                OpCode::REVERT,
                false,
                false,
            );
            build_unique_stop_block(&mut vcode, BlockId(2), value_byte);
            lowered.push((
                func,
                LoweredFunction {
                    vcode,
                    block_order: vec![BlockId(0), BlockId(1), BlockId(2)],
                },
            ));
        }

        let helpers =
            run_late_section_terminal_outline(&module, &mut lowered, LateCleanupProfile::Speed);
        assert_eq!(helpers.len(), 1, "expected one shared payload helper");

        for (_, lowered) in &lowered {
            assert_eq!(
                lowered.block_order,
                vec![BlockId(0), BlockId(1), BlockId(2)]
            );
            assert_eq!(
                block_ops(&lowered.vcode, BlockId(1)),
                vec![
                    OpCode::PUSH32 as u8,
                    OpCode::PUSH0 as u8,
                    OpCode::JUMP as u8,
                ]
            );
        }
    }

    #[test]
    fn parameterized_payload_skips_dynamic_store_address() {
        let (module, names) = test_module();
        let mut lowered = Vec::new();

        for (func, value_byte) in [(names["a"], 0x55), (names["b"], 0x66)] {
            let mut vcode = VCode::<OpCode>::default();
            build_parameterized_payload_block(
                &mut vcode,
                BlockId(0),
                value_byte,
                OpCode::REVERT,
                true,
                true,
            );
            lowered.push((
                func,
                LoweredFunction {
                    vcode,
                    block_order: vec![BlockId(0)],
                },
            ));
        }

        let helpers =
            run_late_section_terminal_outline(&module, &mut lowered, LateCleanupProfile::Speed);
        assert!(
            helpers.is_empty(),
            "dynamic store addresses are not safe to outline"
        );
    }

    #[test]
    fn parameterized_return_payload_outlines_only_in_size_profile() {
        let (module, names) = test_module();
        let build_lowered = || {
            [(names["a"], 0x77), (names["b"], 0x88)]
                .into_iter()
                .map(|(func, value_byte)| {
                    let mut vcode = VCode::<OpCode>::default();
                    build_parameterized_payload_block(
                        &mut vcode,
                        BlockId(0),
                        value_byte,
                        OpCode::RETURN,
                        true,
                        false,
                    );
                    (
                        func,
                        LoweredFunction {
                            vcode,
                            block_order: vec![BlockId(0)],
                        },
                    )
                })
                .collect::<Vec<_>>()
        };
        let mut speed_lowered = build_lowered();
        let mut size_lowered = build_lowered();

        let speed_helpers = run_late_section_terminal_outline(
            &module,
            &mut speed_lowered,
            LateCleanupProfile::Speed,
        );
        assert!(
            speed_helpers.is_empty(),
            "speed profile should avoid adding jumps to return paths"
        );

        let size_helpers =
            run_late_section_terminal_outline(&module, &mut size_lowered, LateCleanupProfile::Size);
        assert_eq!(
            size_helpers.len(),
            1,
            "size profile should outline profitable return payloads"
        );
    }
}
