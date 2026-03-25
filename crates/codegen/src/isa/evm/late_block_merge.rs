use cranelift_entity::EntityList;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use sonatina_ir::{BlockId, inst::data::SymbolRef, module::FuncRef};

use crate::machinst::vcode::{Label, VCode, VCodeFixup, VCodeInst};

use super::{
    LateCleanupProfile, is_plain_inst, is_push_opcode, opcode::OpCode,
    referenced_insn_label_targets,
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct StackSummary {
    min_before: u16,
    delta: i16,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum FixupKey {
    None,
    Block(BlockId),
    Function(FuncRef),
    Sym(crate::machinst::vcode::SymFixupKind, SymbolRef),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct InstKey {
    opcode: u8,
    imm: SmallVec<[u8; 8]>,
    fixup: FixupKey,
}

struct RegionAnalysis {
    key: Vec<InstKey>,
    summary: StackSummary,
    estimated_size: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct TailDonor {
    block: BlockId,
    start: usize,
}

#[derive(Clone, Debug)]
struct TailGroup {
    donors: Vec<TailDonor>,
    suffix_len: usize,
    suffix_size: usize,
    first_order_idx: usize,
    savings: isize,
}

#[derive(Clone, Debug)]
struct ExactBlockGroup {
    blocks: Vec<BlockId>,
    estimated_size: usize,
}

#[derive(Clone, Copy, Debug)]
struct FallthroughUnlock {
    pred: BlockId,
    fallthrough: BlockId,
    other_succ: BlockId,
    tail_anchor: BlockId,
    push: VCodeInst,
    has_trailing_iszero: bool,
    order_idx: usize,
    savings: isize,
}

#[derive(Default)]
struct LateBlockMerge {
    next_synth_block: u32,
}

pub(super) fn run_late_block_merge(
    vcode: &mut VCode<OpCode>,
    block_order: &mut Vec<BlockId>,
    entry_block: BlockId,
    profile: LateCleanupProfile,
) -> bool {
    if profile == LateCleanupProfile::Off {
        return false;
    }

    let mut changed = run_exact_block_dedup(vcode, block_order, entry_block);
    if profile == LateCleanupProfile::Size {
        changed |= run_common_tail_merge(vcode, block_order, entry_block);
    }
    changed
}

fn run_exact_block_dedup(
    vcode: &mut VCode<OpCode>,
    block_order: &mut Vec<BlockId>,
    entry_block: BlockId,
) -> bool {
    LateBlockMerge::new(vcode, block_order).run_exact_block_dedup(vcode, block_order, entry_block)
}

fn run_common_tail_merge(
    vcode: &mut VCode<OpCode>,
    block_order: &mut Vec<BlockId>,
    entry_block: BlockId,
) -> bool {
    LateBlockMerge::new(vcode, block_order).run_common_tail_merge(vcode, block_order, entry_block)
}

fn compose(a: StackSummary, b: StackSummary) -> StackSummary {
    let req_from_a_for_b = (i32::from(b.min_before) - i32::from(a.delta)).max(0) as u16;
    let delta = i32::from(a.delta) + i32::from(b.delta);
    StackSummary {
        min_before: a.min_before.max(req_from_a_for_b),
        delta: i16::try_from(delta).expect("stack delta overflow"),
    }
}

fn opcode_stack_summary(op: OpCode) -> StackSummary {
    let byte = op as u8;
    if (OpCode::PUSH0 as u8..=OpCode::PUSH32 as u8).contains(&byte) {
        return StackSummary {
            min_before: 0,
            delta: 1,
        };
    }
    if (OpCode::DUP1 as u8..=OpCode::DUP16 as u8).contains(&byte) {
        return StackSummary {
            min_before: u16::from(byte - OpCode::DUP1 as u8 + 1),
            delta: 1,
        };
    }
    if (OpCode::SWAP1 as u8..=OpCode::SWAP16 as u8).contains(&byte) {
        return StackSummary {
            min_before: u16::from(byte - OpCode::SWAP1 as u8 + 2),
            delta: 0,
        };
    }
    if (OpCode::LOG0 as u8..=OpCode::LOG4 as u8).contains(&byte) {
        let topics = byte - OpCode::LOG0 as u8;
        return StackSummary {
            min_before: u16::from(2 + topics),
            delta: -i16::from(2 + topics),
        };
    }

    match op {
        OpCode::STOP | OpCode::JUMPDEST | OpCode::INVALID => StackSummary::default(),
        OpCode::ADD
        | OpCode::MUL
        | OpCode::SUB
        | OpCode::DIV
        | OpCode::SDIV
        | OpCode::MOD
        | OpCode::SMOD
        | OpCode::EXP
        | OpCode::SIGNEXTEND
        | OpCode::LT
        | OpCode::GT
        | OpCode::SLT
        | OpCode::SGT
        | OpCode::EQ
        | OpCode::AND
        | OpCode::OR
        | OpCode::XOR
        | OpCode::BYTE
        | OpCode::SHL
        | OpCode::SHR
        | OpCode::SAR
        | OpCode::KECCAK256 => StackSummary {
            min_before: 2,
            delta: -1,
        },
        OpCode::ADDMOD | OpCode::MULMOD => StackSummary {
            min_before: 3,
            delta: -2,
        },
        OpCode::ISZERO | OpCode::NOT | OpCode::CLZ | OpCode::MLOAD | OpCode::SLOAD => {
            StackSummary {
                min_before: 1,
                delta: 0,
            }
        }
        OpCode::ADDRESS
        | OpCode::ORIGIN
        | OpCode::CALLER
        | OpCode::CALLVALUE
        | OpCode::CALLDATASIZE
        | OpCode::CODESIZE
        | OpCode::GASPRICE
        | OpCode::RETURNDATASIZE
        | OpCode::COINBASE
        | OpCode::TIMESTAMP
        | OpCode::NUMBER
        | OpCode::PREVRANDAO
        | OpCode::GASLIMIT
        | OpCode::CHAINID
        | OpCode::SELFBALANCE
        | OpCode::BASEFEE
        | OpCode::BLOBBASEFEE
        | OpCode::PC
        | OpCode::MSIZE
        | OpCode::GAS => StackSummary {
            min_before: 0,
            delta: 1,
        },
        OpCode::BALANCE
        | OpCode::CALLDATALOAD
        | OpCode::EXTCODESIZE
        | OpCode::EXTCODEHASH
        | OpCode::BLOCKHASH
        | OpCode::BLOBHASH
        | OpCode::TLOAD => StackSummary {
            min_before: 1,
            delta: 0,
        },
        OpCode::CALLDATACOPY | OpCode::CODECOPY | OpCode::RETURNDATACOPY | OpCode::MCOPY => {
            StackSummary {
                min_before: 3,
                delta: -3,
            }
        }
        OpCode::EXTCODECOPY => StackSummary {
            min_before: 4,
            delta: -4,
        },
        OpCode::POP => StackSummary {
            min_before: 1,
            delta: -1,
        },
        OpCode::MSTORE | OpCode::MSTORE8 | OpCode::SSTORE | OpCode::TSTORE => StackSummary {
            min_before: 2,
            delta: -2,
        },
        OpCode::JUMP => StackSummary {
            min_before: 1,
            delta: -1,
        },
        OpCode::JUMPI => StackSummary {
            min_before: 2,
            delta: -2,
        },
        OpCode::CREATE => StackSummary {
            min_before: 3,
            delta: -2,
        },
        OpCode::CALL | OpCode::CALLCODE => StackSummary {
            min_before: 7,
            delta: -6,
        },
        OpCode::RETURN | OpCode::REVERT => StackSummary {
            min_before: 2,
            delta: -2,
        },
        OpCode::DELEGATECALL | OpCode::STATICCALL => StackSummary {
            min_before: 6,
            delta: -5,
        },
        OpCode::CREATE2 => StackSummary {
            min_before: 4,
            delta: -3,
        },
        OpCode::SELFDESTRUCT => StackSummary {
            min_before: 1,
            delta: -1,
        },
        OpCode::PUSH0
        | OpCode::PUSH1
        | OpCode::PUSH2
        | OpCode::PUSH3
        | OpCode::PUSH4
        | OpCode::PUSH5
        | OpCode::PUSH6
        | OpCode::PUSH7
        | OpCode::PUSH8
        | OpCode::PUSH9
        | OpCode::PUSH10
        | OpCode::PUSH11
        | OpCode::PUSH12
        | OpCode::PUSH13
        | OpCode::PUSH14
        | OpCode::PUSH15
        | OpCode::PUSH16
        | OpCode::PUSH17
        | OpCode::PUSH18
        | OpCode::PUSH19
        | OpCode::PUSH20
        | OpCode::PUSH21
        | OpCode::PUSH22
        | OpCode::PUSH23
        | OpCode::PUSH24
        | OpCode::PUSH25
        | OpCode::PUSH26
        | OpCode::PUSH27
        | OpCode::PUSH28
        | OpCode::PUSH29
        | OpCode::PUSH30
        | OpCode::PUSH31
        | OpCode::PUSH32
        | OpCode::DUP1
        | OpCode::DUP2
        | OpCode::DUP3
        | OpCode::DUP4
        | OpCode::DUP5
        | OpCode::DUP6
        | OpCode::DUP7
        | OpCode::DUP8
        | OpCode::DUP9
        | OpCode::DUP10
        | OpCode::DUP11
        | OpCode::DUP12
        | OpCode::DUP13
        | OpCode::DUP14
        | OpCode::DUP15
        | OpCode::DUP16
        | OpCode::SWAP1
        | OpCode::SWAP2
        | OpCode::SWAP3
        | OpCode::SWAP4
        | OpCode::SWAP5
        | OpCode::SWAP6
        | OpCode::SWAP7
        | OpCode::SWAP8
        | OpCode::SWAP9
        | OpCode::SWAP10
        | OpCode::SWAP11
        | OpCode::SWAP12
        | OpCode::SWAP13
        | OpCode::SWAP14
        | OpCode::SWAP15
        | OpCode::SWAP16
        | OpCode::LOG0
        | OpCode::LOG1
        | OpCode::LOG2
        | OpCode::LOG3
        | OpCode::LOG4 => unreachable!("range cases handled above"),
    }
}

fn sequence_summary(vcode: &VCode<OpCode>, insts: &[VCodeInst]) -> StackSummary {
    insts
        .iter()
        .copied()
        .fold(StackSummary::default(), |summary, inst| {
            compose(summary, opcode_stack_summary(vcode.insts[inst]))
        })
}

fn is_non_fallthrough_terminal(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::JUMP
            | OpCode::RETURN
            | OpCode::REVERT
            | OpCode::STOP
            | OpCode::INVALID
            | OpCode::SELFDESTRUCT
    )
}

fn may_fall_through(op: OpCode) -> bool {
    !is_non_fallthrough_terminal(op)
}

fn inst_estimated_size(vcode: &VCode<OpCode>, inst: VCodeInst) -> usize {
    1 + if vcode.fixups.get(inst).is_some() {
        4
    } else {
        vcode
            .inst_imm_bytes
            .get(inst)
            .map_or(0, |(_, bytes)| bytes.len())
    }
}

fn inst_key(vcode: &VCode<OpCode>, inst: VCodeInst) -> Option<InstKey> {
    let fixup = match vcode.fixups.get(inst) {
        None => FixupKey::None,
        Some((_, VCodeFixup::Label(label))) => match vcode.labels[*label] {
            Label::Insn(_) => return None,
            Label::Block(block) => FixupKey::Block(block),
            Label::Function(func) => FixupKey::Function(func),
        },
        Some((_, VCodeFixup::Sym(sym))) => FixupKey::Sym(sym.kind.clone(), sym.sym.clone()),
    };

    Some(InstKey {
        opcode: vcode.insts[inst] as u8,
        imm: vcode
            .inst_imm_bytes
            .get(inst)
            .map_or_else(SmallVec::new, |(_, bytes)| bytes.clone()),
        fixup,
    })
}

fn analyze_region(vcode: &VCode<OpCode>, insts: &[VCodeInst]) -> Option<RegionAnalysis> {
    let mut key = Vec::with_capacity(insts.len());
    let mut estimated_size = 0usize;
    for &inst in insts {
        if (vcode.insts[inst] as u8) == (OpCode::JUMPDEST as u8) {
            return None;
        }
        key.push(inst_key(vcode, inst)?);
        estimated_size += inst_estimated_size(vcode, inst);
    }

    Some(RegionAnalysis {
        key,
        summary: sequence_summary(vcode, insts),
        estimated_size,
    })
}

fn block_insts(vcode: &VCode<OpCode>, block: BlockId) -> Vec<VCodeInst> {
    vcode.block_insns(block).collect()
}

fn replace_block_insts(vcode: &mut VCode<OpCode>, block: BlockId, insts: &[VCodeInst]) {
    let mut list: EntityList<VCodeInst> = Default::default();
    for &inst in insts {
        list.push(inst, &mut vcode.insts_pool);
    }
    vcode.blocks[block] = list;
}

fn create_inst(vcode: &mut VCode<OpCode>, op: OpCode) -> VCodeInst {
    let inst = vcode.insts.push(op);
    vcode.inst_ir[inst] = None.into();
    inst
}

fn clone_inst(vcode: &mut VCode<OpCode>, inst: VCodeInst, block: BlockId) -> VCodeInst {
    let new_inst = vcode.add_inst_to_block(vcode.insts[inst], vcode.inst_ir[inst].expand(), block);
    if let Some((_, bytes)) = vcode.inst_imm_bytes.get(inst) {
        vcode.inst_imm_bytes.insert((new_inst, bytes.clone()));
    }
    if let Some((_, fixup)) = vcode.fixups.get(inst) {
        let cloned_fixup = match fixup {
            VCodeFixup::Label(label) => {
                let cloned = vcode.labels.push(vcode.labels[*label]);
                VCodeFixup::Label(cloned)
            }
            VCodeFixup::Sym(sym) => VCodeFixup::Sym(sym.clone()),
        };
        vcode.fixups.insert((new_inst, cloned_fixup));
    }
    new_inst
}

fn canonical_block(aliases: &FxHashMap<BlockId, BlockId>, mut block: BlockId) -> BlockId {
    while let Some(&next) = aliases.get(&block) {
        if next == block {
            break;
        }
        block = next;
    }
    block
}

fn rewrite_block_labels(vcode: &mut VCode<OpCode>, aliases: &FxHashMap<BlockId, BlockId>) {
    let labels: Vec<_> = vcode.labels.keys().collect();
    for label in labels {
        if let Label::Block(block) = vcode.labels[label] {
            let canonical = canonical_block(aliases, block);
            if canonical != block {
                vcode.labels[label] = Label::Block(canonical);
            }
        }
    }
}

fn layout_fallthrough_targets(
    vcode: &VCode<OpCode>,
    block_order: &[BlockId],
) -> FxHashSet<BlockId> {
    let mut targets = FxHashSet::default();
    for window in block_order.windows(2) {
        let prev = window[0];
        let next = window[1];
        let prev_last = block_insts(vcode, prev).last().copied();
        if prev_last.is_none_or(|inst| may_fall_through(vcode.insts[inst])) {
            targets.insert(next);
        }
    }
    targets
}

fn collect_exact_block_groups(
    vcode: &VCode<OpCode>,
    block_order: &[BlockId],
) -> Vec<ExactBlockGroup> {
    let mut groups: FxHashMap<Vec<InstKey>, ExactBlockGroup> = FxHashMap::default();

    for &block in block_order {
        let insts = block_insts(vcode, block);
        let Some(&last) = insts.last() else {
            continue;
        };
        if !is_non_fallthrough_terminal(vcode.insts[last]) {
            continue;
        }

        let Some(region) = analyze_region(vcode, &insts) else {
            continue;
        };
        if region.summary.min_before != 0 {
            continue;
        }

        let entry = groups.entry(region.key).or_insert_with(|| ExactBlockGroup {
            blocks: Vec::new(),
            estimated_size: region.estimated_size,
        });
        entry.blocks.push(block);
    }

    groups.into_values().collect()
}

fn exact_dedup_canonical_block(
    blocks: &[BlockId],
    fallthrough_targets: &FxHashSet<BlockId>,
    entry_block: BlockId,
) -> BlockId {
    blocks
        .iter()
        .copied()
        .find(|&block| block == entry_block)
        .or_else(|| {
            blocks
                .iter()
                .copied()
                .find(|block| fallthrough_targets.contains(block))
        })
        .unwrap_or(blocks[0])
}

impl LateBlockMerge {
    fn new(vcode: &VCode<OpCode>, block_order: &[BlockId]) -> Self {
        let max_block = block_order
            .iter()
            .copied()
            .chain(vcode.blocks.keys())
            .map(|block| block.0)
            .max()
            .map_or(1, |max| max.saturating_add(1));
        Self {
            next_synth_block: max_block,
        }
    }

    fn alloc_synth_block(&mut self) -> BlockId {
        let block = BlockId(self.next_synth_block);
        self.next_synth_block = self
            .next_synth_block
            .checked_add(1)
            .expect("synthetic block id overflow");
        block
    }

    fn run_exact_block_dedup(
        &mut self,
        vcode: &mut VCode<OpCode>,
        block_order: &mut Vec<BlockId>,
        entry_block: BlockId,
    ) -> bool {
        let mut changed = false;
        loop {
            changed |= self.unlock_fallthrough_duplicates(vcode, block_order);

            let fallthrough_targets = layout_fallthrough_targets(vcode, block_order);
            let mut aliases = FxHashMap::default();
            for group in collect_exact_block_groups(vcode, block_order) {
                if group.blocks.len() < 2 {
                    continue;
                }
                let canonical =
                    exact_dedup_canonical_block(&group.blocks, &fallthrough_targets, entry_block);
                for block in group.blocks {
                    if block == canonical {
                        continue;
                    }
                    if block != entry_block && !fallthrough_targets.contains(&block) {
                        aliases.insert(block, canonical);
                    }
                }
            }

            if aliases.is_empty() {
                break;
            }

            rewrite_block_labels(vcode, &aliases);
            block_order.retain(|block| !aliases.contains_key(block));
            changed = true;
        }

        changed
    }

    fn unlock_fallthrough_duplicates(
        &mut self,
        vcode: &mut VCode<OpCode>,
        block_order: &mut Vec<BlockId>,
    ) -> bool {
        let Some(unlock) = self.select_best_fallthrough_unlock(vcode, block_order) else {
            return false;
        };
        self.apply_fallthrough_unlock(vcode, block_order, unlock);
        true
    }

    fn select_best_fallthrough_unlock(
        &self,
        vcode: &VCode<OpCode>,
        block_order: &[BlockId],
    ) -> Option<FallthroughUnlock> {
        let label_targets = referenced_insn_label_targets(vcode);
        let fallthrough_targets = layout_fallthrough_targets(vcode, block_order);
        let order_index: FxHashMap<BlockId, usize> = block_order
            .iter()
            .copied()
            .enumerate()
            .map(|(idx, block)| (block, idx))
            .collect();
        let mut candidates = Vec::new();

        for group in collect_exact_block_groups(vcode, block_order) {
            let fallthrough_count = group
                .blocks
                .iter()
                .filter(|block| fallthrough_targets.contains(block))
                .count();
            if fallthrough_count <= 1 {
                continue;
            }

            for &block in &group.blocks {
                if !fallthrough_targets.contains(&block) {
                    continue;
                }
                if let Some(candidate) = self.analyze_fallthrough_unlock_candidate(
                    vcode,
                    block_order,
                    &label_targets,
                    &order_index,
                    block,
                    group.estimated_size,
                ) {
                    candidates.push(candidate);
                }
            }
        }

        candidates.into_iter().max_by(|a, b| {
            a.savings
                .cmp(&b.savings)
                .then_with(|| a.order_idx.cmp(&b.order_idx))
        })
    }

    fn analyze_fallthrough_unlock_candidate(
        &self,
        vcode: &VCode<OpCode>,
        block_order: &[BlockId],
        label_targets: &FxHashSet<VCodeInst>,
        order_index: &FxHashMap<BlockId, usize>,
        fallthrough: BlockId,
        duplicated_region_size: usize,
    ) -> Option<FallthroughUnlock> {
        let order_idx = order_index[&fallthrough];
        if order_idx == 0 || order_idx + 1 >= block_order.len() {
            return None;
        }

        let pred = block_order[order_idx - 1];
        let other_succ = block_order[order_idx + 1];
        let tail_anchor = block_order.iter().copied().rev().find(|&block| {
            block != fallthrough
                && block_insts(vcode, block)
                    .last()
                    .is_some_and(|&inst| is_non_fallthrough_terminal(vcode.insts[inst]))
        })?;
        let insts = block_insts(vcode, pred);
        if insts.len() < 2 {
            return None;
        }

        let jumpi = *insts.last().expect("checked length");
        let push = insts[insts.len() - 2];
        if !is_plain_inst(vcode, label_targets, jumpi)
            || (vcode.insts[jumpi] as u8) != (OpCode::JUMPI as u8)
            || label_targets.contains(&push)
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
                if !is_plain_inst(vcode, label_targets, inst) {
                    return None;
                }
                true
            }
            _ => false,
        };

        let savings = if has_trailing_iszero {
            isize::try_from(duplicated_region_size).expect("region size overflow") + 1
        } else {
            isize::try_from(duplicated_region_size).expect("region size overflow") - 1
        };
        (savings > 0).then_some(FallthroughUnlock {
            pred,
            fallthrough,
            other_succ,
            tail_anchor,
            push,
            has_trailing_iszero,
            order_idx,
            savings,
        })
    }

    fn apply_fallthrough_unlock(
        &mut self,
        vcode: &mut VCode<OpCode>,
        block_order: &mut Vec<BlockId>,
        unlock: FallthroughUnlock,
    ) {
        debug_assert_eq!(block_order[unlock.order_idx - 1], unlock.pred);
        debug_assert_eq!(block_order[unlock.order_idx], unlock.fallthrough);
        debug_assert_eq!(block_order[unlock.order_idx + 1], unlock.other_succ);

        let insts = block_insts(vcode, unlock.pred);
        let prefix_len = insts.len() - usize::from(unlock.has_trailing_iszero) - 2;
        let mut rebuilt = insts[..prefix_len].to_vec();
        if !unlock.has_trailing_iszero {
            rebuilt.push(create_inst(vcode, OpCode::ISZERO));
        }

        let label = vcode.labels.push(Label::Block(unlock.fallthrough));
        vcode.fixups.insert((unlock.push, VCodeFixup::Label(label)));
        rebuilt.push(unlock.push);
        rebuilt.push(*insts.last().expect("checked by candidate analysis"));
        replace_block_insts(vcode, unlock.pred, &rebuilt);

        let moved = block_order.remove(unlock.order_idx);
        debug_assert_eq!(moved, unlock.fallthrough);
        let anchor_idx = block_order
            .iter()
            .position(|&block| block == unlock.tail_anchor)
            .expect("tail anchor must remain in block order");
        block_order.insert(anchor_idx + 1, moved);
    }

    fn run_common_tail_merge(
        &mut self,
        vcode: &mut VCode<OpCode>,
        block_order: &mut Vec<BlockId>,
        entry_block: BlockId,
    ) -> bool {
        let mut changed = false;
        while let Some(group) = self.select_best_tail_group(vcode, block_order) {
            self.apply_tail_group(vcode, block_order, &group);
            changed = true;
            self.run_exact_block_dedup(vcode, block_order, entry_block);
        }
        changed
    }

    fn select_best_tail_group(
        &self,
        vcode: &VCode<OpCode>,
        block_order: &[BlockId],
    ) -> Option<TailGroup> {
        let order_index: FxHashMap<BlockId, usize> = block_order
            .iter()
            .copied()
            .enumerate()
            .map(|(idx, block)| (block, idx))
            .collect();
        let mut groups: FxHashMap<Vec<InstKey>, TailGroup> = FxHashMap::default();

        for &block in block_order {
            let insts = block_insts(vcode, block);
            let Some(&last) = insts.last() else {
                continue;
            };
            if !is_non_fallthrough_terminal(vcode.insts[last]) || insts.len() < 2 {
                continue;
            }

            for start in 1..insts.len() {
                let prefix = &insts[..start];
                let suffix = &insts[start..];
                let Some(&prefix_last) = prefix.last() else {
                    continue;
                };
                if !may_fall_through(vcode.insts[prefix_last]) {
                    continue;
                }

                let Some(region) = analyze_region(vcode, suffix) else {
                    continue;
                };
                if region.summary.min_before != 0 {
                    continue;
                }

                let entry = groups.entry(region.key).or_insert_with(|| TailGroup {
                    donors: Vec::new(),
                    suffix_len: suffix.len(),
                    suffix_size: region.estimated_size,
                    first_order_idx: order_index[&block],
                    savings: 0,
                });
                entry.donors.push(TailDonor { block, start });
                entry.first_order_idx = entry.first_order_idx.min(order_index[&block]);
            }
        }

        let mut candidates: Vec<_> = groups
            .into_values()
            .filter_map(|mut group| {
                if group.donors.len() < 2 {
                    return None;
                }

                let k = isize::try_from(group.donors.len()).expect("tail donor count overflow");
                let suffix_size =
                    isize::try_from(group.suffix_size).expect("tail suffix size overflow");
                group.savings = (k - 1) * suffix_size - k * 6 - 1;
                (group.savings >= 2).then_some(group)
            })
            .collect();

        candidates.sort_by(|a, b| {
            b.savings
                .cmp(&a.savings)
                .then_with(|| b.suffix_len.cmp(&a.suffix_len))
                .then_with(|| a.first_order_idx.cmp(&b.first_order_idx))
        });

        candidates.into_iter().next()
    }

    fn apply_tail_group(
        &mut self,
        vcode: &mut VCode<OpCode>,
        block_order: &mut Vec<BlockId>,
        group: &TailGroup,
    ) {
        let tail_block = self.alloc_synth_block();
        let canonical_donor = group.donors[0];
        let donor_insts = block_insts(vcode, canonical_donor.block);
        for &inst in donor_insts[canonical_donor.start..].iter() {
            clone_inst(vcode, inst, tail_block);
        }
        block_order.push(tail_block);

        let mut rewritten = FxHashSet::default();
        for donor in &group.donors {
            if !rewritten.insert(donor.block) {
                continue;
            }

            let insts = block_insts(vcode, donor.block);
            let mut rebuilt: Vec<VCodeInst> = insts[..donor.start].to_vec();

            let push = create_inst(vcode, OpCode::PUSH0);
            let label = vcode.labels.push(Label::Block(tail_block));
            vcode.fixups.insert((push, VCodeFixup::Label(label)));
            rebuilt.push(push);

            let jump = create_inst(vcode, OpCode::JUMP);
            rebuilt.push(jump);
            replace_block_insts(vcode, donor.block, &rebuilt);
        }
    }
}

#[cfg(test)]
mod tests {
    use smallvec::smallvec;

    use super::*;

    fn summary_for_ops(ops: &[OpCode]) -> StackSummary {
        ops.iter()
            .copied()
            .fold(StackSummary::default(), |summary, op| {
                compose(summary, opcode_stack_summary(op))
            })
    }

    fn push_imm(vcode: &mut VCode<OpCode>, block: BlockId, bytes: &[u8]) -> VCodeInst {
        let inst = vcode.add_inst_to_block(super::super::push_op(bytes.len()), None, block);
        if !bytes.is_empty() {
            vcode.inst_imm_bytes.insert((inst, bytes.into()));
        }
        inst
    }

    fn push_block(vcode: &mut VCode<OpCode>, block: BlockId, dest: BlockId) -> VCodeInst {
        let inst = vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        let label = vcode.labels.push(Label::Block(dest));
        vcode.fixups.insert((inst, VCodeFixup::Label(label)));
        inst
    }

    fn push_function(vcode: &mut VCode<OpCode>, block: BlockId, dest: FuncRef) -> VCodeInst {
        let inst = vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        let label = vcode.labels.push(Label::Function(dest));
        vcode.fixups.insert((inst, VCodeFixup::Label(label)));
        inst
    }

    fn push_insn(vcode: &mut VCode<OpCode>, block: BlockId, dest: VCodeInst) -> VCodeInst {
        let inst = vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        let label = vcode.labels.push(Label::Insn(dest));
        vcode.fixups.insert((inst, VCodeFixup::Label(label)));
        inst
    }

    fn build_local_pc_suffix_block(vcode: &mut VCode<OpCode>, block: BlockId, prefix: u8) {
        let prefix = push_imm(vcode, block, &[prefix]);
        let push_local = create_inst(vcode, OpCode::PUSH0);
        let jump = create_inst(vcode, OpCode::JUMP);
        let jumpdest = create_inst(vcode, OpCode::JUMPDEST);
        let stop = create_inst(vcode, OpCode::STOP);
        let label = vcode.labels.push(Label::Insn(jumpdest));
        vcode.fixups.insert((push_local, VCodeFixup::Label(label)));
        replace_block_insts(vcode, block, &[prefix, push_local, jump, jumpdest, stop]);
    }

    fn build_adjacent_jumpi(
        vcode: &mut VCode<OpCode>,
        block: BlockId,
        cond: &[OpCode],
        dest: BlockId,
    ) {
        for &op in cond {
            vcode.add_inst_to_block(op, None, block);
        }
        push_block(vcode, block, dest);
        vcode.add_inst_to_block(OpCode::JUMPI, None, block);
    }

    fn build_revert_block(vcode: &mut VCode<OpCode>, block: BlockId) {
        vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        vcode.add_inst_to_block(OpCode::PUSH0, None, block);
        vcode.add_inst_to_block(OpCode::REVERT, None, block);
    }

    fn block_ops(vcode: &VCode<OpCode>, block: BlockId) -> Vec<u8> {
        block_insts(vcode, block)
            .into_iter()
            .map(|inst| vcode.insts[inst] as u8)
            .collect()
    }

    fn block_label_targets(vcode: &VCode<OpCode>, block: BlockId) -> Vec<BlockId> {
        block_insts(vcode, block)
            .into_iter()
            .filter_map(|inst| match vcode.fixups.get(inst) {
                Some((_, VCodeFixup::Label(label))) => match vcode.labels[*label] {
                    Label::Block(block) => Some(block),
                    _ => None,
                },
                _ => None,
            })
            .collect()
    }

    #[test]
    fn push_zero_revert_is_stack_closed() {
        let summary = summary_for_ops(&[OpCode::PUSH0, OpCode::PUSH0, OpCode::REVERT]);
        assert_eq!(
            summary,
            StackSummary {
                min_before: 0,
                delta: 0,
            }
        );
    }

    #[test]
    fn push_function_jump_invalid_is_stack_closed() {
        let summary = summary_for_ops(&[OpCode::PUSH1, OpCode::JUMP, OpCode::INVALID]);
        assert_eq!(
            summary,
            StackSummary {
                min_before: 0,
                delta: 0,
            }
        );
    }

    #[test]
    fn swap_jump_is_not_stack_closed() {
        let summary = summary_for_ops(&[OpCode::SWAP1, OpCode::JUMP]);
        assert_ne!(summary.min_before, 0);
    }

    #[test]
    fn jumpi_may_fall_through() {
        assert!(may_fall_through(OpCode::JUMPI));
    }

    #[test]
    fn identical_block_and_function_fixups_have_equal_keys() {
        let mut vcode = VCode::<OpCode>::default();
        let block0 = BlockId(0);
        let block1 = BlockId(1);
        let func = FuncRef::from_u32(7);

        let a = push_block(&mut vcode, block0, block1);
        let b = push_block(&mut vcode, block0, block1);
        let c = push_function(&mut vcode, block0, func);
        let d = push_function(&mut vcode, block0, func);

        assert_eq!(inst_key(&vcode, a), inst_key(&vcode, b));
        assert_eq!(inst_key(&vcode, c), inst_key(&vcode, d));
    }

    #[test]
    fn region_with_local_insn_label_is_rejected() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);
        let target = vcode.add_inst_to_block(OpCode::JUMPDEST, None, block);
        let push = push_insn(&mut vcode, block, target);
        assert!(analyze_region(&vcode, &[push, target]).is_none());
    }

    #[test]
    fn different_immediates_produce_different_keys() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);
        let a = push_imm(&mut vcode, block, &[0xaa]);
        let b = push_imm(&mut vcode, block, &[0xbb]);

        assert_ne!(inst_key(&vcode, a), inst_key(&vcode, b));
    }

    #[test]
    fn exact_dedup_merges_duplicate_revert_blocks() {
        let mut vcode = VCode::<OpCode>::default();
        let entry = BlockId(0);
        let block1 = BlockId(1);
        let block2 = BlockId(2);
        let block3 = BlockId(3);

        push_block(&mut vcode, entry, block1);
        vcode.add_inst_to_block(OpCode::JUMP, None, entry);

        push_block(&mut vcode, block3, block2);
        vcode.add_inst_to_block(OpCode::JUMP, None, block3);

        for block in [block1, block2] {
            vcode.add_inst_to_block(OpCode::PUSH0, None, block);
            vcode.add_inst_to_block(OpCode::PUSH0, None, block);
            vcode.add_inst_to_block(OpCode::REVERT, None, block);
        }

        let mut block_order = vec![entry, block1, block3, block2];
        assert!(
            LateBlockMerge::new(&vcode, &block_order).run_exact_block_dedup(
                &mut vcode,
                &mut block_order,
                entry
            )
        );
        assert_eq!(block_order, vec![entry, block1]);
        assert_eq!(block_label_targets(&vcode, block3), vec![block1]);
    }

    #[test]
    fn exact_dedup_prefers_fallthrough_block_as_canonical() {
        let mut vcode = VCode::<OpCode>::default();
        let entry = BlockId(0);
        let block1 = BlockId(1);
        let block2 = BlockId(2);
        let block3 = BlockId(3);
        let block4 = BlockId(4);

        push_block(&mut vcode, entry, block1);
        vcode.add_inst_to_block(OpCode::JUMP, None, entry);

        build_adjacent_jumpi(&mut vcode, block2, &[OpCode::PUSH0], block4);
        vcode.add_inst_to_block(OpCode::STOP, None, block4);

        build_revert_block(&mut vcode, block1);
        build_revert_block(&mut vcode, block3);

        let mut block_order = vec![entry, block1, block2, block3, block4];
        assert!(
            LateBlockMerge::new(&vcode, &block_order).run_exact_block_dedup(
                &mut vcode,
                &mut block_order,
                entry
            )
        );
        assert_eq!(block_order, vec![entry, block2, block3, block4]);
        assert_eq!(block_label_targets(&vcode, entry), vec![block3]);
    }

    #[test]
    fn exact_dedup_skips_fallthrough_target() {
        let mut vcode = VCode::<OpCode>::default();
        let entry = BlockId(0);
        let block1 = BlockId(1);
        let block2 = BlockId(2);
        let block3 = BlockId(3);

        vcode.add_inst_to_block(OpCode::PUSH0, None, entry);

        push_block(&mut vcode, block3, block2);
        vcode.add_inst_to_block(OpCode::JUMP, None, block3);

        for block in [block1, block2] {
            vcode.add_inst_to_block(OpCode::PUSH0, None, block);
            vcode.add_inst_to_block(OpCode::PUSH0, None, block);
            vcode.add_inst_to_block(OpCode::REVERT, None, block);
        }

        let mut block_order = vec![entry, block1, block3, block2];
        assert!(
            LateBlockMerge::new(&vcode, &block_order).run_exact_block_dedup(
                &mut vcode,
                &mut block_order,
                entry
            )
        );
        assert!(block_order.contains(&block1));
        assert!(!block_order.contains(&block2));
        assert_eq!(block_label_targets(&vcode, block3), vec![block1]);
    }

    #[test]
    fn exact_dedup_unlocks_fallthrough_duplicate_by_adding_iszero() {
        let mut vcode = VCode::<OpCode>::default();
        let entry = BlockId(0);
        let block1 = BlockId(1);
        let block2 = BlockId(2);
        let block3 = BlockId(3);
        let block4 = BlockId(4);

        build_adjacent_jumpi(&mut vcode, entry, &[OpCode::PUSH0], block2);
        vcode.add_inst_to_block(OpCode::STOP, None, block2);
        build_adjacent_jumpi(&mut vcode, block3, &[OpCode::PUSH0], block2);

        build_revert_block(&mut vcode, block1);
        build_revert_block(&mut vcode, block4);

        let mut block_order = vec![entry, block1, block2, block3, block4];
        assert!(
            LateBlockMerge::new(&vcode, &block_order).run_exact_block_dedup(
                &mut vcode,
                &mut block_order,
                entry
            )
        );
        assert_eq!(block_order, vec![entry, block2, block3, block4]);
        assert_eq!(
            block_ops(&vcode, entry),
            vec![
                OpCode::PUSH0 as u8,
                OpCode::ISZERO as u8,
                OpCode::PUSH0 as u8,
                OpCode::JUMPI as u8
            ]
        );
        assert_eq!(block_label_targets(&vcode, entry), vec![block4]);
    }

    #[test]
    fn exact_dedup_unlocks_fallthrough_duplicate_by_removing_iszero() {
        let mut vcode = VCode::<OpCode>::default();
        let entry = BlockId(0);
        let block1 = BlockId(1);
        let block2 = BlockId(2);
        let block3 = BlockId(3);
        let block4 = BlockId(4);

        build_adjacent_jumpi(&mut vcode, entry, &[OpCode::PUSH0, OpCode::ISZERO], block2);
        vcode.add_inst_to_block(OpCode::STOP, None, block2);
        build_adjacent_jumpi(&mut vcode, block3, &[OpCode::PUSH0], block2);

        build_revert_block(&mut vcode, block1);
        build_revert_block(&mut vcode, block4);

        let mut block_order = vec![entry, block1, block2, block3, block4];
        assert!(
            LateBlockMerge::new(&vcode, &block_order).run_exact_block_dedup(
                &mut vcode,
                &mut block_order,
                entry
            )
        );
        assert_eq!(block_order, vec![entry, block2, block3, block4]);
        assert_eq!(
            block_ops(&vcode, entry),
            vec![
                OpCode::PUSH0 as u8,
                OpCode::PUSH0 as u8,
                OpCode::JUMPI as u8
            ]
        );
        assert_eq!(block_label_targets(&vcode, entry), vec![block4]);
    }

    #[test]
    fn exact_dedup_unlocks_fallthrough_duplicate_by_moving_stub_to_tail_anchor() {
        let mut vcode = VCode::<OpCode>::default();
        let entry = BlockId(0);
        let block1 = BlockId(1);
        let block2 = BlockId(2);
        let block3 = BlockId(3);
        let block4 = BlockId(4);

        build_adjacent_jumpi(&mut vcode, entry, &[OpCode::PUSH0], block2);
        vcode.add_inst_to_block(OpCode::PUSH0, None, block2);
        build_adjacent_jumpi(&mut vcode, block3, &[OpCode::PUSH0], block2);

        build_revert_block(&mut vcode, block1);
        build_revert_block(&mut vcode, block4);

        let mut block_order = vec![entry, block1, block2, block3, block4];
        assert!(
            LateBlockMerge::new(&vcode, &block_order).run_exact_block_dedup(
                &mut vcode,
                &mut block_order,
                entry
            )
        );
        assert_eq!(block_order, vec![entry, block2, block3, block4]);
        assert_eq!(
            block_ops(&vcode, entry),
            vec![
                OpCode::PUSH0 as u8,
                OpCode::ISZERO as u8,
                OpCode::PUSH0 as u8,
                OpCode::JUMPI as u8
            ]
        );
        assert_eq!(block_label_targets(&vcode, entry), vec![block4]);
    }

    #[test]
    fn exact_dedup_keeps_entry_block_as_canonical() {
        let mut vcode = VCode::<OpCode>::default();
        let entry = BlockId(0);
        let block1 = BlockId(1);

        for block in [entry, block1] {
            vcode.add_inst_to_block(OpCode::PUSH0, None, block);
            vcode.add_inst_to_block(OpCode::PUSH0, None, block);
            vcode.add_inst_to_block(OpCode::REVERT, None, block);
        }

        let mut block_order = vec![entry, block1];
        assert!(
            LateBlockMerge::new(&vcode, &block_order).run_exact_block_dedup(
                &mut vcode,
                &mut block_order,
                entry
            )
        );
        assert_eq!(block_order, vec![entry]);
    }

    #[test]
    fn tail_merge_extracts_shared_revert_suffix() {
        let mut vcode = VCode::<OpCode>::default();
        let block1 = BlockId(1);
        let block2 = BlockId(2);

        push_imm(&mut vcode, block1, &[0xaa]);
        for byte in [0x11, 0x22, 0x33, 0x44, 0x55, 0x66] {
            push_imm(&mut vcode, block1, &[byte]);
        }
        vcode.add_inst_to_block(OpCode::PUSH0, None, block1);
        vcode.add_inst_to_block(OpCode::PUSH0, None, block1);
        vcode.add_inst_to_block(OpCode::REVERT, None, block1);

        push_imm(&mut vcode, block2, &[0xbb]);
        for byte in [0x11, 0x22, 0x33, 0x44, 0x55, 0x66] {
            push_imm(&mut vcode, block2, &[byte]);
        }
        vcode.add_inst_to_block(OpCode::PUSH0, None, block2);
        vcode.add_inst_to_block(OpCode::PUSH0, None, block2);
        vcode.add_inst_to_block(OpCode::REVERT, None, block2);

        let mut block_order = vec![block1, block2];
        let block1_insts = block_insts(&vcode, block1);
        let block2_insts = block_insts(&vcode, block2);
        let block1_region = analyze_region(&vcode, &block1_insts[1..]).expect("block1 suffix");
        let block2_region = analyze_region(&vcode, &block2_insts[1..]).expect("block2 suffix");
        assert_eq!(block1_region.summary.min_before, 0);
        assert_eq!(block1_region.estimated_size, 15);
        assert_eq!(block1_region.key, block2_region.key);
        assert!(
            LateBlockMerge::new(&vcode, &block_order)
                .select_best_tail_group(&vcode, &block_order)
                .is_some()
        );
        assert!(run_late_block_merge(
            &mut vcode,
            &mut block_order,
            block1,
            LateCleanupProfile::Size
        ));

        let tail = *block_order
            .last()
            .expect("expected synthetic tail block in block order");
        assert!(tail.0 > block2.0);
        assert_eq!(
            block_ops(&vcode, block1),
            vec![OpCode::PUSH1 as u8, OpCode::PUSH0 as u8, OpCode::JUMP as u8]
        );
        assert_eq!(
            block_ops(&vcode, block2),
            vec![OpCode::PUSH1 as u8, OpCode::PUSH0 as u8, OpCode::JUMP as u8]
        );
        assert_eq!(block_label_targets(&vcode, block1), vec![tail]);
        assert_eq!(block_label_targets(&vcode, block2), vec![tail]);
        assert_eq!(
            block_ops(&vcode, tail),
            vec![
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH0 as u8,
                OpCode::PUSH0 as u8,
                OpCode::REVERT as u8
            ]
        );
    }

    #[test]
    fn tail_merge_skips_local_pc_label_suffix() {
        let mut vcode = VCode::<OpCode>::default();
        let block1 = BlockId(1);
        let block2 = BlockId(2);

        build_local_pc_suffix_block(&mut vcode, block1, 0xaa);
        build_local_pc_suffix_block(&mut vcode, block2, 0xbb);

        let before = block_order_snapshot(&vcode, &[block1, block2]);
        let mut block_order = vec![block1, block2];
        assert!(
            !LateBlockMerge::new(&vcode, &block_order).run_common_tail_merge(
                &mut vcode,
                &mut block_order,
                block1
            )
        );
        assert_eq!(before, block_order_snapshot(&vcode, &block_order));
    }

    #[test]
    fn tail_merge_skips_open_suffix() {
        let mut vcode = VCode::<OpCode>::default();
        let block1 = BlockId(1);
        let block2 = BlockId(2);

        push_imm(&mut vcode, block1, &[0xaa]);
        vcode.add_inst_to_block(OpCode::SWAP1, None, block1);
        vcode.add_inst_to_block(OpCode::JUMP, None, block1);

        push_imm(&mut vcode, block2, &[0xbb]);
        vcode.add_inst_to_block(OpCode::SWAP1, None, block2);
        vcode.add_inst_to_block(OpCode::JUMP, None, block2);

        let before = block_order_snapshot(&vcode, &[block1, block2]);
        let mut block_order = vec![block1, block2];
        assert!(
            !LateBlockMerge::new(&vcode, &block_order).run_common_tail_merge(
                &mut vcode,
                &mut block_order,
                block1
            )
        );
        assert_eq!(before, block_order_snapshot(&vcode, &block_order));
    }

    #[test]
    fn speed_mode_runs_exact_dedup_but_not_tail_merge() {
        let mut vcode = VCode::<OpCode>::default();
        let entry = BlockId(0);
        let block1 = BlockId(1);
        let block2 = BlockId(2);
        let block3 = BlockId(3);
        let block4 = BlockId(4);
        let block5 = BlockId(5);
        let block6 = BlockId(6);

        push_block(&mut vcode, entry, block1);
        vcode.add_inst_to_block(OpCode::JUMP, None, entry);

        push_imm(&mut vcode, block1, &[0xaa]);
        for byte in [0x11, 0x22, 0x33, 0x44, 0x55, 0x66] {
            push_imm(&mut vcode, block1, &[byte]);
        }
        vcode.add_inst_to_block(OpCode::PUSH0, None, block1);
        vcode.add_inst_to_block(OpCode::PUSH0, None, block1);
        vcode.add_inst_to_block(OpCode::REVERT, None, block1);

        push_imm(&mut vcode, block2, &[0xbb]);
        for byte in [0x11, 0x22, 0x33, 0x44, 0x55, 0x66] {
            push_imm(&mut vcode, block2, &[byte]);
        }
        vcode.add_inst_to_block(OpCode::PUSH0, None, block2);
        vcode.add_inst_to_block(OpCode::PUSH0, None, block2);
        vcode.add_inst_to_block(OpCode::REVERT, None, block2);

        push_block(&mut vcode, block5, block3);
        vcode.add_inst_to_block(OpCode::JUMP, None, block5);
        push_block(&mut vcode, block6, block4);
        vcode.add_inst_to_block(OpCode::JUMP, None, block6);

        for block in [block3, block4] {
            vcode.add_inst_to_block(OpCode::PUSH0, None, block);
            vcode.add_inst_to_block(OpCode::PUSH0, None, block);
            vcode.add_inst_to_block(OpCode::REVERT, None, block);
        }

        let mut block_order = vec![entry, block1, block2, block5, block3, block6, block4];
        assert!(run_late_block_merge(
            &mut vcode,
            &mut block_order,
            entry,
            LateCleanupProfile::Speed
        ));

        assert!(!block_order.iter().any(|block| block.0 > block6.0));
        assert!(block_order.contains(&block1));
        assert!(block_order.contains(&block2));
        assert!(block_order.contains(&block3));
        assert!(!block_order.contains(&block4));
        assert_eq!(
            block_ops(&vcode, block1),
            vec![
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH0 as u8,
                OpCode::PUSH0 as u8,
                OpCode::REVERT as u8
            ]
        );
        assert_eq!(
            block_ops(&vcode, block2),
            vec![
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH1 as u8,
                OpCode::PUSH0 as u8,
                OpCode::PUSH0 as u8,
                OpCode::REVERT as u8
            ]
        );
    }

    fn block_order_snapshot(vcode: &VCode<OpCode>, block_order: &[BlockId]) -> Vec<Vec<u8>> {
        block_order
            .iter()
            .copied()
            .map(|block| block_ops(vcode, block))
            .collect()
    }

    #[test]
    fn label_fixup_estimate_uses_conservative_width() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);
        let push = push_block(&mut vcode, block, BlockId(1));
        assert_eq!(inst_estimated_size(&vcode, push), 5);
        let imm = push_imm(&mut vcode, block, &[0xaa, 0xbb]);
        assert_eq!(inst_estimated_size(&vcode, imm), 3);
    }

    #[test]
    fn function_fixup_key_ignores_label_id_identity() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);
        let func = FuncRef::from_u32(9);
        let first = push_function(&mut vcode, block, func);
        let second = push_function(&mut vcode, block, func);
        assert_eq!(inst_key(&vcode, first), inst_key(&vcode, second));
    }

    #[test]
    fn imm_key_captures_payload_bytes() {
        let mut vcode = VCode::<OpCode>::default();
        let block = BlockId(0);
        let inst = push_imm(&mut vcode, block, &[0x01, 0x02, 0x03]);
        assert_eq!(
            inst_key(&vcode, inst),
            Some(InstKey {
                opcode: OpCode::PUSH3 as u8,
                imm: smallvec![0x01, 0x02, 0x03],
                fixup: FixupKey::None,
            })
        );
    }
}
