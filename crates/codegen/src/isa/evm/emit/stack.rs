use cranelift_entity::EntityList;
use rustc_hash::FxHashSet;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{BlockId, Immediate, Type, U256};

use crate::{
    machinst::{
        lower::Lower,
        vcode::{Label, VCode, VCodeFixup, VCodeInst},
    },
    stackalloc::Action,
};

use super::super::{DYN_SP_SLOT, FREE_PTR_SLOT, OpCode, WORD_BYTES};

pub(crate) fn is_push_opcode(op: OpCode) -> bool {
    let byte = op as u8;
    byte == OpCode::PUSH0 as u8 || (OpCode::PUSH1 as u8..=OpCode::PUSH32 as u8).contains(&byte)
}

#[derive(Clone, Copy)]
enum StackPeepholeOp {
    Push,
    Dup(u8),
    Swap(u8),
    Pop,
}

fn classify_stack_peephole_op(
    vcode: &VCode<OpCode>,
    label_targets: &FxHashSet<VCodeInst>,
    inst: VCodeInst,
) -> Option<StackPeepholeOp> {
    if label_targets.contains(&inst) || vcode.fixups.get(inst).is_some() {
        return None;
    }
    let op = vcode.insts[inst];
    if is_push_opcode(op) {
        if (op as u8) == (OpCode::PUSH0 as u8) {
            if vcode.inst_imm_bytes.get(inst).is_none() {
                return Some(StackPeepholeOp::Push);
            }
            return None;
        }
        if vcode.inst_imm_bytes.get(inst).is_some() {
            return Some(StackPeepholeOp::Push);
        }
        return None;
    }
    if vcode.inst_imm_bytes.get(inst).is_some() {
        return None;
    }
    let byte = op as u8;
    if byte == OpCode::POP as u8 {
        return Some(StackPeepholeOp::Pop);
    }
    if (OpCode::DUP1 as u8..=OpCode::DUP16 as u8).contains(&byte) {
        return Some(StackPeepholeOp::Dup(byte - OpCode::DUP1 as u8 + 1));
    }
    if (OpCode::SWAP1 as u8..=OpCode::SWAP16 as u8).contains(&byte) {
        return Some(StackPeepholeOp::Swap(byte - OpCode::SWAP1 as u8 + 1));
    }
    None
}

fn is_bool_producer_opcode(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::LT
            | OpCode::GT
            | OpCode::SLT
            | OpCode::SGT
            | OpCode::EQ
            | OpCode::ISZERO
            | OpCode::CALL
            | OpCode::CALLCODE
            | OpCode::DELEGATECALL
            | OpCode::STATICCALL
    )
}

pub(crate) fn is_plain_inst(
    vcode: &VCode<OpCode>,
    label_targets: &FxHashSet<VCodeInst>,
    inst: VCodeInst,
) -> bool {
    !label_targets.contains(&inst)
        && vcode.fixups.get(inst).is_none()
        && vcode.inst_imm_bytes.get(inst).is_none()
}

fn push_immediate_u256(vcode: &VCode<OpCode>, inst: VCodeInst) -> Option<U256> {
    let op = vcode.insts[inst];
    if (op as u8) == (OpCode::PUSH0 as u8) {
        return Some(U256::zero());
    }
    if !is_push_opcode(op) || vcode.fixups.get(inst).is_some() {
        return None;
    }

    let (_, bytes) = vcode.inst_imm_bytes.get(inst)?;
    let mut be = [0u8; 32];
    be[32 - bytes.len()..].copy_from_slice(bytes);
    Some(U256::from_big_endian(&be))
}

fn is_noop_stack_peephole_sequence(
    vcode: &VCode<OpCode>,
    label_targets: &FxHashSet<VCodeInst>,
    insts: &[VCodeInst],
) -> bool {
    let mut stack: SmallVec<[u16; 64]> = (0..32).collect();
    let initial = stack.clone();
    let mut next_push_token: u16 = 1000;

    for &inst in insts {
        let Some(op) = classify_stack_peephole_op(vcode, label_targets, inst) else {
            return false;
        };
        match op {
            StackPeepholeOp::Push => {
                stack.push(next_push_token);
                next_push_token = next_push_token.wrapping_add(1);
            }
            StackPeepholeOp::Dup(depth) => {
                let depth = depth as usize;
                let len = stack.len();
                if len < depth {
                    return false;
                }
                let value = stack[len - depth];
                stack.push(value);
            }
            StackPeepholeOp::Swap(depth) => {
                let depth = depth as usize;
                let len = stack.len();
                if len <= depth {
                    return false;
                }
                stack.swap(len - 1, len - 1 - depth);
            }
            StackPeepholeOp::Pop => {
                if stack.pop().is_none() {
                    return false;
                }
            }
        }
    }

    stack == initial
}

pub(crate) fn prune_redundant_opcode_sequences(vcode: &mut VCode<OpCode>, block_order: &[BlockId]) {
    let label_targets = super::layout::referenced_insn_label_targets(vcode);

    for block in block_order.iter().copied() {
        let insts: Vec<VCodeInst> = vcode.block_insns(block).collect();
        if insts.len() < 3 {
            continue;
        }

        let mut kept: Vec<VCodeInst> = Vec::with_capacity(insts.len());
        let mut changed = false;
        let mut i = 0usize;
        while i < insts.len() {
            if i + 1 < insts.len() {
                let push = insts[i];
                let eq = insts[i + 1];
                if !label_targets.contains(&push)
                    && push_immediate_u256(vcode, push) == Some(U256::zero())
                    && is_plain_inst(vcode, &label_targets, eq)
                    && (vcode.insts[eq] as u8) == (OpCode::EQ as u8)
                {
                    vcode.insts[eq] = OpCode::ISZERO;
                    kept.push(eq);
                    changed = true;
                    i += 2;
                    continue;
                }
            }

            if i + 3 < insts.len() {
                let z0 = insts[i];
                let z1 = insts[i + 1];
                let push = insts[i + 2];
                let jumpi = insts[i + 3];
                if is_plain_inst(vcode, &label_targets, z0)
                    && is_plain_inst(vcode, &label_targets, z1)
                    && is_plain_inst(vcode, &label_targets, jumpi)
                    && (vcode.insts[z0] as u8) == (OpCode::ISZERO as u8)
                    && (vcode.insts[z1] as u8) == (OpCode::ISZERO as u8)
                    && is_push_opcode(vcode.insts[push])
                    && matches!(vcode.fixups.get(push), Some((_, VCodeFixup::Label(_))))
                    && (vcode.insts[jumpi] as u8) == (OpCode::JUMPI as u8)
                {
                    kept.push(push);
                    kept.push(jumpi);
                    changed = true;
                    i += 4;
                    continue;
                }
            }

            if i + 2 < insts.len() {
                let inst = insts[i];
                let push = insts[i + 1];
                let and = insts[i + 2];
                if is_plain_inst(vcode, &label_targets, inst)
                    && is_plain_inst(vcode, &label_targets, and)
                    && is_bool_producer_opcode(vcode.insts[inst])
                    && (vcode.insts[and] as u8) == (OpCode::AND as u8)
                    && push_immediate_u256(vcode, push) == Some(U256::one())
                {
                    kept.push(inst);
                    changed = true;
                    i += 3;
                    continue;
                }
            }

            if i + 2 < insts.len() {
                let inst = insts[i];
                if is_plain_inst(vcode, &label_targets, inst) {
                    let op = vcode.insts[inst];
                    if is_bool_producer_opcode(op) {
                        let mut j = i + 1;
                        while j < insts.len() {
                            let z = insts[j];
                            if label_targets.contains(&z)
                                || vcode.fixups.get(z).is_some()
                                || vcode.inst_imm_bytes.get(z).is_some()
                                || (vcode.insts[z] as u8) != (OpCode::ISZERO as u8)
                            {
                                break;
                            }
                            j += 1;
                        }

                        let run = j - (i + 1);
                        if run >= 2 {
                            kept.push(inst);
                            if run % 2 == 1 {
                                kept.push(insts[i + 1]);
                            }
                            changed = true;
                            i = j;
                            continue;
                        }
                    }
                }
            }

            const MAX_WINDOW: usize = 24;
            let run_limit = (i + MAX_WINDOW).min(insts.len());
            let mut run_end = i;
            while run_end < run_limit
                && classify_stack_peephole_op(vcode, &label_targets, insts[run_end]).is_some()
            {
                run_end += 1;
            }

            let mut removed = false;
            if run_end >= i + 3 {
                for end in (i + 3..=run_end).rev() {
                    if is_noop_stack_peephole_sequence(vcode, &label_targets, &insts[i..end]) {
                        changed = true;
                        removed = true;
                        i = end;
                        break;
                    }
                }
            }
            if removed {
                continue;
            }

            kept.push(insts[i]);
            i += 1;
        }

        if changed {
            let mut list: EntityList<VCodeInst> = Default::default();
            for inst in kept {
                list.push(inst, &mut vcode.insts_pool);
            }
            vcode.blocks[block] = list;
        }
    }
}

pub(crate) fn immediate_u32(imm: Immediate) -> Option<u32> {
    if imm.is_negative() {
        return None;
    }

    let u256 = imm.as_i256().to_u256();
    if u256 > U256::from(u32::MAX) {
        return None;
    }

    Some(u256.low_u32())
}

pub(crate) fn fold_stack_actions(actions: &[Action]) -> SmallVec<[Action; 8]> {
    let mut out: SmallVec<[Action; 8]> = SmallVec::new();
    for &action in actions {
        out.push(action);
        loop {
            let len = out.len();

            let mut changed = false;
            if len >= 2 {
                let prev = out[len - 2];
                let last = out[len - 1];
                let cancels = match (prev, last) {
                    (Action::StackSwap(a), Action::StackSwap(b)) => a == b,
                    (Action::StackDup(_), Action::Pop) | (Action::Push(_), Action::Pop) => true,
                    _ => false,
                };
                if cancels {
                    out.truncate(len - 2);
                    changed = true;
                }
            }

            if !changed && len >= 3 {
                let a = out[len - 3];
                let b = out[len - 2];
                let c = out[len - 1];
                if matches!(a, Action::Push(_)) && b == Action::StackSwap(1) && c == Action::Pop {
                    out.truncate(len - 3);
                    changed = true;
                }
            }

            if !changed && len >= 8 {
                let i = len - 8;
                if matches!(out[i], Action::Push(_))
                    && matches!(out[i + 1], Action::Push(_))
                    && out[i + 2] == Action::StackSwap(1)
                    && out[i + 3] == Action::StackSwap(2)
                    && out[i + 4] == Action::StackSwap(1)
                    && out[i + 5] == Action::Pop
                    && out[i + 6] == Action::StackSwap(1)
                    && out[i + 7] == Action::Pop
                {
                    out.truncate(len - 8);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }
    }
    out
}

pub(crate) fn frame_slot_sp_relative_bytes(frame_size_slots: u32, offset_words: u32) -> u32 {
    let sp_relative_words = frame_size_slots
        .checked_sub(offset_words)
        .filter(|words| *words != 0)
        .unwrap_or_else(|| {
            panic!(
                "frame slot offset {} out of range for frame size {}",
                offset_words, frame_size_slots
            )
        });
    sp_relative_words
        .checked_mul(WORD_BYTES)
        .expect("frame slot byte offset overflow")
}

pub(crate) fn emit_dyn_frame_addr(
    ctx: &mut Lower<OpCode>,
    frame_size_slots: u32,
    offset_words: u32,
) {
    let sp_relative_bytes = frame_slot_sp_relative_bytes(frame_size_slots, offset_words);
    push_bytes(ctx, &u32_to_be(sp_relative_bytes));
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MLOAD);
    ctx.push(OpCode::SUB);
}

pub(crate) fn perform_action(ctx: &mut Lower<OpCode>, action: Action, frame_size_slots: u32) {
    match action {
        Action::StackDup(slot) => {
            debug_assert!(slot < 16, "DUP out of range: {slot}");
            ctx.push(dup_op(slot));
        }
        Action::StackSwap(n) => {
            debug_assert!((1..=16).contains(&n), "SWAP out of range: {n}");
            ctx.push(swap_op(n));
        }
        Action::Push(imm) => {
            if imm.is_zero() {
                ctx.push(OpCode::PUSH0);
            } else {
                let bytes = match imm {
                    Immediate::I1(v) => smallvec![v as u8],
                    Immediate::I8(v) => SmallVec::from_slice(&v.to_be_bytes()),
                    Immediate::I16(v) => shrink_bytes(&v.to_be_bytes()),
                    Immediate::I32(v) => shrink_bytes(&v.to_be_bytes()),
                    Immediate::I64(v) => shrink_bytes(&v.to_be_bytes()),
                    Immediate::I128(v) => shrink_bytes(&v.to_be_bytes()),
                    Immediate::I256(v) => shrink_bytes(&v.to_u256().to_big_endian()),
                    Immediate::EnumTag { value, .. } => {
                        shrink_bytes(&value.to_u256().to_big_endian())
                    }
                };
                push_bytes(ctx, &bytes);
                if imm.is_negative() && bytes.len() < 32 {
                    push_bytes(ctx, &u32_to_be((bytes.len() - 1) as u32));
                    ctx.push(OpCode::SIGNEXTEND);
                }
            }
        }
        Action::Pop => {
            ctx.push(OpCode::POP);
        }
        Action::MemLoadAbs(offset) => {
            push_bytes(ctx, &u32_to_be(offset));
            ctx.push(OpCode::MLOAD);
        }
        Action::MemLoadFrameSlot(offset) => {
            emit_dyn_frame_addr(ctx, frame_size_slots, offset);
            ctx.push(OpCode::MLOAD);
        }
        Action::MemStoreAbs(offset) => {
            push_bytes(ctx, &u32_to_be(offset));
            ctx.push(OpCode::MSTORE);
        }
        Action::MemStoreFrameSlot(offset) => {
            emit_dyn_frame_addr(ctx, frame_size_slots, offset);
            ctx.push(OpCode::MSTORE);
        }
        Action::MemLoadObj(_) | Action::MemStoreObj(_) => {
            panic!("unlowered Mem*Obj action");
        }
        Action::PushContinuationOffset => {
            panic!("handle PushContinuationOffset elsewhere");
        }
    }
}

pub(crate) fn perform_actions(ctx: &mut Lower<OpCode>, actions: &[Action], frame_size_slots: u32) {
    let folded = fold_stack_actions(actions);
    for action in folded {
        perform_action(ctx, action, frame_size_slots);
    }
}

pub(crate) fn push_bytes(ctx: &mut Lower<OpCode>, bytes: &[u8]) {
    assert!(!bytes.is_empty());
    if bytes == [0] {
        ctx.push(OpCode::PUSH0);
    } else {
        ctx.push_with_imm(push_op(bytes.len()), bytes);
    }
}

fn shrink_bytes(bytes: &[u8]) -> SmallVec<[u8; 8]> {
    assert!(!bytes.is_empty());

    let is_neg = bytes[0].leading_ones() > 0;
    let skip = if is_neg { 0xff } else { 0x00 };
    let mut bytes = bytes
        .iter()
        .copied()
        .skip_while(|b| *b == skip)
        .collect::<SmallVec<[u8; 8]>>();

    if is_neg && bytes.first().map(|&b| b < 0x80).unwrap_or(true) {
        bytes.insert(0, 0xff);
    }
    bytes
}

pub(crate) fn u32_to_be(num: u32) -> SmallVec<[u8; 4]> {
    if num == 0 {
        smallvec![0]
    } else {
        num.to_be_bytes()
            .into_iter()
            .skip_while(|b| *b == 0)
            .collect()
    }
}

pub(crate) fn u256_to_be(num: &U256) -> SmallVec<[u8; 8]> {
    if num.is_zero() {
        smallvec![0]
    } else {
        let b = num.to_big_endian();
        b.into_iter().skip_while(|b| *b == 0).collect()
    }
}

pub(crate) fn scalar_bit_width(ty: Type, module: &sonatina_ir::module::ModuleCtx) -> Option<u16> {
    let bits = match ty {
        Type::I1 => 1,
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        Type::I128 => 128,
        Type::I256 => 256,
        Type::EnumTag(_) => return None,
        Type::Unit => 0,
        Type::Compound(_) if ty.is_pointer(module) => 256,
        Type::Compound(_) => return None,
    };
    Some(bits)
}

pub(crate) fn low_bits_mask(bits: u16) -> Option<U256> {
    if bits >= 256 {
        None
    } else if bits == 0 {
        Some(U256::zero())
    } else {
        Some((U256::one() << (bits as usize)) - U256::one())
    }
}

fn emit_signextend_top(ctx: &mut Lower<OpCode>, bits: u16) {
    debug_assert!((8..256).contains(&bits) && bits.is_multiple_of(8));
    push_bytes(ctx, &[((bits / 8) - 1) as u8]);
    ctx.push(OpCode::SIGNEXTEND);
}

fn emit_signextend_top_two_operands(ctx: &mut Lower<OpCode>, bits: u16) {
    emit_signextend_top(ctx, bits);
    ctx.push(OpCode::SWAP1);
    emit_signextend_top(ctx, bits);
    ctx.push(OpCode::SWAP1);
}

pub(crate) fn emit_narrow_unsigned_saturating_binary(
    ctx: &mut Lower<OpCode>,
    op: OpCode,
    bits: u16,
    saturated: U256,
) {
    debug_assert!((8..256).contains(&bits));
    let mask = low_bits_mask(bits).unwrap();
    let limit = U256::one() << (bits as usize);

    push_bytes(ctx, &u256_to_be(&mask));
    ctx.push(OpCode::AND);
    ctx.push(OpCode::SWAP1);
    push_bytes(ctx, &u256_to_be(&mask));
    ctx.push(OpCode::AND);
    ctx.push(OpCode::SWAP1);

    ctx.push(op);
    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &u256_to_be(&limit));
    ctx.push(OpCode::SWAP1);
    ctx.push(OpCode::LT);

    let keep_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    ctx.push(OpCode::POP);
    push_bytes(ctx, &u256_to_be(&saturated));

    let keep = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(keep_push, Label::Insn(keep));
}

pub(crate) fn emit_narrow_signed_saturating_binary(ctx: &mut Lower<OpCode>, op: OpCode, bits: u16) {
    debug_assert!((8..256).contains(&bits) && bits.is_multiple_of(8));
    let limit = U256::one() << (bits as usize);
    let sign = U256::one() << ((bits - 1) as usize);
    let smax = sign - U256::one();

    emit_signextend_top_two_operands(ctx, bits);
    ctx.push(op);
    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &u256_to_be(&sign));
    ctx.push(OpCode::ADD);
    push_bytes(ctx, &u256_to_be(&limit));
    ctx.push(OpCode::SWAP1);
    ctx.push(OpCode::LT);

    let keep_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &[0xff]);
    ctx.push(OpCode::SAR);
    push_bytes(ctx, &u256_to_be(&smax));
    ctx.push(OpCode::XOR);
    ctx.push(OpCode::SWAP1);
    ctx.push(OpCode::POP);

    let keep = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(keep_push, Label::Insn(keep));
}

fn emit_max_top_two(ctx: &mut Lower<OpCode>) {
    ctx.push(OpCode::DUP2);
    ctx.push(OpCode::DUP2);
    ctx.push(OpCode::LT);

    let keep_b_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);
    ctx.push(OpCode::SWAP1);

    let keep_b = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(keep_b_push, Label::Insn(keep_b));
    ctx.push(OpCode::POP);
}

fn emit_max_top_with_const(ctx: &mut Lower<OpCode>, constant: &[u8]) {
    let constant = U256::from_big_endian(constant);
    if constant.is_zero() {
        return;
    }

    let compare_const = u256_to_be(&(constant - U256::from(1_u8)));
    push_bytes(ctx, &compare_const);
    ctx.push(OpCode::DUP2);
    ctx.push(OpCode::GT);

    let keep_x_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    ctx.push(OpCode::POP);
    push_bytes(ctx, &u256_to_be(&constant));

    let keep_x = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(keep_x_push, Label::Insn(keep_x));
}

pub(crate) fn emit_malloc_base(
    ctx: &mut Lower<OpCode>,
    min_base_bytes: u32,
    needs_dyn_sp_clamp: bool,
) {
    push_bytes(ctx, &[FREE_PTR_SLOT]);
    ctx.push(OpCode::MLOAD);

    if needs_dyn_sp_clamp {
        push_bytes(ctx, &[DYN_SP_SLOT]);
        ctx.push(OpCode::MLOAD);
        emit_max_top_two(ctx);
    }

    let min_base = u32_to_be(min_base_bytes);
    emit_max_top_with_const(ctx, &min_base);
}

pub(crate) fn init_dyn_sp(ctx: &mut Lower<OpCode>, dyn_base: u32) {
    push_bytes(ctx, &u32_to_be(dyn_base));
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);
}

pub(crate) fn ensure_dyn_sp_init(ctx: &mut Lower<OpCode>, dyn_base: u32) {
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MLOAD);
    ctx.push(OpCode::DUP1);

    let skip_init_push = ctx.push(OpCode::PUSH1);
    ctx.push(OpCode::JUMPI);

    ctx.push(OpCode::POP);
    push_bytes(ctx, &u32_to_be(dyn_base));
    ctx.push(OpCode::DUP1);
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);

    let skip_init = ctx.push(OpCode::JUMPDEST);
    ctx.add_label_reference(skip_init_push, Label::Insn(skip_init));
    ctx.push(OpCode::POP);
}

pub(crate) fn enter_frame_initialized(ctx: &mut Lower<OpCode>, frame_slots: u32) {
    if frame_slots == 0 {
        return;
    }

    let frame_bytes = frame_slots
        .checked_mul(WORD_BYTES)
        .expect("frame size overflow");

    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MLOAD);
    push_bytes(ctx, &[FREE_PTR_SLOT]);
    ctx.push(OpCode::MLOAD);
    emit_max_top_two(ctx);
    push_bytes(ctx, &u32_to_be(frame_bytes));
    ctx.push(OpCode::ADD);
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);
}

pub(crate) fn leave_frame(ctx: &mut Lower<OpCode>, frame_slots: u32) {
    if frame_slots == 0 {
        return;
    }

    push_bytes(
        ctx,
        &u32_to_be(
            frame_slots
                .checked_mul(WORD_BYTES)
                .expect("frame size overflow"),
        ),
    );
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MLOAD);
    ctx.push(OpCode::SUB);
    push_bytes(ctx, &[DYN_SP_SLOT]);
    ctx.push(OpCode::MSTORE);
}

fn dup_op(n: u8) -> OpCode {
    match n + 1 {
        1 => OpCode::DUP1,
        2 => OpCode::DUP2,
        3 => OpCode::DUP3,
        4 => OpCode::DUP4,
        5 => OpCode::DUP5,
        6 => OpCode::DUP6,
        7 => OpCode::DUP7,
        8 => OpCode::DUP8,
        9 => OpCode::DUP9,
        10 => OpCode::DUP10,
        11 => OpCode::DUP11,
        12 => OpCode::DUP12,
        13 => OpCode::DUP13,
        14 => OpCode::DUP14,
        15 => OpCode::DUP15,
        16 => OpCode::DUP16,
        _ => unreachable!(),
    }
}

pub(crate) fn swap_op(n: u8) -> OpCode {
    match n {
        1 => OpCode::SWAP1,
        2 => OpCode::SWAP2,
        3 => OpCode::SWAP3,
        4 => OpCode::SWAP4,
        5 => OpCode::SWAP5,
        6 => OpCode::SWAP6,
        7 => OpCode::SWAP7,
        8 => OpCode::SWAP8,
        9 => OpCode::SWAP9,
        10 => OpCode::SWAP10,
        11 => OpCode::SWAP11,
        12 => OpCode::SWAP12,
        13 => OpCode::SWAP13,
        14 => OpCode::SWAP14,
        15 => OpCode::SWAP15,
        16 => OpCode::SWAP16,
        _ => unreachable!(),
    }
}

pub(crate) fn push_op(bytes: usize) -> OpCode {
    match bytes {
        0 => OpCode::PUSH0,
        1 => OpCode::PUSH1,
        2 => OpCode::PUSH2,
        3 => OpCode::PUSH3,
        4 => OpCode::PUSH4,
        5 => OpCode::PUSH5,
        6 => OpCode::PUSH6,
        7 => OpCode::PUSH7,
        8 => OpCode::PUSH8,
        9 => OpCode::PUSH9,
        10 => OpCode::PUSH10,
        11 => OpCode::PUSH11,
        12 => OpCode::PUSH12,
        13 => OpCode::PUSH13,
        14 => OpCode::PUSH14,
        15 => OpCode::PUSH15,
        16 => OpCode::PUSH16,
        17 => OpCode::PUSH17,
        18 => OpCode::PUSH18,
        19 => OpCode::PUSH19,
        20 => OpCode::PUSH20,
        21 => OpCode::PUSH21,
        22 => OpCode::PUSH22,
        23 => OpCode::PUSH23,
        24 => OpCode::PUSH24,
        25 => OpCode::PUSH25,
        26 => OpCode::PUSH26,
        27 => OpCode::PUSH27,
        28 => OpCode::PUSH28,
        29 => OpCode::PUSH29,
        30 => OpCode::PUSH30,
        31 => OpCode::PUSH31,
        32 => OpCode::PUSH32,
        _ => unreachable!(),
    }
}
