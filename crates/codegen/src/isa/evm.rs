#![allow(unused_variables, dead_code)] // XXX

pub mod opcode;
use opcode::OpCode;

use crate::{
    machinst::{
        lower::{Lower, LowerBackend},
        vcode::Label,
    },
    stackalloc::{Action, Allocator},
};
use smallvec::{smallvec, SmallVec};
use sonatina_ir::{
    insn::{BinaryOp, CastOp, JumpOp, UnaryOp},
    Immediate, Insn, InsnData, Value, U256,
};

const FRAME_POINTER_OFFSET: u8 = 0x40;

#[derive(Default)]
pub struct EvmBackend {
    // triple: TargetTriple,
}

impl LowerBackend for EvmBackend {
    type MInst = OpCode;

    fn lower(&self, ctx: &mut Lower<Self::MInst>, alloc: &mut dyn Allocator, insn: Insn) {
        let result = ctx.insn_result(insn);

        let data = ctx.insn_data(insn).clone();
        match &data {
            InsnData::Unary { code, args } => {
                perform_actions(ctx, &alloc.read(insn, args));
                match code {
                    UnaryOp::Not => {
                        ctx.push(OpCode::NOT);
                    }
                    UnaryOp::Neg => {
                        // 0 - v
                        ctx.push(OpCode::PUSH0);
                        ctx.push(OpCode::SUB);
                    }
                }
                perform_actions(ctx, &alloc.write(insn, result.unwrap()));
            }
            InsnData::Binary { code, args } => {
                perform_actions(ctx, &alloc.read(insn, args));

                match code {
                    BinaryOp::Add => ctx.push(OpCode::ADD),
                    BinaryOp::Sub => ctx.push(OpCode::SUB),
                    BinaryOp::Mul => ctx.push(OpCode::MUL),
                    BinaryOp::Udiv => ctx.push(OpCode::DIV),
                    BinaryOp::Sdiv => ctx.push(OpCode::SDIV),
                    BinaryOp::Lt => ctx.push(OpCode::LT),
                    BinaryOp::Gt => ctx.push(OpCode::GT),
                    BinaryOp::Slt => ctx.push(OpCode::SLT),
                    BinaryOp::Sgt => ctx.push(OpCode::SGT),
                    BinaryOp::Le => {
                        ctx.push(OpCode::GT);
                        ctx.push(OpCode::ISZERO)
                    }
                    BinaryOp::Ge => {
                        ctx.push(OpCode::LT);
                        ctx.push(OpCode::ISZERO)
                    }
                    BinaryOp::Sle => {
                        ctx.push(OpCode::SGT);
                        ctx.push(OpCode::ISZERO)
                    }
                    BinaryOp::Sge => {
                        ctx.push(OpCode::SLT);
                        ctx.push(OpCode::ISZERO)
                    }
                    BinaryOp::Eq => ctx.push(OpCode::EQ),
                    BinaryOp::Ne => {
                        ctx.push(OpCode::EQ);
                        ctx.push(OpCode::ISZERO)
                    }
                    BinaryOp::And => ctx.push(OpCode::AND),
                    BinaryOp::Or => ctx.push(OpCode::OR),
                    BinaryOp::Xor => ctx.push(OpCode::XOR),
                };
                perform_actions(ctx, &alloc.write(insn, result.unwrap()));
            }

            InsnData::Cast {
                code,
                args: [v],
                ty,
            } => match code {
                CastOp::Sext => {
                    todo!()
                }
                CastOp::Zext => {
                    todo!()
                }
                CastOp::Trunc => {
                    todo!()
                }
                CastOp::BitCast => {
                    todo!()
                }
            },

            InsnData::Load { args: [v], loc } => {
                todo!()
            }

            InsnData::Store {
                args, // what's the arg order?
                loc,
            } => {
                todo!()
            }

            InsnData::Call { func, args, ret_ty } => {
                // xxx if func uses memory, store new fp

                // Push (pc+1) onto stack, for jump at end of func.
                let p = ctx.push(OpCode::PUSH1);
                ctx.add_jump_fixup_inst(p, Label::Insn(ctx.next_insn()));

                perform_actions(ctx, &alloc.read(insn, &args));
                let p = ctx.push(OpCode::PUSH1);
                ctx.add_jump_fixup_inst(p, Label::Function(*func));
                ctx.push(OpCode::JUMP);
            }

            InsnData::Jump {
                code,
                dests: [dest],
            } => {
                perform_actions(ctx, &alloc.traverse_edge(ctx.insn_block(insn), *dest));
                if *code == JumpOp::Jump {
                    let push_op = ctx.push(OpCode::PUSH1);
                    ctx.add_jump_fixup_inst(push_op, Label::Block(*dest));
                    ctx.push(OpCode::JUMP);
                }
            }

            InsnData::Branch {
                args,
                dests: [left, right],
            } => {
                // JUMPI: dest is top of stack, bool val is next
                perform_actions(ctx, &alloc.read(insn, args));

                let from = ctx.insn_block(insn);
                let jumpi_target = ctx.push(OpCode::PUSH1);
                ctx.push(OpCode::JUMPI); // Fixup handled below.

                // Perform stack-prep actions for the right branch, and jump.
                perform_actions(ctx, &alloc.traverse_edge(ctx.insn_block(insn), *right));
                let right_jump_target = ctx.push(OpCode::PUSH1);
                ctx.add_jump_fixup_inst(right_jump_target, Label::Block(*right));
                ctx.push(OpCode::JUMP);

                // If there are any stack-prep actions for the left branch,
                // perform them, then jump left.
                let left_actions = alloc.traverse_edge(from, *left);
                if !left_actions.is_empty() {
                    ctx.add_jump_fixup_inst(jumpi_target, Label::Insn(ctx.next_insn()));
                    perform_actions(ctx, &left_actions);

                    let left_jump_target = ctx.push(OpCode::PUSH1);
                    ctx.add_jump_fixup_inst(left_jump_target, Label::Block(*left));
                    ctx.push(OpCode::JUMP);
                } else {
                    // Otherwise, we can jump directly to the left block.
                    ctx.add_jump_fixup_inst(jumpi_target, Label::Block(*left));
                }
            }

            InsnData::BrTable {
                args,
                default,
                table,
            } => {}

            InsnData::Alloca { ty } => {}

            InsnData::Gep { args } => {}

            InsnData::Return { args } => {
                let v = match args {
                    Some(v) => core::slice::from_ref(v),
                    None => &[],
                };
                perform_actions(ctx, &alloc.read(insn, v));

                // Caller pushes return location onto stack prior to call.
                if args.is_some() {
                    // Swap the return loc to the top.
                    ctx.push(OpCode::SWAP1);
                }
                ctx.push(OpCode::JUMP);
            }

            InsnData::Phi { values, blocks, ty } => {}
        }
    }
}

fn read_vals(ctx: &mut Lower<OpCode>, alloc: &mut dyn Allocator, insn: Insn, vals: &[Value]) {}

/// Panics if `insn` has no result value
fn write_result(
    ctx: &mut Lower<OpCode>,
    alloc: &mut dyn Allocator,
    insn: Insn,
    val: Option<Value>,
) {
    perform_actions(ctx, &alloc.write(insn, val.unwrap()));
}

fn perform_actions(ctx: &mut Lower<OpCode>, actions: &[Action]) {
    for action in actions {
        match action {
            Action::StackDup(slot) => {
                ctx.push(dup_op(*slot));
            }
            Action::StackSwap(n) => {
                ctx.push(swap_op(*n));
            }
            Action::Push(imm) => {
                let bytes = imm_to_be_bytes(&imm);
                push_imm(ctx, &bytes);
            }
            Action::Pop => {
                ctx.push(OpCode::POP);
            }
            Action::MemLoadAbs(offset) => {
                let bytes = u32_to_be(*offset);
                push_imm(ctx, &bytes);
                ctx.push(OpCode::MLOAD);
            }
            Action::MemLoadFrameSlot(offset) => {
                ctx.push_with_imm(OpCode::PUSH1, &[FRAME_POINTER_OFFSET]);
                ctx.push(OpCode::MLOAD);
                let bytes = u32_to_be(*offset);
                push_imm(ctx, &bytes);
                ctx.push(OpCode::ADD);
                ctx.push(OpCode::MLOAD);
            }
            Action::MemStoreAbs(offset) => {
                let bytes = u32_to_be(*offset);
                push_imm(ctx, &bytes);
                ctx.push(OpCode::MSTORE);
            }
            Action::MemStoreFrameSlot(offset) => {
                ctx.push_with_imm(OpCode::PUSH1, &[FRAME_POINTER_OFFSET]);
                ctx.push(OpCode::MLOAD);
                let bytes = u32_to_be(*offset);
                push_imm(ctx, &bytes);
                ctx.push(OpCode::ADD);
                ctx.push(OpCode::MSTORE);
            }
        }
    }
}

fn push_imm(ctx: &mut Lower<OpCode>, bytes: &[u8]) {
    assert!(!bytes.is_empty());
    if bytes == &[0] {
        ctx.push(OpCode::PUSH0);
    } else {
        ctx.push_with_imm(push_op(bytes.len()), bytes);
    }
}

fn imm_to_be_bytes(imm: &Immediate) -> SmallVec<[u8; 4]> {
    match imm {
        Immediate::I1(v) => smallvec![*v as u8],
        Immediate::I8(v) => smallvec![*v as u8],
        Immediate::I16(v) => todo!(),
        Immediate::I32(v) => todo!(),
        Immediate::I64(v) => todo!(),
        Immediate::I128(v) => todo!(),
        Immediate::I256(v) => todo!(),
    }
}
fn u32_to_be(num: u32) -> SmallVec<[u8; 4]> {
    if num == 0 {
        smallvec![0]
    } else {
        num.to_be_bytes()
            .into_iter()
            .skip_while(|b| *b == 0)
            .collect()
    }
}

fn u256_to_be(num: &U256) -> SmallVec<[u8; 8]> {
    if num.is_zero() {
        smallvec![0]
    } else {
        let mut b = [0; 32];
        num.to_big_endian(&mut b);
        b.into_iter().skip_while(|b| *b == 0).collect()
    }
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

fn swap_op(n: u8) -> OpCode {
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

fn push_op(bytes: usize) -> OpCode {
    match bytes {
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
        _ => unreachable!(),
    }
}
