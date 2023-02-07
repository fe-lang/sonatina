#![allow(unused_variables)] // XXX

pub mod opcode;

use opcode::OpCode;

use sonatina_ir::{
    insn::{BinaryOp, CastOp, JumpOp, UnaryOp},
    Insn, InsnData,
};

use crate::machinst::lower::{Lower, LowerBackend};

#[derive(Default)]
pub struct EvmBackend {
    // triple: TargetTriple,
}

impl LowerBackend for EvmBackend {
    type MInst = OpCode;

    fn lower(&self, ctx: &mut Lower<Self::MInst>, insn: Insn) {
        // naive insn lowering
        let result_reg = ctx.insn_result_reg(insn);

        let data = ctx.insn_data(insn).clone(); // XXX shoot
        match &data {
            InsnData::Unary { code, args: [v] } => {
                let arg = ctx.value_reg(*v);
                match code {
                    UnaryOp::Not => {
                        ctx.push(OpCode::NOT, &[ctx.value_reg(*v)], &[result_reg.unwrap()]);
                    }

                    UnaryOp::Neg => {
                        ctx.push(OpCode::PUSH1([0]), &[], &[]);
                        ctx.push(OpCode::SUB, &[arg], &[result_reg.unwrap()]);
                    }
                }
            }
            InsnData::Binary {
                code,
                args: [v1, v2],
            } => {
                let ins = &[ctx.value_reg(*v1), ctx.value_reg(*v2)];
                let out = &[result_reg.unwrap()];

                match code {
                    BinaryOp::Add => {
                        ctx.push(OpCode::ADD, ins, out);
                    }
                    BinaryOp::Sub => {
                        ctx.push(OpCode::SUB, ins, out);
                    }
                    BinaryOp::Mul => {
                        ctx.push(OpCode::MUL, ins, out);
                    }
                    BinaryOp::Udiv => {
                        ctx.push(OpCode::DIV, ins, out);
                    }
                    BinaryOp::Sdiv => {
                        ctx.push(OpCode::SDIV, ins, out);
                    }
                    BinaryOp::Lt => {
                        ctx.push(OpCode::LT, ins, out);
                    }
                    BinaryOp::Gt => {
                        ctx.push(OpCode::GT, ins, out);
                    }
                    BinaryOp::Slt => {
                        ctx.push(OpCode::SLT, ins, out);
                    }
                    BinaryOp::Sgt => {
                        ctx.push(OpCode::SGT, ins, out);
                    }

                    BinaryOp::Le => {
                        ctx.push(OpCode::GT, ins, &[]);
                        ctx.push(OpCode::ISZERO, &[], out);
                    }
                    BinaryOp::Ge => {
                        ctx.push(OpCode::LT, ins, &[]);
                        ctx.push(OpCode::ISZERO, &[], out);
                    }
                    BinaryOp::Sle => {
                        ctx.push(OpCode::SGT, ins, &[]);
                        ctx.push(OpCode::ISZERO, &[], out);
                    }
                    BinaryOp::Sge => {
                        ctx.push(OpCode::SLT, ins, &[]);
                        ctx.push(OpCode::ISZERO, &[], out);
                    }
                    BinaryOp::Eq => {
                        ctx.push(OpCode::EQ, ins, out);
                    }
                    BinaryOp::Ne => {
                        ctx.push(OpCode::EQ, ins, &[]);
                        ctx.push(OpCode::ISZERO, &[], out);
                    }
                    BinaryOp::And => {
                        ctx.push(OpCode::AND, ins, out);
                    }
                    BinaryOp::Or => {
                        ctx.push(OpCode::OR, ins, out);
                    }
                    BinaryOp::Xor => {
                        ctx.push(OpCode::XOR, ins, out);
                    }
                };
            }

            InsnData::Cast {
                code,
                args: [v],
                ty,
            } => match code {
                CastOp::Sext => {}
                CastOp::Zext => {}
                CastOp::Trunc => {}
                CastOp::BitCast => {}
            },

            InsnData::Load { args: [v], loc } => {}

            InsnData::Store {
                args: [v1, v2],
                loc,
            } => {}

            InsnData::Call { func, args, ret_ty } => {}

            InsnData::Jump {
                code: JumpOp::FallThrough,
                ..
            } => {} // XXX noop, presumably?
            InsnData::Jump {
                code: JumpOp::Jump,
                dests: [dest],
            } => {
                let dest_reg = ctx.jumpdest_reg(*dest);
                let push_op = ctx.push(OpCode::PUSH2([0, 0]), &[], &[dest_reg]);
                ctx.add_jump_fixup_inst(push_op, *dest);
                ctx.push(OpCode::JUMP, &[dest_reg], &[]);
                // XXX mark as side-effecting
            }

            InsnData::Branch {
                args: [v],
                dests: [left, right],
            } => {
                let left_reg = ctx.jumpdest_reg(*left);
                let push_op = ctx.push(OpCode::PUSH2([0, 0]), &[], &[left_reg]);
                ctx.add_jump_fixup_inst(push_op, *left);
                ctx.push(OpCode::JUMPI, &[left_reg, ctx.value_reg(*v)], &[]);

                let right_reg = ctx.jumpdest_reg(*right);
                let push_op = ctx.push(OpCode::PUSH2([0, 0]), &[], &[right_reg]);
                ctx.add_jump_fixup_inst(push_op, *right);
                ctx.push(OpCode::JUMP, &[right_reg], &[]);
            }

            InsnData::BrTable {
                args,
                default,
                table,
            } => {}

            InsnData::Alloca { ty } => {}

            InsnData::Gep { args } => {}

            InsnData::Return { args } => {}

            InsnData::Phi { values, blocks, ty } => {}
        }
    }
}
