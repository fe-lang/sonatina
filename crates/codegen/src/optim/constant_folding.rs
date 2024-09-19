use sonatina_ir::{
    inst::{BinaryOp, CastOp, UnaryOp},
    DataFlowGraph, Immediate, InsnData,
};

pub(super) fn fold_constant(dfg: &DataFlowGraph, insn_data: &InsnData) -> Option<Immediate> {
    match insn_data {
        InsnData::Unary { code, args } => {
            let arg = dfg.value_imm(args[0])?;
            Some(match *code {
                UnaryOp::Not => !arg,
                UnaryOp::Neg => -arg,
            })
        }

        InsnData::Binary { code, args } => {
            let lhs = dfg.value_imm(args[0])?;
            let rhs = dfg.value_imm(args[1])?;
            Some(match *code {
                BinaryOp::Add => lhs + rhs,
                BinaryOp::Sub => lhs - rhs,
                BinaryOp::Mul => lhs * rhs,
                BinaryOp::Udiv => lhs.udiv(rhs),
                BinaryOp::Sdiv => lhs.sdiv(rhs),
                BinaryOp::Lt => lhs.lt(rhs),
                BinaryOp::Gt => lhs.gt(rhs),
                BinaryOp::Slt => lhs.slt(rhs),
                BinaryOp::Sgt => lhs.sgt(rhs),
                BinaryOp::Le => lhs.le(rhs),
                BinaryOp::Ge => lhs.ge(rhs),
                BinaryOp::Sle => lhs.sle(rhs),
                BinaryOp::Sge => lhs.sge(rhs),
                BinaryOp::Eq => lhs.imm_eq(rhs),
                BinaryOp::Ne => lhs.imm_ne(rhs),
                BinaryOp::And => lhs & rhs,
                BinaryOp::Or => lhs | rhs,
                BinaryOp::Xor => lhs ^ rhs,
            })
        }

        InsnData::Cast { code, args, ty } => {
            let arg = dfg.value_imm(args[0])?;
            Some(match code {
                CastOp::Sext => arg.sext(*ty),
                CastOp::Zext => arg.zext(*ty),
                CastOp::Trunc => arg.trunc(*ty),
                CastOp::BitCast => return None,
            })
        }

        InsnData::Load { .. }
        | InsnData::Jump { .. }
        | InsnData::Branch { .. }
        | InsnData::BrTable { .. }
        | InsnData::Store { .. }
        | InsnData::Call { .. }
        | InsnData::Alloca { .. }
        | InsnData::Gep { .. }
        | InsnData::Return { .. }
        | InsnData::Phi { .. } => None,
    }
}
