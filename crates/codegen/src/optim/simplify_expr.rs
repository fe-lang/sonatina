use sonatina_ir::{
    Function, Immediate, Type, ValueId,
    inst::{BinaryInstKind, CastInstKind},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SimplifyExprResult {
    Const(Immediate),
    Copy(ValueId),
    NoChange,
}

impl SimplifyExprResult {
    pub(crate) fn is_no_change(&self) -> bool {
        matches!(self, Self::NoChange)
    }
}

pub(crate) fn simplify_binary_with_known_imm(
    func: &Function,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    known_imm: impl Fn(ValueId) -> Option<Immediate>,
    same_value: impl Fn(ValueId, ValueId) -> bool,
) -> SimplifyExprResult {
    let ty = func.dfg.value_ty(lhs);
    let lhs_imm = known_imm(lhs);
    let rhs_imm = known_imm(rhs);

    match kind {
        BinaryInstKind::Add => {
            if lhs_imm.is_some_and(Immediate::is_zero) {
                return SimplifyExprResult::Copy(rhs);
            }
            if rhs_imm.is_some_and(Immediate::is_zero) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Sub => {
            if ty.is_integral() && same_value(lhs, rhs) {
                return SimplifyExprResult::Const(Immediate::zero(ty));
            }
            if rhs_imm == Some(Immediate::zero(ty)) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Mul => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                let one = Immediate::one(ty);
                if lhs_imm == Some(zero) || rhs_imm == Some(zero) {
                    return SimplifyExprResult::Const(zero);
                }
                if lhs_imm == Some(one) {
                    return SimplifyExprResult::Copy(rhs);
                }
                if rhs_imm == Some(one) {
                    return SimplifyExprResult::Copy(lhs);
                }
            }
        }
        BinaryInstKind::And => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                let all_one = Immediate::all_one(ty);
                if lhs_imm == Some(zero) || rhs_imm == Some(zero) {
                    return SimplifyExprResult::Const(zero);
                }
                if lhs_imm == Some(all_one) {
                    return SimplifyExprResult::Copy(rhs);
                }
                if rhs_imm == Some(all_one) {
                    return SimplifyExprResult::Copy(lhs);
                }
            }
            if same_value(lhs, rhs) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Or => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                let all_one = Immediate::all_one(ty);
                if lhs_imm == Some(all_one) || rhs_imm == Some(all_one) {
                    return SimplifyExprResult::Const(all_one);
                }
                if lhs_imm == Some(zero) {
                    return SimplifyExprResult::Copy(rhs);
                }
                if rhs_imm == Some(zero) {
                    return SimplifyExprResult::Copy(lhs);
                }
            }
            if same_value(lhs, rhs) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Xor => {
            if ty.is_integral() {
                let zero = Immediate::zero(ty);
                if lhs_imm == Some(zero) {
                    return SimplifyExprResult::Copy(rhs);
                }
                if rhs_imm == Some(zero) {
                    return SimplifyExprResult::Copy(lhs);
                }
                if same_value(lhs, rhs) {
                    return SimplifyExprResult::Const(zero);
                }
            }
        }
        BinaryInstKind::Udiv
        | BinaryInstKind::Sdiv
        | BinaryInstKind::EvmUdiv
        | BinaryInstKind::EvmSdiv => {
            if ty.is_integral() && rhs_imm == Some(Immediate::one(ty)) {
                return SimplifyExprResult::Copy(lhs);
            }
        }
        BinaryInstKind::Umod
        | BinaryInstKind::Smod
        | BinaryInstKind::EvmUmod
        | BinaryInstKind::EvmSmod => {
            if ty.is_integral() && rhs_imm == Some(Immediate::one(ty)) {
                return SimplifyExprResult::Const(Immediate::zero(ty));
            }
        }
        BinaryInstKind::Eq => {
            if same_value(lhs, rhs) {
                return SimplifyExprResult::Const(Immediate::one(Type::I1));
            }
        }
        BinaryInstKind::Ne => {
            if same_value(lhs, rhs) {
                return SimplifyExprResult::Const(Immediate::zero(Type::I1));
            }
        }
        BinaryInstKind::Shl
        | BinaryInstKind::Shr
        | BinaryInstKind::Sar
        | BinaryInstKind::Lt
        | BinaryInstKind::Gt
        | BinaryInstKind::Slt
        | BinaryInstKind::Sgt
        | BinaryInstKind::Le
        | BinaryInstKind::Ge
        | BinaryInstKind::Sle
        | BinaryInstKind::Sge
        | BinaryInstKind::EvmExp
        | BinaryInstKind::EvmByte => {}
    }

    SimplifyExprResult::NoChange
}

pub(crate) fn simplify_cast(
    func: &Function,
    _kind: CastInstKind,
    from: ValueId,
    ty: Type,
) -> SimplifyExprResult {
    if func.dfg.value_ty(from) == ty {
        SimplifyExprResult::Copy(from)
    } else {
        SimplifyExprResult::NoChange
    }
}
