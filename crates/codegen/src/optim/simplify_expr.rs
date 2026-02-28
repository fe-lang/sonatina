use sonatina_ir::{
    Function, Immediate, Type, ValueId,
    inst::{BinaryInstKind, CastInstKind, UnaryInstKind},
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

pub(crate) fn simplify_unary_with_same_inner(
    kind: UnaryInstKind,
    arg: ValueId,
    same_inner_arg: impl Fn(ValueId, UnaryInstKind) -> Option<ValueId>,
) -> SimplifyExprResult {
    match kind {
        UnaryInstKind::Not | UnaryInstKind::Neg => same_inner_arg(arg, kind)
            .map(SimplifyExprResult::Copy)
            .unwrap_or(SimplifyExprResult::NoChange),
        UnaryInstKind::IsZero | UnaryInstKind::EvmClz => SimplifyExprResult::NoChange,
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
        BinaryInstKind::Shl | BinaryInstKind::Shr | BinaryInstKind::Sar => {
            let value_ty = func.dfg.value_ty(rhs);
            let value_zero = Immediate::zero(value_ty);
            if rhs_imm == Some(value_zero) {
                return SimplifyExprResult::Const(value_zero);
            }
            if lhs_imm.is_some_and(Immediate::is_zero) {
                return SimplifyExprResult::Copy(rhs);
            }
        }
        BinaryInstKind::Lt
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

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        I256, Immediate, Linkage, Signature, Type, builder::test_util::test_isa, module::ModuleCtx,
    };

    use super::*;

    #[test]
    fn simplify_unary_with_same_inner_folds_double_not() {
        let arg = ValueId::from_u32(42);
        let simplified = simplify_unary_with_same_inner(UnaryInstKind::Not, arg, |value, kind| {
            if value == arg && kind == UnaryInstKind::Not {
                Some(ValueId::from_u32(7))
            } else {
                None
            }
        });

        assert_eq!(simplified, SimplifyExprResult::Copy(ValueId::from_u32(7)));
    }

    #[test]
    fn simplify_binary_with_known_imm_folds_shift_identities() {
        let isa = test_isa();
        let ctx = ModuleCtx::new(&isa);
        let sig = Signature::new("f", Linkage::Private, &[], Type::I256);
        let mut func = Function::new(&ctx, &sig);
        let bits = func.dfg.make_imm_value(Immediate::zero(Type::I8));
        let value = func
            .dfg
            .make_imm_value(Immediate::from_i256(I256::from(7), Type::I256));

        let simplified = simplify_binary_with_known_imm(
            &func,
            BinaryInstKind::Shl,
            bits,
            value,
            |v| func.dfg.value_imm(v),
            |_lhs, _rhs| false,
        );
        assert_eq!(simplified, SimplifyExprResult::Copy(value));
    }
}
