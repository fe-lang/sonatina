use cranelift_entity::SecondaryMap;
use smallvec::{SmallVec, smallvec};
use sonatina_ir::{
    Function, Immediate, InstId, Type, Value, ValueId,
    inst::{
        BinaryInstKind, CastInstKind, InstClassKind, UnaryInstKind, cast, data, downcast,
        inst_set::InstSetBase,
    },
};

use super::{
    sccp::LatticeCell,
    simplify_expr::{
        SimplifyExprResult, simplify_binary_with_known_imm, simplify_cast,
        simplify_unary_with_same_inner,
    },
};

#[derive(Clone, Copy)]
pub(super) enum SimplifyAction {
    Const(Immediate),
    Copy(ValueId),
    NoChange,
}

pub(super) type SimplifyResults = SmallVec<[SimplifyAction; 1]>;

fn from_expr_simplify_result(simplified: SimplifyExprResult) -> SimplifyAction {
    match simplified {
        SimplifyExprResult::Const(imm) => SimplifyAction::Const(imm),
        SimplifyExprResult::Copy(value) => SimplifyAction::Copy(value),
        SimplifyExprResult::NoChange => SimplifyAction::NoChange,
    }
}

fn wrap_action(action: SimplifyAction) -> SimplifyResults {
    smallvec![action]
}

fn no_change_results(len: usize) -> SimplifyResults {
    std::iter::repeat_n(SimplifyAction::NoChange, len).collect()
}

fn known_imm(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    v: ValueId,
) -> Option<Immediate> {
    func.dfg.value_imm(v).or_else(|| match lattice.get(v) {
        Some(LatticeCell::Const(imm)) => Some(*imm),
        _ => None,
    })
}

fn is_explicit_undef(func: &Function, v: ValueId) -> bool {
    matches!(func.dfg.value(v), Value::Undef { .. })
}

fn is_may_be_undef(
    func: &Function,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    v: ValueId,
) -> bool {
    is_explicit_undef(func, v) || may_be_undef.get(v).copied().unwrap_or_default()
}

fn same_non_undef(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
) -> bool {
    if lhs != rhs {
        return false;
    }
    if is_may_be_undef(func, may_be_undef, lhs) {
        return false;
    }
    if func.dfg.value_imm(lhs).is_some() {
        return true;
    }

    !matches!(lattice.get(lhs), Some(LatticeCell::Bot) | None)
}

fn simplify_commutative_and(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    from_expr_simplify_result(simplify_binary_with_known_imm(
        func,
        BinaryInstKind::And,
        lhs,
        rhs,
        |v| known_imm(func, lattice, v),
        |lhs, rhs| same_non_undef(func, lattice, may_be_undef, lhs, rhs),
    ))
}

fn simplify_commutative_or(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    from_expr_simplify_result(simplify_binary_with_known_imm(
        func,
        BinaryInstKind::Or,
        lhs,
        rhs,
        |v| known_imm(func, lattice, v),
        |lhs, rhs| same_non_undef(func, lattice, may_be_undef, lhs, rhs),
    ))
}

fn simplify_commutative_xor(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    from_expr_simplify_result(simplify_binary_with_known_imm(
        func,
        BinaryInstKind::Xor,
        lhs,
        rhs,
        |v| known_imm(func, lattice, v),
        |lhs, rhs| same_non_undef(func, lattice, may_be_undef, lhs, rhs),
    ))
}

fn simplify_commutative_mul(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    from_expr_simplify_result(simplify_binary_with_known_imm(
        func,
        BinaryInstKind::Mul,
        lhs,
        rhs,
        |v| known_imm(func, lattice, v),
        |_lhs, _rhs| false,
    ))
}

fn simplify_commutative_add(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    from_expr_simplify_result(simplify_binary_with_known_imm(
        func,
        BinaryInstKind::Add,
        lhs,
        rhs,
        |v| known_imm(func, lattice, v),
        |_lhs, _rhs| false,
    ))
}

fn simplify_gep_all_zero(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    values: &[ValueId],
) -> SimplifyAction {
    let Some((&base, indices)) = values.split_first() else {
        return SimplifyAction::NoChange;
    };

    if indices
        .iter()
        .all(|&idx| known_imm(func, lattice, idx).is_some_and(Immediate::is_zero))
    {
        return SimplifyAction::Copy(base);
    }

    SimplifyAction::NoChange
}

fn simplify_sub(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    from_expr_simplify_result(simplify_binary_with_known_imm(
        func,
        BinaryInstKind::Sub,
        lhs,
        rhs,
        |v| known_imm(func, lattice, v),
        |lhs, rhs| same_non_undef(func, lattice, may_be_undef, lhs, rhs),
    ))
}

fn simplify_redundant_cast(
    func: &Function,
    kind: CastInstKind,
    from: ValueId,
    ty: Type,
) -> SimplifyAction {
    from_expr_simplify_result(simplify_cast(func, kind, from, ty))
}

fn zext_i1_source(func: &Function, is: &dyn InstSetBase, value: ValueId) -> Option<ValueId> {
    let Value::Inst { inst, .. } = func.dfg.value(value) else {
        return None;
    };
    let zext = downcast::<&cast::Zext>(is, func.dfg.inst(*inst))?;
    let from = *zext.from();
    (func.dfg.value_ty(from) == Type::I1).then_some(from)
}

fn simplify_eq_zext_i1_one(
    func: &Function,
    is: &dyn InstSetBase,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    if let Some(from) = zext_i1_source(func, is, lhs)
        && known_imm(func, lattice, rhs) == Some(Immediate::one(func.dfg.value_ty(lhs)))
    {
        return SimplifyAction::Copy(from);
    }
    if let Some(from) = zext_i1_source(func, is, rhs)
        && known_imm(func, lattice, lhs) == Some(Immediate::one(func.dfg.value_ty(rhs)))
    {
        return SimplifyAction::Copy(from);
    }
    SimplifyAction::NoChange
}

fn simplify_ne_zext_i1_zero(
    func: &Function,
    is: &dyn InstSetBase,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    if let Some(from) = zext_i1_source(func, is, lhs)
        && known_imm(func, lattice, rhs) == Some(Immediate::zero(func.dfg.value_ty(lhs)))
    {
        return SimplifyAction::Copy(from);
    }
    if let Some(from) = zext_i1_source(func, is, rhs)
        && known_imm(func, lattice, lhs) == Some(Immediate::zero(func.dfg.value_ty(rhs)))
    {
        return SimplifyAction::Copy(from);
    }
    SimplifyAction::NoChange
}

fn simplify_div_by_one(
    func: &Function,
    kind: BinaryInstKind,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    from_expr_simplify_result(simplify_binary_with_known_imm(
        func,
        kind,
        lhs,
        rhs,
        |v| known_imm(func, lattice, v),
        |_lhs, _rhs| false,
    ))
}

fn simplify_rem_by_one(
    func: &Function,
    kind: BinaryInstKind,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    from_expr_simplify_result(simplify_binary_with_known_imm(
        func,
        kind,
        lhs,
        rhs,
        |v| known_imm(func, lattice, v),
        |_lhs, _rhs| false,
    ))
}

fn simplify_cmp_self(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
    result: bool,
) -> SimplifyAction {
    if same_non_undef(func, lattice, may_be_undef, lhs, rhs) {
        return SimplifyAction::Const(Immediate::I1(result));
    }

    SimplifyAction::NoChange
}

fn simplify_uaddo(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
    results_len: usize,
) -> SimplifyResults {
    if results_len != 2 {
        return no_change_results(results_len);
    }

    let lhs_ty = func.dfg.value_ty(lhs);
    if known_imm(func, lattice, rhs) == Some(Immediate::zero(lhs_ty)) {
        return smallvec![
            SimplifyAction::Copy(lhs),
            SimplifyAction::Const(Immediate::I1(false))
        ];
    }
    if known_imm(func, lattice, lhs) == Some(Immediate::zero(lhs_ty)) {
        return smallvec![
            SimplifyAction::Copy(rhs),
            SimplifyAction::Const(Immediate::I1(false))
        ];
    }
    no_change_results(results_len)
}

fn simplify_usubo(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
    results_len: usize,
) -> SimplifyResults {
    if results_len != 2 {
        return no_change_results(results_len);
    }

    let lhs_ty = func.dfg.value_ty(lhs);
    if known_imm(func, lattice, rhs) == Some(Immediate::zero(lhs_ty)) {
        return smallvec![
            SimplifyAction::Copy(lhs),
            SimplifyAction::Const(Immediate::I1(false))
        ];
    }

    no_change_results(results_len)
}

fn simplify_umulo(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
    results_len: usize,
) -> SimplifyResults {
    if results_len != 2 {
        return no_change_results(results_len);
    }

    let lhs_ty = func.dfg.value_ty(lhs);
    let zero = Immediate::zero(lhs_ty);
    let one = Immediate::one(lhs_ty);

    if known_imm(func, lattice, lhs) == Some(zero) || known_imm(func, lattice, rhs) == Some(zero) {
        return smallvec![
            SimplifyAction::Const(zero),
            SimplifyAction::Const(Immediate::I1(false))
        ];
    }
    if known_imm(func, lattice, lhs) == Some(one) {
        return smallvec![
            SimplifyAction::Copy(rhs),
            SimplifyAction::Const(Immediate::I1(false))
        ];
    }
    if known_imm(func, lattice, rhs) == Some(one) {
        return smallvec![
            SimplifyAction::Copy(lhs),
            SimplifyAction::Const(Immediate::I1(false))
        ];
    }

    no_change_results(results_len)
}

fn simplify_saturating_add(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    let ty = func.dfg.value_ty(lhs);
    if known_imm(func, lattice, rhs) == Some(Immediate::zero(ty)) {
        return SimplifyAction::Copy(lhs);
    }
    if known_imm(func, lattice, lhs) == Some(Immediate::zero(ty)) {
        return SimplifyAction::Copy(rhs);
    }
    SimplifyAction::NoChange
}

fn simplify_saturating_sub(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
    unsigned: bool,
) -> SimplifyAction {
    let ty = func.dfg.value_ty(lhs);
    if known_imm(func, lattice, rhs) == Some(Immediate::zero(ty)) {
        return SimplifyAction::Copy(lhs);
    }
    if unsigned
        && known_imm(func, lattice, lhs) == Some(Immediate::zero(ty))
        && !is_may_be_undef(func, may_be_undef, rhs)
    {
        return SimplifyAction::Const(Immediate::zero(ty));
    }
    SimplifyAction::NoChange
}

fn simplify_saturating_mul(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyAction {
    let ty = func.dfg.value_ty(lhs);
    let zero = Immediate::zero(ty);
    let one = Immediate::one(ty);

    if (known_imm(func, lattice, lhs) == Some(zero) && !is_may_be_undef(func, may_be_undef, rhs))
        || (known_imm(func, lattice, rhs) == Some(zero)
            && !is_may_be_undef(func, may_be_undef, lhs))
    {
        return SimplifyAction::Const(zero);
    }
    if known_imm(func, lattice, lhs) == Some(one) {
        return SimplifyAction::Copy(rhs);
    }
    if known_imm(func, lattice, rhs) == Some(one) {
        return SimplifyAction::Copy(lhs);
    }
    SimplifyAction::NoChange
}

fn simplify_snego(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    arg: ValueId,
    results_len: usize,
) -> SimplifyResults {
    if results_len != 2 {
        return no_change_results(results_len);
    }

    let arg_ty = func.dfg.value_ty(arg);
    if known_imm(func, lattice, arg) == Some(Immediate::zero(arg_ty)) {
        return smallvec![
            SimplifyAction::Const(Immediate::zero(arg_ty)),
            SimplifyAction::Const(Immediate::I1(false))
        ];
    }

    no_change_results(results_len)
}

fn simplify_evm_divo(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
    results_len: usize,
) -> SimplifyResults {
    if results_len != 2 {
        return no_change_results(results_len);
    }

    let lhs_ty = func.dfg.value_ty(lhs);
    if known_imm(func, lattice, rhs) == Some(Immediate::one(lhs_ty)) {
        return smallvec![
            SimplifyAction::Copy(lhs),
            SimplifyAction::Const(Immediate::I1(false))
        ];
    }

    no_change_results(results_len)
}

fn simplify_evm_modo(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
    results_len: usize,
) -> SimplifyResults {
    if results_len != 2 {
        return no_change_results(results_len);
    }

    let lhs_ty = func.dfg.value_ty(lhs);
    if known_imm(func, lattice, rhs) == Some(Immediate::one(lhs_ty)) {
        let imm = Immediate::zero(lhs_ty);
        return smallvec![
            SimplifyAction::Const(imm),
            SimplifyAction::Const(Immediate::I1(false))
        ];
    }

    no_change_results(results_len)
}

pub(super) fn simplify_inst(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    inst_id: InstId,
) -> SimplifyResults {
    let inst = func.dfg.inst(inst_id);
    let is = func.inst_set();
    let results_len = func.dfg.inst_results(inst_id).len();

    match inst.kind() {
        InstClassKind::Unary(kind) => {
            let values = inst.collect_values();
            let [arg] = values.as_slice() else {
                return no_change_results(results_len);
            };

            if matches!(kind, UnaryInstKind::Snego) {
                return simplify_snego(func, lattice, *arg, results_len);
            }

            wrap_action(from_expr_simplify_result(simplify_unary_with_same_inner(
                kind,
                *arg,
                |arg, expected| {
                    let Value::Inst { inst, .. } = func.dfg.value(arg) else {
                        return None;
                    };
                    let inner = func.dfg.inst(*inst);
                    if inner.kind() != InstClassKind::Unary(expected) {
                        return None;
                    }

                    let values = inner.collect_values();
                    let [arg] = values.as_slice() else {
                        return None;
                    };
                    Some(*arg)
                },
            )))
        }
        InstClassKind::Binary(kind) => {
            let values = inst.collect_values();
            let [lhs, rhs] = values.as_slice() else {
                return no_change_results(results_len);
            };

            if matches!(kind, BinaryInstKind::Uaddo | BinaryInstKind::Saddo) {
                return simplify_uaddo(func, lattice, *lhs, *rhs, results_len);
            }
            if matches!(kind, BinaryInstKind::Uaddsat | BinaryInstKind::Saddsat) {
                return wrap_action(simplify_saturating_add(func, lattice, *lhs, *rhs));
            }
            if matches!(kind, BinaryInstKind::Usubo | BinaryInstKind::Ssubo) {
                return simplify_usubo(func, lattice, *lhs, *rhs, results_len);
            }
            if matches!(kind, BinaryInstKind::Usubsat | BinaryInstKind::Ssubsat) {
                return wrap_action(simplify_saturating_sub(
                    func,
                    lattice,
                    may_be_undef,
                    *lhs,
                    *rhs,
                    matches!(kind, BinaryInstKind::Usubsat),
                ));
            }
            if matches!(kind, BinaryInstKind::Umulo | BinaryInstKind::Smulo) {
                return simplify_umulo(func, lattice, *lhs, *rhs, results_len);
            }
            if matches!(kind, BinaryInstKind::Umulsat | BinaryInstKind::Smulsat) {
                return wrap_action(simplify_saturating_mul(
                    func,
                    lattice,
                    may_be_undef,
                    *lhs,
                    *rhs,
                ));
            }
            if matches!(kind, BinaryInstKind::EvmUdivo | BinaryInstKind::EvmSdivo) {
                return simplify_evm_divo(func, lattice, *lhs, *rhs, results_len);
            }
            if matches!(kind, BinaryInstKind::EvmUmodo | BinaryInstKind::EvmSmodo) {
                return simplify_evm_modo(func, lattice, *lhs, *rhs, results_len);
            }

            wrap_action(match kind {
                BinaryInstKind::And => {
                    simplify_commutative_and(func, lattice, may_be_undef, *lhs, *rhs)
                }
                BinaryInstKind::Or => {
                    simplify_commutative_or(func, lattice, may_be_undef, *lhs, *rhs)
                }
                BinaryInstKind::Xor => {
                    simplify_commutative_xor(func, lattice, may_be_undef, *lhs, *rhs)
                }
                BinaryInstKind::Mul => simplify_commutative_mul(func, lattice, *lhs, *rhs),
                BinaryInstKind::Add => simplify_commutative_add(func, lattice, *lhs, *rhs),
                BinaryInstKind::Sub => simplify_sub(func, lattice, may_be_undef, *lhs, *rhs),
                BinaryInstKind::Udiv
                | BinaryInstKind::Sdiv
                | BinaryInstKind::EvmUdiv
                | BinaryInstKind::EvmSdiv => simplify_div_by_one(func, kind, lattice, *lhs, *rhs),
                BinaryInstKind::Umod
                | BinaryInstKind::Smod
                | BinaryInstKind::EvmUmod
                | BinaryInstKind::EvmSmod => simplify_rem_by_one(func, kind, lattice, *lhs, *rhs),
                BinaryInstKind::Shl | BinaryInstKind::Shr | BinaryInstKind::Sar => {
                    from_expr_simplify_result(simplify_binary_with_known_imm(
                        func,
                        kind,
                        *lhs,
                        *rhs,
                        |v| known_imm(func, lattice, v),
                        |_lhs, _rhs| false,
                    ))
                }
                BinaryInstKind::Eq => {
                    let simplified = simplify_eq_zext_i1_one(func, is, lattice, *lhs, *rhs);
                    if !matches!(simplified, SimplifyAction::NoChange) {
                        return wrap_action(simplified);
                    }
                    simplify_cmp_self(func, lattice, may_be_undef, *lhs, *rhs, true)
                }
                BinaryInstKind::Ne => {
                    let simplified = simplify_ne_zext_i1_zero(func, is, lattice, *lhs, *rhs);
                    if !matches!(simplified, SimplifyAction::NoChange) {
                        return wrap_action(simplified);
                    }
                    simplify_cmp_self(func, lattice, may_be_undef, *lhs, *rhs, false)
                }
                BinaryInstKind::Lt
                | BinaryInstKind::Gt
                | BinaryInstKind::Slt
                | BinaryInstKind::Sgt => {
                    simplify_cmp_self(func, lattice, may_be_undef, *lhs, *rhs, false)
                }
                BinaryInstKind::Le
                | BinaryInstKind::Ge
                | BinaryInstKind::Sle
                | BinaryInstKind::Sge => {
                    simplify_cmp_self(func, lattice, may_be_undef, *lhs, *rhs, true)
                }
                BinaryInstKind::Uaddo
                | BinaryInstKind::Uaddsat
                | BinaryInstKind::Saddo
                | BinaryInstKind::Saddsat
                | BinaryInstKind::Umulo
                | BinaryInstKind::Umulsat
                | BinaryInstKind::Smulo
                | BinaryInstKind::Smulsat
                | BinaryInstKind::Usubo
                | BinaryInstKind::Usubsat
                | BinaryInstKind::Ssubo
                | BinaryInstKind::Ssubsat
                | BinaryInstKind::EvmUdivo
                | BinaryInstKind::EvmSdivo
                | BinaryInstKind::EvmUmodo
                | BinaryInstKind::EvmSmodo
                | BinaryInstKind::EvmUaddsat
                | BinaryInstKind::EvmSaddsat
                | BinaryInstKind::EvmUsubsat
                | BinaryInstKind::EvmSsubsat
                | BinaryInstKind::EvmUmulsat
                | BinaryInstKind::EvmSmulsat
                | BinaryInstKind::EvmExp
                | BinaryInstKind::EvmByte => SimplifyAction::NoChange,
            })
        }
        InstClassKind::Cast(kind) => {
            let values = inst.collect_values();
            let [from] = values.as_slice() else {
                return no_change_results(results_len);
            };

            let ty = match kind {
                CastInstKind::Sext => downcast::<&cast::Sext>(is, inst).map(|i| *i.ty()),
                CastInstKind::Zext => downcast::<&cast::Zext>(is, inst).map(|i| *i.ty()),
                CastInstKind::Trunc => downcast::<&cast::Trunc>(is, inst).map(|i| *i.ty()),
                CastInstKind::Bitcast => downcast::<&cast::Bitcast>(is, inst).map(|i| *i.ty()),
                CastInstKind::IntToPtr => downcast::<&cast::IntToPtr>(is, inst).map(|i| *i.ty()),
                CastInstKind::PtrToInt => downcast::<&cast::PtrToInt>(is, inst).map(|i| *i.ty()),
            };

            if let Some(ty) = ty {
                wrap_action(simplify_redundant_cast(func, kind, *from, ty))
            } else {
                no_change_results(results_len)
            }
        }
        InstClassKind::Phi | InstClassKind::Opaque => {
            if let Some(i) = downcast::<&data::Gep>(is, inst) {
                return wrap_action(simplify_gep_all_zero(func, lattice, i.values().as_slice()));
            }

            no_change_results(results_len)
        }
    }
}
