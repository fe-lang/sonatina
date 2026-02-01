use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    Function, Immediate, InstId, Type, Value, ValueId,
    inst::{arith, cast, cmp, downcast, evm, inst_set::InstSetBase, logic},
};

use super::sccp::LatticeCell;

pub(super) enum SimplifyResult {
    Const(Immediate),
    Copy(ValueId),
    NoChange,
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
) -> SimplifyResult {
    let ty = func.dfg.value_ty(lhs);
    let lhs_imm = known_imm(func, lattice, lhs);
    let rhs_imm = known_imm(func, lattice, rhs);

    let zero = Immediate::zero(ty);
    let all_one = Immediate::all_one(ty);

    if lhs_imm == Some(zero) || rhs_imm == Some(zero) {
        return SimplifyResult::Const(zero);
    }
    if lhs_imm == Some(all_one) {
        return SimplifyResult::Copy(rhs);
    }
    if rhs_imm == Some(all_one) {
        return SimplifyResult::Copy(lhs);
    }
    if same_non_undef(func, lattice, may_be_undef, lhs, rhs) {
        return SimplifyResult::Copy(lhs);
    }

    SimplifyResult::NoChange
}

fn simplify_commutative_or(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyResult {
    let ty = func.dfg.value_ty(lhs);
    let lhs_imm = known_imm(func, lattice, lhs);
    let rhs_imm = known_imm(func, lattice, rhs);

    let zero = Immediate::zero(ty);
    let all_one = Immediate::all_one(ty);

    if lhs_imm == Some(all_one) || rhs_imm == Some(all_one) {
        return SimplifyResult::Const(all_one);
    }
    if lhs_imm == Some(zero) {
        return SimplifyResult::Copy(rhs);
    }
    if rhs_imm == Some(zero) {
        return SimplifyResult::Copy(lhs);
    }
    if same_non_undef(func, lattice, may_be_undef, lhs, rhs) {
        return SimplifyResult::Copy(lhs);
    }

    SimplifyResult::NoChange
}

fn simplify_commutative_xor(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyResult {
    let ty = func.dfg.value_ty(lhs);
    let lhs_imm = known_imm(func, lattice, lhs);
    let rhs_imm = known_imm(func, lattice, rhs);

    let zero = Immediate::zero(ty);

    if lhs_imm == Some(zero) {
        return SimplifyResult::Copy(rhs);
    }
    if rhs_imm == Some(zero) {
        return SimplifyResult::Copy(lhs);
    }
    if same_non_undef(func, lattice, may_be_undef, lhs, rhs) {
        return SimplifyResult::Const(zero);
    }

    SimplifyResult::NoChange
}

fn simplify_commutative_mul(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyResult {
    let ty = func.dfg.value_ty(lhs);
    let lhs_imm = known_imm(func, lattice, lhs);
    let rhs_imm = known_imm(func, lattice, rhs);

    let zero = Immediate::zero(ty);
    let one = Immediate::one(ty);

    if lhs_imm == Some(zero) || rhs_imm == Some(zero) {
        return SimplifyResult::Const(zero);
    }
    if lhs_imm == Some(one) {
        return SimplifyResult::Copy(rhs);
    }
    if rhs_imm == Some(one) {
        return SimplifyResult::Copy(lhs);
    }

    SimplifyResult::NoChange
}

fn simplify_commutative_add(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyResult {
    let ty = func.dfg.value_ty(lhs);
    let lhs_imm = known_imm(func, lattice, lhs);
    let rhs_imm = known_imm(func, lattice, rhs);

    let zero = Immediate::zero(ty);

    if lhs_imm == Some(zero) {
        return SimplifyResult::Copy(rhs);
    }
    if rhs_imm == Some(zero) {
        return SimplifyResult::Copy(lhs);
    }

    SimplifyResult::NoChange
}

fn simplify_sub(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyResult {
    let ty = func.dfg.value_ty(lhs);
    let rhs_imm = known_imm(func, lattice, rhs);
    let zero = Immediate::zero(ty);

    if same_non_undef(func, lattice, may_be_undef, lhs, rhs) {
        return SimplifyResult::Const(zero);
    }
    if rhs_imm == Some(zero) {
        return SimplifyResult::Copy(lhs);
    }

    SimplifyResult::NoChange
}

fn simplify_shift(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    bits: ValueId,
    value: ValueId,
    allow_zero_bits_copy: bool,
) -> SimplifyResult {
    let ty = func.dfg.value_ty(value);
    let value_imm = known_imm(func, lattice, value);
    let zero = Immediate::zero(ty);

    if value_imm == Some(zero) {
        return SimplifyResult::Const(zero);
    }

    let bits_imm = known_imm(func, lattice, bits);
    if allow_zero_bits_copy && bits_imm.is_some_and(|imm| imm.is_zero()) {
        return SimplifyResult::Copy(value);
    }

    SimplifyResult::NoChange
}

fn simplify_double_not(func: &Function, is: &dyn InstSetBase, arg: ValueId) -> SimplifyResult {
    let Value::Inst { inst, .. } = func.dfg.value(arg) else {
        return SimplifyResult::NoChange;
    };

    if let Some(i) = downcast::<&logic::Not>(is, func.dfg.inst(*inst)) {
        return SimplifyResult::Copy(*i.arg());
    }

    SimplifyResult::NoChange
}

fn simplify_double_neg(func: &Function, is: &dyn InstSetBase, arg: ValueId) -> SimplifyResult {
    let Value::Inst { inst, .. } = func.dfg.value(arg) else {
        return SimplifyResult::NoChange;
    };

    if let Some(i) = downcast::<&arith::Neg>(is, func.dfg.inst(*inst)) {
        return SimplifyResult::Copy(*i.arg());
    }

    SimplifyResult::NoChange
}

fn simplify_redundant_cast(func: &Function, from: ValueId, ty: Type) -> SimplifyResult {
    if func.dfg.value_ty(from) == ty {
        return SimplifyResult::Copy(from);
    }

    SimplifyResult::NoChange
}

fn simplify_div_by_one(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyResult {
    let ty = func.dfg.value_ty(lhs);
    let rhs_imm = known_imm(func, lattice, rhs);
    let one = Immediate::one(ty);

    if rhs_imm == Some(one) {
        return SimplifyResult::Copy(lhs);
    }

    SimplifyResult::NoChange
}

fn simplify_rem_by_one(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyResult {
    let ty = func.dfg.value_ty(lhs);
    let rhs_imm = known_imm(func, lattice, rhs);
    let one = Immediate::one(ty);

    if rhs_imm == Some(one) {
        return SimplifyResult::Const(Immediate::zero(ty));
    }

    SimplifyResult::NoChange
}

fn simplify_cmp_self(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    lhs: ValueId,
    rhs: ValueId,
    result: bool,
) -> SimplifyResult {
    if same_non_undef(func, lattice, may_be_undef, lhs, rhs) {
        return SimplifyResult::Const(Immediate::I1(result));
    }

    SimplifyResult::NoChange
}

pub(super) fn simplify_inst(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    may_be_undef: &SecondaryMap<ValueId, bool>,
    inst_id: InstId,
) -> SimplifyResult {
    let inst = func.dfg.inst(inst_id);
    let is = func.inst_set();

    if let Some(i) = downcast::<&logic::Not>(is, inst) {
        return simplify_double_not(func, is, *i.arg());
    }
    if let Some(i) = downcast::<&arith::Neg>(is, inst) {
        return simplify_double_neg(func, is, *i.arg());
    }

    if let Some(i) = downcast::<&logic::And>(is, inst) {
        return simplify_commutative_and(func, lattice, may_be_undef, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&logic::Or>(is, inst) {
        return simplify_commutative_or(func, lattice, may_be_undef, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&logic::Xor>(is, inst) {
        return simplify_commutative_xor(func, lattice, may_be_undef, *i.lhs(), *i.rhs());
    }

    if let Some(i) = downcast::<&arith::Mul>(is, inst) {
        return simplify_commutative_mul(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&arith::Add>(is, inst) {
        return simplify_commutative_add(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&arith::Sub>(is, inst) {
        return simplify_sub(func, lattice, may_be_undef, *i.lhs(), *i.rhs());
    }

    if let Some(i) = downcast::<&arith::Udiv>(is, inst) {
        return simplify_div_by_one(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&arith::Sdiv>(is, inst) {
        return simplify_div_by_one(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&arith::Umod>(is, inst) {
        return simplify_rem_by_one(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&arith::Smod>(is, inst) {
        return simplify_rem_by_one(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&evm::EvmUdiv>(is, inst) {
        return simplify_div_by_one(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&evm::EvmSdiv>(is, inst) {
        return simplify_div_by_one(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&evm::EvmUmod>(is, inst) {
        return simplify_rem_by_one(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = downcast::<&evm::EvmSmod>(is, inst) {
        return simplify_rem_by_one(func, lattice, *i.lhs(), *i.rhs());
    }

    if let Some(i) = downcast::<&arith::Shl>(is, inst) {
        return simplify_shift(func, lattice, *i.bits(), *i.value(), true);
    }
    if let Some(i) = downcast::<&arith::Shr>(is, inst) {
        return simplify_shift(func, lattice, *i.bits(), *i.value(), true);
    }
    if let Some(i) = downcast::<&arith::Sar>(is, inst) {
        return simplify_shift(func, lattice, *i.bits(), *i.value(), true);
    }

    if let Some(i) = downcast::<&cast::Zext>(is, inst) {
        return simplify_redundant_cast(func, *i.from(), *i.ty());
    }
    if let Some(i) = downcast::<&cast::Sext>(is, inst) {
        return simplify_redundant_cast(func, *i.from(), *i.ty());
    }
    if let Some(i) = downcast::<&cast::Trunc>(is, inst) {
        return simplify_redundant_cast(func, *i.from(), *i.ty());
    }
    if let Some(i) = downcast::<&cast::Bitcast>(is, inst) {
        return simplify_redundant_cast(func, *i.from(), *i.ty());
    }

    if let Some(i) = downcast::<&cmp::Eq>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), true);
    }
    if let Some(i) = downcast::<&cmp::Ne>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), false);
    }

    if let Some(i) = downcast::<&cmp::Lt>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), false);
    }
    if let Some(i) = downcast::<&cmp::Gt>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), false);
    }
    if let Some(i) = downcast::<&cmp::Slt>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), false);
    }
    if let Some(i) = downcast::<&cmp::Sgt>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), false);
    }

    if let Some(i) = downcast::<&cmp::Le>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), true);
    }
    if let Some(i) = downcast::<&cmp::Ge>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), true);
    }
    if let Some(i) = downcast::<&cmp::Sle>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), true);
    }
    if let Some(i) = downcast::<&cmp::Sge>(is, inst) {
        return simplify_cmp_self(func, lattice, may_be_undef, *i.lhs(), *i.rhs(), true);
    }

    SimplifyResult::NoChange
}
