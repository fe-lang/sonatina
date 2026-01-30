use cranelift_entity::SecondaryMap;
use sonatina_ir::{
    Function, Immediate, InstDowncast, InstId, Type, Value, ValueId,
    inst::{arith, cast, cmp, logic},
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

fn same_non_undef(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
) -> bool {
    if lhs != rhs {
        return false;
    }
    if is_explicit_undef(func, lhs) {
        return false;
    }
    if func.dfg.value_imm(lhs).is_some() {
        return true;
    }

    match lattice.get(lhs) {
        Some(LatticeCell::Bot) | None => false,
        _ => true,
    }
}

fn simplify_commutative_and(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
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
    if same_non_undef(func, lattice, lhs, rhs) {
        return SimplifyResult::Copy(lhs);
    }

    SimplifyResult::NoChange
}

fn simplify_commutative_or(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
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
    if same_non_undef(func, lattice, lhs, rhs) {
        return SimplifyResult::Copy(lhs);
    }

    SimplifyResult::NoChange
}

fn simplify_commutative_xor(
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
    if same_non_undef(func, lattice, lhs, rhs) {
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
    lhs: ValueId,
    rhs: ValueId,
) -> SimplifyResult {
    let ty = func.dfg.value_ty(lhs);
    let rhs_imm = known_imm(func, lattice, rhs);
    let zero = Immediate::zero(ty);

    if same_non_undef(func, lattice, lhs, rhs) {
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

fn simplify_redundant_cast(func: &Function, from: ValueId, ty: Type) -> SimplifyResult {
    if func.dfg.value_ty(from) == ty {
        return SimplifyResult::Copy(from);
    }

    SimplifyResult::NoChange
}

fn simplify_cmp_self(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    lhs: ValueId,
    rhs: ValueId,
    result: bool,
) -> SimplifyResult {
    if same_non_undef(func, lattice, lhs, rhs) {
        return SimplifyResult::Const(Immediate::I1(result));
    }

    SimplifyResult::NoChange
}

pub(super) fn simplify_inst(
    func: &Function,
    lattice: &SecondaryMap<ValueId, LatticeCell>,
    inst_id: InstId,
) -> SimplifyResult {
    let inst = func.dfg.inst(inst_id);
    let is = func.inst_set();

    if let Some(i) = <&logic::And as InstDowncast>::downcast(is, inst) {
        return simplify_commutative_and(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = <&logic::Or as InstDowncast>::downcast(is, inst) {
        return simplify_commutative_or(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = <&logic::Xor as InstDowncast>::downcast(is, inst) {
        return simplify_commutative_xor(func, lattice, *i.lhs(), *i.rhs());
    }

    if let Some(i) = <&arith::Mul as InstDowncast>::downcast(is, inst) {
        return simplify_commutative_mul(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = <&arith::Add as InstDowncast>::downcast(is, inst) {
        return simplify_commutative_add(func, lattice, *i.lhs(), *i.rhs());
    }
    if let Some(i) = <&arith::Sub as InstDowncast>::downcast(is, inst) {
        return simplify_sub(func, lattice, *i.lhs(), *i.rhs());
    }

    if let Some(i) = <&arith::Shl as InstDowncast>::downcast(is, inst) {
        return simplify_shift(func, lattice, *i.bits(), *i.value(), true);
    }
    if let Some(i) = <&arith::Shr as InstDowncast>::downcast(is, inst) {
        return simplify_shift(func, lattice, *i.bits(), *i.value(), true);
    }
    if let Some(i) = <&arith::Sar as InstDowncast>::downcast(is, inst) {
        return simplify_shift(func, lattice, *i.bits(), *i.value(), true);
    }

    if let Some(i) = <&cast::Zext as InstDowncast>::downcast(is, inst) {
        return simplify_redundant_cast(func, *i.from(), *i.ty());
    }
    if let Some(i) = <&cast::Sext as InstDowncast>::downcast(is, inst) {
        return simplify_redundant_cast(func, *i.from(), *i.ty());
    }
    if let Some(i) = <&cast::Trunc as InstDowncast>::downcast(is, inst) {
        return simplify_redundant_cast(func, *i.from(), *i.ty());
    }
    if let Some(i) = <&cast::Bitcast as InstDowncast>::downcast(is, inst) {
        return simplify_redundant_cast(func, *i.from(), *i.ty());
    }

    if let Some(i) = <&cmp::Eq as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), true);
    }
    if let Some(i) = <&cmp::Ne as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), false);
    }

    if let Some(i) = <&cmp::Lt as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), false);
    }
    if let Some(i) = <&cmp::Gt as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), false);
    }
    if let Some(i) = <&cmp::Slt as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), false);
    }
    if let Some(i) = <&cmp::Sgt as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), false);
    }

    if let Some(i) = <&cmp::Le as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), true);
    }
    if let Some(i) = <&cmp::Ge as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), true);
    }
    if let Some(i) = <&cmp::Sle as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), true);
    }
    if let Some(i) = <&cmp::Sge as InstDowncast>::downcast(is, inst) {
        return simplify_cmp_self(func, lattice, *i.lhs(), *i.rhs(), true);
    }

    SimplifyResult::NoChange
}
