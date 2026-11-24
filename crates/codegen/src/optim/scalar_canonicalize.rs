use rustc_hash::FxHashMap;
use sonatina_ir::{
    Function, I256, Immediate, Inst, InstId, Type, U256, Value, ValueId,
    inst::{
        BinaryInstKind, CastInstKind, InstClassKind, UnaryInstKind, arith, cast, cmp, evm, logic,
    },
};

use sonatina_triple::Architecture;

use crate::{isa::evm::immediate_materialization_plan, object::lowering::StepKind};

use super::{
    simplify_expr::{
        ZextI1CompareRewrite, canonicalize_cast_chain, imm_to_u256, integral_bit_width,
        nontrivial_pow2_shift, simplify_cast, simplify_zext_i1_compare,
    },
    steps::StepLog,
};

pub struct ScalarCanonicalize {
    plans: Vec<RewritePlan>,
}

#[derive(Clone, Copy)]
enum RewritePlan {
    Copy {
        inst: InstId,
        result: ValueId,
        replacement: ValueId,
    },
    ReplaceInst {
        inst: InstId,
        replacement: InstSpec,
    },
}

#[derive(Clone, Copy)]
enum InstSpec {
    Unary {
        kind: UnaryInstKind,
        arg: ValueId,
    },
    Binary {
        kind: BinaryInstKind,
        lhs: Operand,
        rhs: Operand,
    },
    Cast {
        kind: CastInstKind,
        from: ValueId,
        ty: Type,
    },
}

#[derive(Clone, Copy)]
enum Operand {
    Value(ValueId),
    Imm(Immediate),
}

impl ScalarCanonicalize {
    pub fn new() -> Self {
        Self { plans: Vec::new() }
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        self.run_with_steps(func, None)
    }

    pub(crate) fn run_with_steps(
        &mut self,
        func: &mut Function,
        mut steps: Option<&mut StepLog>,
    ) -> bool {
        let mut changed = false;

        loop {
            self.plans.clear();
            let blocks: Vec<_> = func.layout.iter_block().collect();
            for block in blocks {
                for inst in func.layout.iter_inst(block) {
                    if let Some(plan) = self.plan_inst(func, inst) {
                        self.plans.push(plan);
                    }
                }
            }

            if self.plans.is_empty() {
                return changed;
            }

            changed = true;
            let resolved = resolve_copy_replacements(&self.plans);
            for &plan in &self.plans {
                if let RewritePlan::ReplaceInst { .. } = plan {
                    apply_replace_plan(func, plan, &resolved);
                }
            }

            for &plan in &self.plans {
                if let RewritePlan::Copy { .. } = plan {
                    apply_copy_plan(func, plan, &resolved);
                }
            }

            for &plan in &self.plans {
                if let RewritePlan::Copy { .. } = plan {
                    remove_rewritten_inst(func, plan.inst());
                }
            }

            prune_dead_pure_insts(func);
            StepLog::step(&mut steps, StepKind::ScalarCanonicalize, func, None);
        }
    }

    fn plan_inst(&self, func: &Function, inst: InstId) -> Option<RewritePlan> {
        let [result] = func.dfg.inst_results(inst) else {
            return None;
        };
        let inst_data = func.dfg.inst(inst);
        match inst_data.kind() {
            InstClassKind::Binary(kind) => {
                let values = inst_data.collect_values();
                let [lhs, rhs] = values.as_slice() else {
                    return None;
                };
                if let Some(rewrite) = simplify_zext_i1_compare(func, kind, *lhs, *rhs, |value| {
                    func.dfg.value_imm(value)
                }) {
                    return Some(match rewrite {
                        ZextI1CompareRewrite::Copy(replacement) => RewritePlan::Copy {
                            inst,
                            result: *result,
                            replacement,
                        },
                        ZextI1CompareRewrite::IsZero(arg) => RewritePlan::ReplaceInst {
                            inst,
                            replacement: InstSpec::Unary {
                                kind: UnaryInstKind::IsZero,
                                arg,
                            },
                        },
                    });
                }

                canonicalize_binary_inst(func, inst, kind, *lhs, *rhs)
                    .filter(|&replacement| supports_inst_spec(func, replacement))
                    .map(|replacement| RewritePlan::ReplaceInst { inst, replacement })
            }
            InstClassKind::Cast(kind) => {
                let values = inst_data.collect_values();
                let [from] = values.as_slice() else {
                    return None;
                };
                let ty = func.dfg.value_ty(*result);
                if let super::simplify_expr::SimplifiedResult::Copy(replacement) =
                    simplify_cast(func, kind, *from, ty)
                {
                    return Some(RewritePlan::Copy {
                        inst,
                        result: *result,
                        replacement,
                    });
                }

                canonicalize_cast_chain(func, kind, *from, ty)
                    .map(|(kind, from, ty)| InstSpec::Cast { kind, from, ty })
                    .filter(|&replacement| supports_inst_spec(func, replacement))
                    .map(|replacement| RewritePlan::ReplaceInst { inst, replacement })
            }
            InstClassKind::Unary(UnaryInstKind::Not) => {
                let value = inst_data.collect_values()[0];
                fold_complemented_arithmetic(func, inst, value)
                    .filter(|&replacement| supports_inst_spec(func, replacement))
                    .map(|replacement| RewritePlan::ReplaceInst { inst, replacement })
            }
            InstClassKind::Unary(UnaryInstKind::IsZero) => {
                let values = inst_data.collect_values();
                let [value] = values.as_slice() else {
                    return None;
                };
                let ty = func.dfg.value_ty(*value);
                if !ty.is_integral() {
                    return None;
                }
                fold_constant_comparison(
                    func,
                    inst,
                    BinaryInstKind::Eq,
                    *value,
                    Immediate::zero(ty),
                )
                .filter(|&replacement| supports_inst_spec(func, replacement))
                .map(|replacement| RewritePlan::ReplaceInst { inst, replacement })
            }
            InstClassKind::Opaque if func.dfg.value_ty(*result) == Type::I256 => {
                use sonatina_ir::inst::downcast;
                let is = func.inst_set();
                let (lhs, rhs, modulus, identity) =
                    if let Some(op) = downcast::<&evm::EvmAddMod>(is, inst_data) {
                        (
                            *op.lhs(),
                            *op.rhs(),
                            *op.modulus(),
                            Immediate::zero(Type::I256),
                        )
                    } else {
                        let op = downcast::<&evm::EvmMulMod>(is, inst_data)?;
                        (
                            *op.lhs(),
                            *op.rhs(),
                            *op.modulus(),
                            Immediate::one(Type::I256),
                        )
                    };
                let value = if func.dfg.value_imm(lhs) == Some(identity) {
                    rhs
                } else if func.dfg.value_imm(rhs) == Some(identity) {
                    lhs
                } else {
                    return None;
                };
                let replacement = InstSpec::Binary {
                    kind: BinaryInstKind::EvmUmod,
                    lhs: Operand::Value(value),
                    rhs: Operand::Value(modulus),
                };
                supports_inst_spec(func, replacement)
                    .then_some(RewritePlan::ReplaceInst { inst, replacement })
            }
            InstClassKind::Unary(_) | InstClassKind::Phi | InstClassKind::Opaque => None,
        }
    }
}

impl Default for ScalarCanonicalize {
    fn default() -> Self {
        Self::new()
    }
}

fn canonicalize_binary_inst(
    func: &Function,
    inst: InstId,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    if let Some(rewrite) = cancel_common_operand(func, inst, kind, lhs, rhs) {
        return Some(rewrite);
    }
    if let Some(rewrite) = fold_bitwise_pair(func, inst, kind, lhs, rhs) {
        return Some(rewrite);
    }
    if kind == BinaryInstKind::Sub
        && func.dfg.value_ty(lhs).is_integral()
        && (func.ctx().triple.architecture != Architecture::Evm
            || func.dfg.value_ty(lhs) == Type::I256)
        && let Some(x) = local_not_source(func, inst, lhs)
        && let Some(y) = local_not_source(func, inst, rhs)
    {
        return Some(InstSpec::Binary {
            kind,
            lhs: Operand::Value(y),
            rhs: Operand::Value(x),
        });
    }
    if let Some(rewrite) = fold_shifted_byte(func, inst, kind, lhs, rhs) {
        return Some(rewrite);
    }
    if let Some(rewrite) = fold_dynamic_pow2_division(func, inst, kind, lhs, rhs) {
        return Some(rewrite);
    }
    if let Some(rewrite) = canonicalize_evm_byte(func, inst, kind, lhs, rhs) {
        return Some(rewrite);
    }
    if let Some(rewrite) = canonicalize_signed_top_field(func, inst, kind, lhs, rhs) {
        return Some(rewrite);
    }
    if let Some(rewrite) = canonicalize_evm_signextend(func, inst, kind, lhs, rhs) {
        return Some(rewrite);
    }
    if matches!(kind, BinaryInstKind::Eq | BinaryInstKind::Ne) {
        let operands = func
            .dfg
            .value_imm(rhs)
            .map(|bound| (lhs, bound))
            .or_else(|| func.dfg.value_imm(lhs).map(|bound| (rhs, bound)));
        if let Some((value, bound)) = operands
            && let Some(rewrite) = fold_constant_comparison(func, inst, kind, value, bound)
        {
            return Some(rewrite);
        }
    }
    if let Some(rewrite) = fold_shifted_sign_test(func, inst, kind, lhs, rhs) {
        return Some(rewrite);
    }
    match kind {
        BinaryInstKind::Eq
            if func.dfg.value_ty(lhs).is_integral() && func.dfg.value_ty(rhs).is_integral() =>
        {
            if func.dfg.value_imm(lhs).is_some_and(Immediate::is_zero) {
                return Some(InstSpec::Unary {
                    kind: UnaryInstKind::IsZero,
                    arg: rhs,
                });
            }
            if func.dfg.value_imm(rhs).is_some_and(Immediate::is_zero) {
                return Some(InstSpec::Unary {
                    kind: UnaryInstKind::IsZero,
                    arg: lhs,
                });
            }
            None
        }
        BinaryInstKind::Add => {
            if let Some(arg) = neg_source(func, rhs) {
                return Some(InstSpec::Binary {
                    kind: BinaryInstKind::Sub,
                    lhs: Operand::Value(lhs),
                    rhs: Operand::Value(arg),
                });
            }
            if let Some(arg) = neg_source(func, lhs) {
                return Some(InstSpec::Binary {
                    kind: BinaryInstKind::Sub,
                    lhs: Operand::Value(rhs),
                    rhs: Operand::Value(arg),
                });
            }
            None
        }
        BinaryInstKind::Sub => neg_source(func, rhs).map(|arg| InstSpec::Binary {
            kind: BinaryInstKind::Add,
            lhs: Operand::Value(lhs),
            rhs: Operand::Value(arg),
        }),
        BinaryInstKind::EvmExp if func.dfg.value_ty(lhs) == Type::I256 => {
            let two = Immediate::I256(I256::from(2));
            if func.dfg.value_imm(lhs) == Some(two) {
                return Some(InstSpec::Binary {
                    kind: BinaryInstKind::Shl,
                    lhs: Operand::Value(rhs),
                    rhs: Operand::Imm(Immediate::one(Type::I256)),
                });
            }
            (func.dfg.value_imm(rhs) == Some(two)).then_some(InstSpec::Binary {
                kind: BinaryInstKind::Mul,
                lhs: Operand::Value(lhs),
                rhs: Operand::Value(lhs),
            })
        }
        BinaryInstKind::Mul => mul_pow2_rewrite(func, lhs, rhs),
        BinaryInstKind::Shl | BinaryInstKind::Shr | BinaryInstKind::Sar => {
            merge_shifts(func, kind, lhs, rhs)
        }
        BinaryInstKind::Udiv
        | BinaryInstKind::EvmUdiv
        | BinaryInstKind::Umod
        | BinaryInstKind::EvmUmod => {
            if matches!(kind, BinaryInstKind::Udiv | BinaryInstKind::EvmUdiv)
                && let Some(rewrite) = merge_unsigned_divisions(func, kind, lhs, rhs)
            {
                return Some(rewrite);
            }
            let divisor = func.dfg.value_imm(rhs)?;
            let shift = nontrivial_pow2_shift(divisor)?;
            Some(
                if matches!(kind, BinaryInstKind::Udiv | BinaryInstKind::EvmUdiv) {
                    InstSpec::Binary {
                        kind: BinaryInstKind::Shr,
                        lhs: Operand::Imm(Immediate::from_i256(I256::from(shift), divisor.ty())),
                        rhs: Operand::Value(lhs),
                    }
                } else {
                    InstSpec::Binary {
                        kind: BinaryInstKind::And,
                        lhs: Operand::Value(lhs),
                        rhs: Operand::Imm(divisor - Immediate::one(divisor.ty())),
                    }
                },
            )
        }
        _ => None,
    }
}

// Keep matched intermediates local and single-use so rewriting removes work
// without extending dependencies across block boundaries.
fn local_single_use_producer(func: &Function, root: InstId, value: ValueId) -> Option<InstId> {
    let producer = func.dfg.value_inst(value)?;
    (func.dfg.users_num(value) == 1
        && func.layout.inst_block(producer) == func.layout.inst_block(root))
    .then_some(producer)
}

/// Cancel identical injective operations on both sides of an equality test.
fn cancel_common_operand(
    func: &Function,
    inst: InstId,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    use BinaryInstKind::{Add, Eq, Mul, Ne, Sub, Xor};
    if !matches!(kind, Eq | Ne) || !func.dfg.value_ty(lhs).is_integral() {
        return None;
    }
    let left = func.dfg.inst(local_single_use_producer(func, inst, lhs)?);
    let right = func.dfg.inst(local_single_use_producer(func, inst, rhs)?);
    let InstClassKind::Binary(op) = left.kind() else {
        return None;
    };
    if right.kind() != left.kind() || !matches!(op, Add | Sub | Xor | Mul) {
        return None;
    }
    let [a, b] = left.collect_values()[..] else {
        return None;
    };
    let [c, d] = right.collect_values()[..] else {
        return None;
    };
    let (key, x, y) = if a == c {
        (a, b, d)
    } else if b == d {
        (b, a, c)
    } else if op != Sub && a == d {
        (a, b, c)
    } else if op != Sub && b == c {
        (b, a, d)
    } else {
        return None;
    };
    if op == Mul {
        // Only odd factors are invertible modulo 2^width.
        let k = func.dfg.value_imm(key)?;
        if (k & Immediate::one(k.ty())).is_zero() {
            return None;
        }
    }
    Some(InstSpec::Binary {
        kind,
        lhs: Operand::Value(x),
        rhs: Operand::Value(y),
    })
}

fn fold_bitwise_pair(
    func: &Function,
    inst: InstId,
    outer: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    use BinaryInstKind::{And, Or, Xor};
    if !matches!(outer, And | Or | Xor) || !func.dfg.value_ty(lhs).is_integral() {
        return None;
    }
    let left = local_single_use_producer(func, inst, lhs)?;
    let right = local_single_use_producer(func, inst, rhs)?;
    let InstClassKind::Binary(a) = func.dfg.inst(left).kind() else {
        return None;
    };
    let InstClassKind::Binary(b) = func.dfg.inst(right).kind() else {
        return None;
    };
    if !matches!(a, And | Or | Xor) || !matches!(b, And | Or | Xor) {
        return None;
    }
    let [x, y] = func.dfg.inst(left).collect_values()[..] else {
        return None;
    };
    let [u, v] = func.dfg.inst(right).collect_values()[..] else {
        return None;
    };
    if !((x == u && y == v) || (x == v && y == u)) {
        return None;
    }
    let kind = match (outer, a, b) {
        (And, And, Or) | (And, Or, And) => And,
        (And, Or, Xor) | (And, Xor, Or) => Xor,
        (Or, And, Or | Xor) | (Or, Or | Xor, And) | (Or, Or, Xor) | (Or, Xor, Or) => Or,
        (Xor, And, Or) | (Xor, Or, And) => Xor,
        (Xor, And, Xor) | (Xor, Xor, And) => Or,
        (Xor, Or, Xor) | (Xor, Xor, Or) => And,
        _ => return None,
    };
    Some(InstSpec::Binary {
        kind,
        lhs: Operand::Value(x),
        rhs: Operand::Value(y),
    })
}

/// Arithmetic right shifts preserve the sign, including oversized shifts.
/// Match constant shift counts.
fn fold_shifted_sign_test(
    func: &Function,
    inst: InstId,
    mut kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    if !matches!(
        kind,
        BinaryInstKind::Slt | BinaryInstKind::Sle | BinaryInstKind::Sgt | BinaryInstKind::Sge
    ) {
        return None;
    }
    let (shifted, bound) = if let Some(bound) = func.dfg.value_imm(rhs) {
        (lhs, bound)
    } else {
        let bound = func.dfg.value_imm(lhs)?;
        kind = match kind {
            BinaryInstKind::Slt => BinaryInstKind::Sgt,
            BinaryInstKind::Sgt => BinaryInstKind::Slt,
            BinaryInstKind::Sle => BinaryInstKind::Sge,
            BinaryInstKind::Sge => BinaryInstKind::Sle,
            _ => unreachable!(),
        };
        (rhs, bound)
    };
    if !bound.ty().is_integral() {
        return None;
    }
    let sign_test = match kind {
        BinaryInstKind::Slt | BinaryInstKind::Sge => bound.is_zero(),
        BinaryInstKind::Sgt | BinaryInstKind::Sle => bound == Immediate::all_one(bound.ty()),
        _ => unreachable!(),
    };
    if !sign_test {
        return None;
    }
    let producer = func.dfg.value_inst(shifted)?;
    if func.dfg.inst(producer).kind() != InstClassKind::Binary(BinaryInstKind::Sar)
        || func.dfg.users_num(shifted) != 1
        || func.layout.inst_block(producer) != func.layout.inst_block(inst)
    {
        return None;
    }
    let [count, input] = func.dfg.inst(producer).collect_values()[..] else {
        return None;
    };
    func.dfg.value_imm(count)?;
    Some(InstSpec::Binary {
        kind,
        lhs: Operand::Value(input),
        rhs: Operand::Imm(bound),
    })
}

/// Move an invertible constant operation into an equality's bound.
/// Keep shared producers and cross-block live ranges, and reject costly bounds.
fn fold_constant_comparison(
    func: &Function,
    inst: InstId,
    kind: BinaryInstKind,
    value: ValueId,
    bound: Immediate,
) -> Option<InstSpec> {
    let ty = func.dfg.value_ty(value);
    if !ty.is_integral() || bound.ty() != ty {
        return None;
    }
    let producer = func.dfg.value_inst(value)?;
    if func.dfg.users_num(value) != 1
        || func.layout.inst_block(producer) != func.layout.inst_block(inst)
    {
        return None;
    }
    let inner_kind = func.dfg.inst(producer).kind();
    if bound.is_zero()
        && matches!(
            inner_kind,
            InstClassKind::Binary(BinaryInstKind::Udiv | BinaryInstKind::EvmUdiv)
        )
    {
        let [lhs, rhs] = func.dfg.inst(producer).collect_values()[..] else {
            return None;
        };
        // The unsigned quotient is zero exactly when the dividend is below the divisor.
        let divisor = func.dfg.value_imm(rhs)?;
        // Preserve division by one and the compact shift spelling for powers of two.
        // A comparison can require a much wider PUSH without saving runtime gas.
        if divisor.is_zero()
            || divisor == Immediate::one(divisor.ty())
            || nontrivial_pow2_shift(divisor).is_some()
        {
            return None;
        }
        return Some(InstSpec::Binary {
            kind: if kind == BinaryInstKind::Eq {
                BinaryInstKind::Lt
            } else {
                BinaryInstKind::Gt
            },
            lhs: Operand::Value(lhs),
            rhs: Operand::Imm(if kind == BinaryInstKind::Eq {
                divisor
            } else {
                divisor - Immediate::one(divisor.ty())
            }),
        });
    }

    if !matches!(
        inner_kind,
        InstClassKind::Binary(BinaryInstKind::Add | BinaryInstKind::Sub | BinaryInstKind::Xor)
    ) {
        return None;
    }
    let [lhs, rhs] = func.dfg.inst(producer).collect_values()[..] else {
        return None;
    };
    let original_bound = bound;
    let (input, constant, bound) = if let Some(c) = func.dfg.value_imm(rhs) {
        let new_bound = match inner_kind {
            InstClassKind::Binary(BinaryInstKind::Add) => bound - c,
            InstClassKind::Binary(BinaryInstKind::Sub) => bound + c,
            InstClassKind::Binary(BinaryInstKind::Xor) => bound ^ c,
            _ => unreachable!(),
        };
        (lhs, c, new_bound)
    } else {
        let c = func.dfg.value_imm(lhs)?;
        let new_bound = match inner_kind {
            InstClassKind::Binary(BinaryInstKind::Add) => bound - c,
            InstClassKind::Binary(BinaryInstKind::Sub) => c - bound,
            InstClassKind::Binary(BinaryInstKind::Xor) => bound ^ c,
            _ => unreachable!(),
        };
        (rhs, c, new_bound)
    };
    // Price the actual EVM materialization, including NOT and shifted constants.
    // Stay no more expensive than the larger original constant in either metric.
    if func.ctx().triple.architecture == Architecture::Evm {
        if ty != Type::I256 {
            return None;
        }
        let a = immediate_materialization_plan(original_bound).cost();
        let b = immediate_materialization_plan(constant).cost();
        let new = immediate_materialization_plan(bound).cost();
        if new.gas > a.gas.max(b.gas) || new.bytes > a.bytes.max(b.bytes) {
            return None;
        }
    }
    Some(InstSpec::Binary {
        kind,
        lhs: Operand::Value(input),
        rhs: Operand::Imm(bound),
    })
}

fn local_not_source(func: &Function, root: InstId, value: ValueId) -> Option<ValueId> {
    let producer = local_single_use_producer(func, root, value)?;
    if func.dfg.inst(producer).kind() != InstClassKind::Unary(UnaryInstKind::Not) {
        return None;
    }
    Some(func.dfg.inst(producer).collect_values()[0])
}

fn fold_complemented_arithmetic(func: &Function, inst: InstId, value: ValueId) -> Option<InstSpec> {
    let ty = func.dfg.value_ty(value);
    if !ty.is_integral()
        || (func.ctx().triple.architecture == Architecture::Evm && ty != Type::I256)
    {
        return None;
    }
    let producer = local_single_use_producer(func, inst, value)?;
    let kind = func.dfg.inst(producer).kind();
    let [lhs, rhs] = func.dfg.inst(producer).collect_values()[..] else {
        return None;
    };
    match kind {
        InstClassKind::Binary(BinaryInstKind::Sub)
            if func.dfg.value_imm(rhs) == Some(Immediate::one(ty)) =>
        {
            // ~((1 << n) - 1) = (-1) << n, including oversized counts.
            if let Some(shift) = local_single_use_producer(func, inst, lhs)
                && func.dfg.inst(shift).kind() == InstClassKind::Binary(BinaryInstKind::Shl)
            {
                let values = func.dfg.inst(shift).collect_values();
                if func.dfg.value_imm(values[1]) == Some(Immediate::one(ty)) {
                    return Some(InstSpec::Binary {
                        kind: BinaryInstKind::Shl,
                        lhs: Operand::Value(values[0]),
                        rhs: Operand::Imm(Immediate::from_i256(I256::from(-1), ty)),
                    });
                }
            }
            Some(InstSpec::Binary {
                kind: BinaryInstKind::Sub,
                lhs: Operand::Imm(Immediate::zero(ty)),
                rhs: Operand::Value(lhs),
            })
        }
        InstClassKind::Binary(BinaryInstKind::Add | BinaryInstKind::Sub) => {
            let (x, y) = if let Some(x) = local_not_source(func, inst, lhs) {
                (x, rhs)
            } else if kind == InstClassKind::Binary(BinaryInstKind::Add) {
                (local_not_source(func, inst, rhs)?, lhs)
            } else {
                return None;
            };
            Some(InstSpec::Binary {
                kind: if kind == InstClassKind::Binary(BinaryInstKind::Add) {
                    BinaryInstKind::Sub
                } else {
                    BinaryInstKind::Add
                },
                lhs: Operand::Value(x),
                rhs: Operand::Value(y),
            })
        }
        _ => None,
    }
}

/// Select the original byte directly instead of shifting the whole word.
/// Keep shared/cross-block producers and indexes selecting shifted-in zeros.
fn fold_shifted_byte(
    func: &Function,
    inst: InstId,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    if kind != BinaryInstKind::EvmByte
        || func.ctx().triple.architecture != Architecture::Evm
        || func.dfg.value_ty(lhs) != Type::I256
        || func.dfg.value_ty(rhs) != Type::I256
    {
        return None;
    }
    let index = imm_to_u256(func.dfg.value_imm(lhs)?);
    if index >= U256::from(32) {
        return None;
    }
    let producer = func.dfg.value_inst(rhs)?;
    let producer_kind = func.dfg.inst(producer).kind();
    if !matches!(
        producer_kind,
        InstClassKind::Binary(BinaryInstKind::Shl | BinaryInstKind::Shr)
    ) || func.dfg.users_num(rhs) != 1
        || func.layout.inst_block(producer) != func.layout.inst_block(inst)
    {
        return None;
    }
    let [count, word] = func.dfg.inst(producer).collect_values()[..] else {
        return None;
    };
    let count = imm_to_u256(func.dfg.value_imm(count)?);
    if count >= U256::from(256) || count % U256::from(8) != U256::zero() {
        return None;
    }
    let bytes = count / U256::from(8);
    let index = match producer_kind {
        InstClassKind::Binary(BinaryInstKind::Shl) if index + bytes < U256::from(32) => {
            index + bytes
        }
        InstClassKind::Binary(BinaryInstKind::Shr) if index >= bytes => index - bytes,
        _ => return None,
    };
    Some(InstSpec::Binary {
        kind: BinaryInstKind::EvmByte,
        lhs: Operand::Imm(Immediate::from_i256(I256::from(index), Type::I256)),
        rhs: Operand::Value(word),
    })
}

/// EVM division by `1 << n` is `x >> n`, including n >= 256 (both yield zero).
/// Keep shared/cross-block divisors, including those still used by a zero check.
fn fold_dynamic_pow2_division(
    func: &Function,
    inst: InstId,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    if kind != BinaryInstKind::EvmUdiv
        || func.ctx().triple.architecture != Architecture::Evm
        || func.dfg.value_ty(lhs) != Type::I256
        || func.dfg.value_ty(rhs) != Type::I256
    {
        return None;
    }
    let producer = func.dfg.value_inst(rhs)?;
    if func.dfg.inst(producer).kind() != InstClassKind::Binary(BinaryInstKind::Shl)
        || func.dfg.users_num(rhs) != 1
        || func.layout.inst_block(producer) != func.layout.inst_block(inst)
    {
        return None;
    }
    let [count, one] = func.dfg.inst(producer).collect_values()[..] else {
        return None;
    };
    if func.dfg.value_imm(one) != Some(Immediate::one(Type::I256)) {
        return None;
    }
    Some(InstSpec::Binary {
        kind: BinaryInstKind::Shr,
        lhs: Operand::Value(count),
        rhs: Operand::Value(lhs),
    })
}

/// Select BYTE when a byte-aligned shift and mask extract one byte.
/// Keep shared or cross-block producers to avoid extending source liveness.
fn canonicalize_evm_byte(
    func: &Function,
    inst: InstId,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    if func.ctx().triple.architecture != Architecture::Evm
        || func.dfg.value_ty(lhs) != Type::I256
        || func.dfg.value_ty(rhs) != Type::I256
    {
        return None;
    }
    // The top byte needs no mask; BYTE 0 also saves a PUSH immediate byte.
    if kind == BinaryInstKind::Shr
        && func
            .dfg
            .value_imm(lhs)
            .is_some_and(|imm| imm_to_u256(imm) == U256::from(248))
    {
        return Some(InstSpec::Binary {
            kind: BinaryInstKind::EvmByte,
            lhs: Operand::Imm(Immediate::zero(Type::I256)),
            rhs: Operand::Value(rhs),
        });
    }
    if kind != BinaryInstKind::And {
        return None;
    }
    let is_byte_mask = |value| {
        func.dfg
            .value_imm(value)
            .is_some_and(|imm| imm_to_u256(imm) == U256::from(255))
    };
    let shifted = if is_byte_mask(rhs) {
        lhs
    } else if is_byte_mask(lhs) {
        rhs
    } else {
        return None;
    };
    let producer = func.dfg.value_inst(shifted)?;
    let shift = func.dfg.downcast::<&arith::Shr>(producer)?;
    if func.dfg.users_num(shifted) != 1
        || func.layout.inst_block(producer) != func.layout.inst_block(inst)
    {
        return None;
    }
    let count = imm_to_u256(func.dfg.value_imm(*shift.bits())?);
    if count == U256::zero() || count > U256::from(248) || count % U256::from(8) != U256::zero() {
        return None;
    }
    Some(InstSpec::Binary {
        kind: BinaryInstKind::EvmByte,
        lhs: Operand::Imm(Immediate::from_i256(
            I256::from(31 - count.as_usize() / 8),
            Type::I256,
        )),
        rhs: Operand::Value(*shift.value()),
    })
}

/// A signed field ending at bit 255 is one arithmetic shift of the word.
/// BYTE 0 is also a spelling of SHR 248 after byte-extraction selection.
fn canonicalize_signed_top_field(
    func: &Function,
    inst: InstId,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    if kind != BinaryInstKind::EvmSignExtend
        || func.ctx().triple.architecture != Architecture::Evm
        || func.dfg.value_ty(lhs) != Type::I256
        || func.dfg.value_ty(rhs) != Type::I256
    {
        return None;
    }
    let byte = imm_to_u256(func.dfg.value_imm(lhs)?);
    if byte >= U256::from(31) {
        return None;
    }
    let producer = func.dfg.value_inst(rhs)?;
    if func.dfg.users_num(rhs) != 1
        || func.layout.inst_block(producer) != func.layout.inst_block(inst)
    {
        return None;
    }
    let [count, word] = func.dfg.inst(producer).collect_values()[..] else {
        return None;
    };
    let count = imm_to_u256(func.dfg.value_imm(count)?);
    let shift = 248 - byte.as_usize() * 8;
    match func.dfg.inst(producer).kind() {
        InstClassKind::Binary(BinaryInstKind::Shr) if count == U256::from(shift) => {}
        InstClassKind::Binary(BinaryInstKind::EvmByte) if byte.is_zero() && count.is_zero() => {}
        _ => return None,
    }
    Some(InstSpec::Binary {
        kind: BinaryInstKind::Sar,
        lhs: Operand::Imm(Immediate::from_i256(I256::from(shift), Type::I256)),
        rhs: Operand::Value(word),
    })
}

/// Select SIGNEXTEND for byte-aligned left/arithmetic-right shift pairs.
/// Keep shared or cross-block producers to avoid extending source liveness.
fn canonicalize_evm_signextend(
    func: &Function,
    inst: InstId,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    if func.ctx().triple.architecture != Architecture::Evm
        || kind != BinaryInstKind::Sar
        || func.dfg.value_ty(lhs) != Type::I256
        || func.dfg.value_ty(rhs) != Type::I256
    {
        return None;
    }
    let count = imm_to_u256(func.dfg.value_imm(lhs)?);
    if count == U256::zero() || count > U256::from(248) || count % U256::from(8) != U256::zero() {
        return None;
    }
    let producer = func.dfg.value_inst(rhs)?;
    let shift = func.dfg.downcast::<&arith::Shl>(producer)?;
    if imm_to_u256(func.dfg.value_imm(*shift.bits())?) != count
        || func.dfg.users_num(rhs) != 1
        || func.layout.inst_block(producer) != func.layout.inst_block(inst)
    {
        return None;
    }
    Some(InstSpec::Binary {
        kind: BinaryInstKind::EvmSignExtend,
        lhs: Operand::Imm(Immediate::from_i256(
            I256::from(31 - count.as_usize() / 8),
            Type::I256,
        )),
        rhs: Operand::Value(*shift.value()),
    })
}

/// Unsigned division rounds down, so (x / a) / b equals x / (a * b).
/// Keep zero divisors and products that do not fit the original width.
/// Require a single user so the rewrite removes the inner division.
fn merge_unsigned_divisions(
    func: &Function,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
    let outer = func.dfg.value_imm(rhs)?;
    let inner_inst = func.dfg.value_inst(lhs)?;
    if func.dfg.inst(inner_inst).kind() != InstClassKind::Binary(kind)
        || func.dfg.users(lhs).count() != 1
    {
        return None;
    }
    let [value, inner_divisor] = func.dfg.inst(inner_inst).collect_values()[..] else {
        return None;
    };
    let inner = func.dfg.value_imm(inner_divisor)?;
    // Power-of-two divisors already become cheap shifts with small constants.
    // Combining them can replace that compact spelling with a large PUSH.
    if outer.is_zero()
        || inner.is_zero()
        || nontrivial_pow2_shift(inner).is_some()
        || nontrivial_pow2_shift(outer).is_some()
    {
        return None;
    }
    let (product, overflow) = imm_to_u256(inner).overflowing_mul(imm_to_u256(outer));
    let width = integral_bit_width(outer.ty())?;
    if overflow || (width < 256 && product >= (U256::one() << width)) {
        return None;
    }
    Some(InstSpec::Binary {
        kind,
        lhs: Operand::Value(value),
        rhs: Operand::Imm(Immediate::from_i256(I256::from(product), outer.ty())),
    })
}

/// `shr a (shr b x)` is `shr (a + b) x`, and likewise for `shl` and `sar`. A
/// total past the width becomes the width, or `width - 1` for `sar`, which
/// shifts the same way: every bit out, or the sign into every bit.
fn merge_shifts(
    func: &Function,
    kind: BinaryInstKind,
    count: ValueId,
    value: ValueId,
) -> Option<InstSpec> {
    let outer = imm_to_u256(func.dfg.value_imm(count)?);
    let inner = func.dfg.value_inst(value)?;
    if func.dfg.inst(inner).kind() != InstClassKind::Binary(kind) {
        return None;
    }
    let [inner_count, x] = func.dfg.inst(inner).collect_values()[..] else {
        return None;
    };
    let inner = imm_to_u256(func.dfg.value_imm(inner_count)?);
    let ty = func.dfg.value_ty(count);
    let width = U256::from(integral_bit_width(ty)?);
    let limit = if kind == BinaryInstKind::Sar {
        width - U256::one()
    } else {
        width
    };
    let total = (outer.min(width) + inner.min(width)).min(limit);
    Some(InstSpec::Binary {
        kind,
        lhs: Operand::Imm(Immediate::from_i256(I256::from(total.as_usize()), ty)),
        rhs: Operand::Value(x),
    })
}

fn neg_source(func: &Function, value: ValueId) -> Option<ValueId> {
    let Value::Inst { inst, .. } = func.dfg.value(value) else {
        return None;
    };
    if func.dfg.inst(*inst).kind() != InstClassKind::Unary(UnaryInstKind::Neg) {
        return None;
    }
    let values = func.dfg.inst(*inst).collect_values();
    let [arg] = values.as_slice() else {
        return None;
    };
    Some(*arg)
}

fn mul_pow2_rewrite(func: &Function, lhs: ValueId, rhs: ValueId) -> Option<InstSpec> {
    if let Some(imm) = func.dfg.value_imm(lhs)
        && let Some(shift) = nontrivial_pow2_shift(imm)
    {
        return Some(InstSpec::Binary {
            kind: BinaryInstKind::Shl,
            lhs: Operand::Imm(Immediate::from_i256(I256::from(shift), imm.ty())),
            rhs: Operand::Value(rhs),
        });
    }
    if let Some(imm) = func.dfg.value_imm(rhs)
        && let Some(shift) = nontrivial_pow2_shift(imm)
    {
        return Some(InstSpec::Binary {
            kind: BinaryInstKind::Shl,
            lhs: Operand::Imm(Immediate::from_i256(I256::from(shift), imm.ty())),
            rhs: Operand::Value(lhs),
        });
    }
    None
}

fn resolve_copy_replacements(plans: &[RewritePlan]) -> FxHashMap<ValueId, ValueId> {
    let rewrites: FxHashMap<_, _> = plans
        .iter()
        .filter_map(|plan| match *plan {
            RewritePlan::Copy {
                result,
                replacement,
                ..
            } => Some((result, replacement)),
            RewritePlan::ReplaceInst { .. } => None,
        })
        .collect();
    let mut resolved = FxHashMap::default();

    for &result in rewrites.keys() {
        resolve_copy_replacement(result, &rewrites, &mut resolved);
    }

    resolved
}

fn resolve_copy_replacement(
    result: ValueId,
    rewrites: &FxHashMap<ValueId, ValueId>,
    resolved: &mut FxHashMap<ValueId, ValueId>,
) -> ValueId {
    if let Some(&replacement) = resolved.get(&result) {
        return replacement;
    }

    let replacement = rewrites[&result];
    let replacement = if rewrites.contains_key(&replacement) {
        debug_assert_ne!(replacement, result, "rewrite cycle on {result:?}");
        resolve_copy_replacement(replacement, rewrites, resolved)
    } else {
        replacement
    };
    resolved.insert(result, replacement);
    replacement
}

fn apply_replace_plan(
    func: &mut Function,
    plan: RewritePlan,
    resolved: &FxHashMap<ValueId, ValueId>,
) {
    let RewritePlan::ReplaceInst { inst, replacement } = plan else {
        return;
    };
    let Some(replacement) = build_inst(func, rebase_inst_spec(replacement, resolved)) else {
        return;
    };
    func.dfg.replace_inst(inst, replacement);
}

fn apply_copy_plan(func: &mut Function, plan: RewritePlan, resolved: &FxHashMap<ValueId, ValueId>) {
    let RewritePlan::Copy { result, .. } = plan else {
        return;
    };
    if func.dfg.has_value(result) {
        func.dfg.change_to_alias(result, resolved[&result]);
    }
}

fn build_inst(func: &mut Function, replacement: InstSpec) -> Option<Box<dyn Inst>> {
    let is = func.inst_set();
    match replacement {
        InstSpec::Unary {
            kind: UnaryInstKind::IsZero,
            arg,
        } => Some(Box::new(cmp::IsZero::new(is.has_is_zero()?, arg))),
        InstSpec::Unary { .. } => None,
        InstSpec::Binary { kind, lhs, rhs } => {
            let lhs = materialize_operand(func, lhs);
            let rhs = materialize_operand(func, rhs);
            match kind {
                BinaryInstKind::Add => Some(Box::new(arith::Add::new(is.has_add()?, lhs, rhs))),
                BinaryInstKind::Sub => Some(Box::new(arith::Sub::new(is.has_sub()?, lhs, rhs))),
                BinaryInstKind::Mul => Some(Box::new(arith::Mul::new(is.has_mul()?, lhs, rhs))),
                BinaryInstKind::Shl => Some(Box::new(arith::Shl::new(is.has_shl()?, lhs, rhs))),
                BinaryInstKind::Shr => Some(Box::new(arith::Shr::new(is.has_shr()?, lhs, rhs))),
                BinaryInstKind::Sar => Some(Box::new(arith::Sar::new(is.has_sar()?, lhs, rhs))),
                BinaryInstKind::And => Some(Box::new(logic::And::new(is.has_and()?, lhs, rhs))),
                BinaryInstKind::Xor => Some(Box::new(logic::Xor::new(is.has_xor()?, lhs, rhs))),
                BinaryInstKind::Or => Some(Box::new(logic::Or::new(is.has_or()?, lhs, rhs))),
                BinaryInstKind::Ne => Some(Box::new(cmp::Ne::new(is.has_ne()?, lhs, rhs))),
                BinaryInstKind::Eq => Some(Box::new(cmp::Eq::new(is.has_eq()?, lhs, rhs))),
                BinaryInstKind::Lt => Some(Box::new(cmp::Lt::new(is.has_lt()?, lhs, rhs))),
                BinaryInstKind::Gt => Some(Box::new(cmp::Gt::new(is.has_gt()?, lhs, rhs))),
                BinaryInstKind::Sge => Some(Box::new(cmp::Sge::new(is.has_sge()?, lhs, rhs))),
                BinaryInstKind::Sgt => Some(Box::new(cmp::Sgt::new(is.has_sgt()?, lhs, rhs))),
                BinaryInstKind::Sle => Some(Box::new(cmp::Sle::new(is.has_sle()?, lhs, rhs))),
                BinaryInstKind::Slt => Some(Box::new(cmp::Slt::new(is.has_slt()?, lhs, rhs))),
                BinaryInstKind::EvmByte => {
                    Some(Box::new(evm::EvmByte::new(is.has_evm_byte()?, lhs, rhs)))
                }
                BinaryInstKind::EvmSignExtend => Some(Box::new(evm::EvmSignExtend::new(
                    is.has_evm_sign_extend()?,
                    lhs,
                    rhs,
                ))),
                BinaryInstKind::EvmUmod => {
                    Some(Box::new(evm::EvmUmod::new(is.has_evm_umod()?, lhs, rhs)))
                }
                BinaryInstKind::Udiv => Some(Box::new(arith::Udiv::new(is.has_udiv()?, lhs, rhs))),
                BinaryInstKind::EvmUdiv => {
                    Some(Box::new(evm::EvmUdiv::new(is.has_evm_udiv()?, lhs, rhs)))
                }
                _ => None,
            }
        }
        InstSpec::Cast { kind, from, ty } => match kind {
            CastInstKind::Zext => Some(Box::new(cast::Zext::new(is.has_zext()?, from, ty))),
            CastInstKind::Sext => Some(Box::new(cast::Sext::new(is.has_sext()?, from, ty))),
            CastInstKind::Trunc => Some(Box::new(cast::Trunc::new(is.has_trunc()?, from, ty))),
            CastInstKind::TruncNuw => {
                Some(Box::new(cast::TruncNuw::new(is.has_trunc_nuw()?, from, ty)))
            }
            CastInstKind::Bitcast | CastInstKind::IntToPtr | CastInstKind::PtrToInt => None,
        },
    }
}

fn rebase_inst_spec(replacement: InstSpec, resolved: &FxHashMap<ValueId, ValueId>) -> InstSpec {
    match replacement {
        InstSpec::Unary { kind, arg } => InstSpec::Unary {
            kind,
            arg: rebase_value(arg, resolved),
        },
        InstSpec::Binary { kind, lhs, rhs } => InstSpec::Binary {
            kind,
            lhs: rebase_operand(lhs, resolved),
            rhs: rebase_operand(rhs, resolved),
        },
        InstSpec::Cast { kind, from, ty } => InstSpec::Cast {
            kind,
            from: rebase_value(from, resolved),
            ty,
        },
    }
}

fn rebase_operand(operand: Operand, resolved: &FxHashMap<ValueId, ValueId>) -> Operand {
    match operand {
        Operand::Value(value) => Operand::Value(rebase_value(value, resolved)),
        Operand::Imm(imm) => Operand::Imm(imm),
    }
}

fn rebase_value(value: ValueId, resolved: &FxHashMap<ValueId, ValueId>) -> ValueId {
    resolved.get(&value).copied().unwrap_or(value)
}

fn materialize_operand(func: &mut Function, operand: Operand) -> ValueId {
    match operand {
        Operand::Value(value) => value,
        Operand::Imm(imm) => func.dfg.make_imm_value(imm),
    }
}

fn supports_inst_spec(func: &Function, replacement: InstSpec) -> bool {
    let is = func.inst_set();
    match replacement {
        InstSpec::Unary {
            kind: UnaryInstKind::IsZero,
            ..
        } => is.has_is_zero().is_some(),
        InstSpec::Unary { .. } => false,
        InstSpec::Binary { kind, .. } => match kind {
            BinaryInstKind::Add => is.has_add().is_some(),
            BinaryInstKind::Sub => is.has_sub().is_some(),
            BinaryInstKind::Mul => is.has_mul().is_some(),
            BinaryInstKind::Shl => is.has_shl().is_some(),
            BinaryInstKind::Shr => is.has_shr().is_some(),
            BinaryInstKind::Sar => is.has_sar().is_some(),
            BinaryInstKind::And => is.has_and().is_some(),
            BinaryInstKind::Xor => is.has_xor().is_some(),
            BinaryInstKind::Or => is.has_or().is_some(),
            BinaryInstKind::Ne => is.has_ne().is_some(),
            BinaryInstKind::Eq => is.has_eq().is_some(),
            BinaryInstKind::Lt => is.has_lt().is_some(),
            BinaryInstKind::Gt => is.has_gt().is_some(),
            BinaryInstKind::Sge => is.has_sge().is_some(),
            BinaryInstKind::Sgt => is.has_sgt().is_some(),
            BinaryInstKind::Sle => is.has_sle().is_some(),
            BinaryInstKind::Slt => is.has_slt().is_some(),
            BinaryInstKind::EvmByte => is.has_evm_byte().is_some(),
            BinaryInstKind::EvmSignExtend => is.has_evm_sign_extend().is_some(),
            BinaryInstKind::EvmUmod => is.has_evm_umod().is_some(),
            BinaryInstKind::Udiv => is.has_udiv().is_some(),
            BinaryInstKind::EvmUdiv => is.has_evm_udiv().is_some(),
            _ => false,
        },
        InstSpec::Cast { kind, .. } => match kind {
            CastInstKind::Zext => is.has_zext().is_some(),
            CastInstKind::Sext => is.has_sext().is_some(),
            CastInstKind::Trunc => is.has_trunc().is_some(),
            CastInstKind::TruncNuw => is.has_trunc_nuw().is_some(),
            CastInstKind::Bitcast | CastInstKind::IntToPtr | CastInstKind::PtrToInt => false,
        },
    }
}

fn remove_rewritten_inst(func: &mut Function, inst: InstId) {
    if !func.layout.is_inst_inserted(inst) {
        return;
    }

    func.layout.remove_inst(inst);
    func.erase_inst(inst);
}

fn prune_dead_pure_insts(func: &mut Function) {
    let blocks: Vec<_> = func.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = func.layout.iter_inst(block).collect();
        for inst in insts {
            if !func.layout.is_inst_inserted(inst) || !func.dfg.can_drop_if_unused(inst) {
                continue;
            }

            if func
                .dfg
                .inst_results(inst)
                .iter()
                .any(|&result| func.dfg.users_num(result) != 0)
            {
                continue;
            }

            func.layout.remove_inst(inst);
            func.erase_inst(inst);
        }
    }
}

impl RewritePlan {
    fn inst(self) -> InstId {
        match self {
            RewritePlan::Copy { inst, .. } | RewritePlan::ReplaceInst { inst, .. } => inst,
        }
    }
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{Module, ir_writer::FuncWriter, module::FuncRef};
    use sonatina_parser::parse_module;

    use super::ScalarCanonicalize;

    #[test]
    fn rewrites_eq_zero_to_is_zero() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    v1.i1 = eq v0 0.i256;
    v2.i256 = zext v1 i256;
    return v2;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains(" = is_zero "), "{dumped}");
        assert!(!dumped.contains(" = eq "), "{dumped}");
    }

    #[test]
    fn rewrites_mul_by_pow2_to_shl() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    v1.i256 = mul v0 8.i256;
    return v1;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains(" = shl 3.i256 v0;"), "{dumped}");
        assert!(!dumped.contains(" = mul "), "{dumped}");
    }

    #[test]
    fn collapses_cast_chains_to_fixpoint() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i8) -> i32 {
block0:
    v1.i16 = zext v0 i16;
    v2.i32 = zext v1 i32;
    v3.i64 = zext v2 i64;
    v4.i32 = trunc v3 i32;
    return v4;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains("v2.i32 = zext v0 i32;"), "{dumped}");
        assert!(!dumped.contains(" i64;"), "{dumped}");
        assert!(dumped.contains("return v2;"), "{dumped}");
    }

    #[test]
    fn truncates_the_source_of_a_wider_extension() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i128, v1.i128) -> i64 {
block0:
    v2.i256 = zext v0 i256;
    v3.i64 = trunc v2 i64;
    v4.i256 = sext v1 i256;
    v5.i64 = trunc v4 i64;
    v6.i64 = add v3 v5;
    return v6;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains("v3.i64 = trunc v0 i64;"), "{dumped}");
        assert!(dumped.contains("v5.i64 = trunc v1 i64;"), "{dumped}");
        assert!(!dumped.contains(" i256;"), "{dumped}");
    }

    #[test]
    fn folds_integer_round_trips_through_pointers() {
        // A dangling pointer's address, as an empty vector's drop compares.
        let (module, func_ref) = parse_test_module(
            r#"
target = "x86_64-unknown-native"

func public %f(v0.i64, v1.*i8) -> *i8 {
block0:
    v2.*i8 = int_to_ptr 16.i64 *i8;
    v3.i64 = ptr_to_int v2 i64;
    v4.i1 = eq v3 v0;
    v5.i64 = ptr_to_int v1 i64;
    v6.*i8 = int_to_ptr v5 *i8;
    br v4 block1 block2;
block1:
    return v2;
block2:
    return v6;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains("v4.i1 = eq 16.i64 v0;"), "{dumped}");
        // A pointer's round trip through an integer loses its provenance.
        assert!(dumped.contains("v6.*i8 = int_to_ptr v5 *i8;"), "{dumped}");
    }

    #[test]
    fn keeps_round_trips_of_integers_wider_than_pointers() {
        // A pointer holds the low 64 bits of an i256, so `1 << 64` comes back
        // as zero.
        let (module, func_ref) = parse_test_module(
            r#"
target = "x86_64-unknown-native"

func public %f(v0.i256) -> i256 {
block0:
    v1.*i8 = int_to_ptr v0 *i8;
    v2.i256 = ptr_to_int v1 i256;
    return v2;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            ScalarCanonicalize::new().run(func);
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains("v2.i256 = ptr_to_int v1 i256;"), "{dumped}");
        assert!(dumped.contains("return v2;"), "{dumped}");
    }

    #[test]
    fn rewrites_zext_i1_eq_zero_to_is_zero_source() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1) -> i256 {
block0:
    v1.i256 = zext v0 i256;
    v2.i1 = eq v1 0.i256;
    v3.i256 = zext v2 i256;
    return v3;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains(" = is_zero v0;"), "{dumped}");
        assert!(!dumped.contains(" = eq v1 0.i256;"), "{dumped}");
    }

    #[test]
    fn rebases_replace_operands_after_copy_rewrites() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i8) -> i256 {
block0:
    v1.i16 = zext v0 i16;
    v2.i8 = trunc v1 i8;
    v3.i1 = eq v2 0.i8;
    v4.i256 = zext v3 i256;
    return v4;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains(" = is_zero v0;"), "{dumped}");
        assert!(!dumped.contains(" = trunc "), "{dumped}");
    }

    #[test]
    fn prunes_dead_multi_result_insts_after_rewrite() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "evm-ethereum-osaka"

func public %f(v0.i8, v1.i256, v2.i256) -> i8 {
block0:
    (v3.i256, v4.i1) = uaddo v1 v2;
    v5.i16 = zext v0 i16;
    v6.i8 = trunc v5 i8;
    return v6;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains("return v0;"), "{dumped}");
        assert!(!dumped.contains("uaddo"), "{dumped}");
        assert!(!dumped.contains(" = zext "), "{dumped}");
        assert!(!dumped.contains(" = trunc "), "{dumped}");
    }

    #[test]
    fn rewrites_unsigned_power_of_two_division_and_remainder() {
        for ty in ["i8", "i256"] {
            let high = if ty == "i8" {
                "-128"
            } else {
                "-57896044618658097711785492504343953926634992332820282019728792003956564819968"
            };
            let high_shift = if ty == "i8" { 7 } else { 255 };
            for (op, replacement) in [
                ("udiv", "shr"),
                ("evm_udiv", "shr"),
                ("umod", "and"),
                ("evm_umod", "and"),
            ] {
                if ty != "i256" && op.starts_with("evm_") {
                    continue;
                }
                for (divisor, shift) in [("32", 5), (high, high_shift)] {
                    let source = format!(
                        "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.{ty}) -> {ty} {{\nblock0:\n v1.{ty} = {op} v0 {divisor}.{ty};\n return v1;\n}}"
                    );
                    let (module, f) = parse_test_module(&source);
                    module
                        .func_store
                        .modify(f, |func| assert!(ScalarCanonicalize::new().run(func)));
                    let dumped = dump_func(&module, f);
                    assert!(dumped.contains(&format!(" = {replacement} ")), "{dumped}");
                    if replacement == "shr" {
                        assert!(dumped.contains(&format!("shr {shift}.{ty} v0")), "{dumped}");
                    }
                }
            }
        }
    }

    #[test]
    fn preserves_signed_zero_and_non_power_of_two_divisors() {
        for (op, divisor) in [
            ("evm_udiv", 0),
            ("evm_umod", 0),
            ("udiv", 3),
            ("umod", 3),
            ("sdiv", 32),
            ("smod", 32),
            ("evm_sdiv", 32),
            ("evm_smod", 32),
        ] {
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {{\nblock0:\n v1.i256 = {op} v0 {divisor}.i256;\n return v1;\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module
                .func_store
                .modify(f, |func| assert!(!ScalarCanonicalize::new().run(func)));
        }
    }

    #[test]
    fn merges_constant_shifts_of_one_kind() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "x86_64-unknown-native"

func public %f(v0.i128, v1.i64) -> i128 {
block0:
    v2.i128 = shr 13.i128 v0;
    v3.i128 = shr 64.i128 v2;
    v4.i64 = shl 5.i64 v1;
    v5.i64 = shl 3.i64 v4;
    v6.i128 = zext v5 i128;
    v7.i128 = shl 64.i128 v3;
    v8.i128 = or v7 v6;
    return v8;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains(" = shr 77.i128 v0;"), "{dumped}");
        assert!(dumped.contains(" = shl 8.i64 v1;"), "{dumped}");
        assert!(!dumped.contains("shr 13."), "{dumped}");
        assert!(!dumped.contains("shl 5."), "{dumped}");
    }

    #[test]
    fn clamps_merged_shift_counts_to_the_width() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "x86_64-unknown-native"

func public %f(v0.i64, v1.i8) -> i64 {
block0:
    v2.i64 = shr 40.i64 v0;
    v3.i64 = shr 40.i64 v2;
    v4.i64 = sar 40.i64 v0;
    v5.i64 = sar 40.i64 v4;
    v6.i8 = shl -56.i8 v1;
    v7.i8 = shl 100.i8 v6;
    v8.i64 = zext v7 i64;
    v9.i64 = or v3 v5;
    v10.i64 = or v9 v8;
    return v10;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(ScalarCanonicalize::new().run(func));
        });

        let dumped = dump_func(&module, func_ref);
        assert!(dumped.contains(" = shr 64.i64 v0;"), "{dumped}");
        assert!(dumped.contains(" = sar 63.i64 v0;"), "{dumped}");
        assert!(dumped.contains(" = shl 8.i8 v1;"), "{dumped}");
    }

    #[test]
    fn keeps_shifts_of_different_kinds() {
        let (module, func_ref) = parse_test_module(
            r#"
target = "x86_64-unknown-native"

func public %f(v0.i64) -> i64 {
block0:
    v1.i64 = shl 3.i64 v0;
    v2.i64 = shr 3.i64 v1;
    return v2;
}
"#,
        );

        module.func_store.modify(func_ref, |func| {
            assert!(!ScalarCanonicalize::new().run(func));
        });
    }

    fn parse_test_module(src: &str) -> (Module, FuncRef) {
        let parsed = parse_module(src).expect("module parses");
        let func_ref = parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func| parsed.module.ctx.func_sig(func, |sig| sig.name() == "f"))
            .expect("missing f");
        (parsed.module, func_ref)
    }

    fn dump_func(module: &Module, func_ref: FuncRef) -> String {
        module.func_store.view(func_ref, |func| {
            FuncWriter::new(func_ref, func).dump_string()
        })
    }

    #[test]
    fn merges_unsigned_constant_division_chains() {
        for (ty, op) in [("i8", "udiv"), ("i128", "udiv"), ("i256", "evm_udiv")] {
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.{ty}) -> {ty} {{\nblock0:\n v1.{ty} = {op} v0 3.{ty};\n v2.{ty} = {op} v1 7.{ty};\n return v2;\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module
                .func_store
                .modify(f, |func| assert!(ScalarCanonicalize::new().run(func)));
            let dumped = dump_func(&module, f);
            assert!(dumped.contains(&format!("{op} v0 21.{ty}")), "{dumped}");
            assert_eq!(dumped.matches(&format!(" = {op} ")).count(), 1, "{dumped}");
        }
    }

    #[test]
    fn preserves_unsafe_or_shared_division_chains() {
        for (ty, op, a, b, shared) in [
            ("i256", "evm_udiv", "0", "3", false),
            ("i256", "evm_udiv", "3", "0", false),
            ("i256", "evm_udiv", "-1", "3", false),
            ("i8", "udiv", "17", "17", false),
            ("i256", "evm_sdiv", "3", "7", false),
            ("i128", "sdiv", "3", "7", false),
            ("i256", "evm_udiv", "3", "7", true),
        ] {
            let result = if shared {
                format!(" v3.{ty} = add v1 v2;\n return v3;")
            } else {
                " return v2;".into()
            };
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.{ty}) -> {ty} {{\nblock0:\n v1.{ty} = {op} v0 {a}.{ty};\n v2.{ty} = {op} v1 {b}.{ty};\n{result}\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module
                .func_store
                .modify(f, |func| assert!(!ScalarCanonicalize::new().run(func)));
        }
    }

    #[test]
    fn keeps_compact_power_of_two_divisors() {
        for (a, b) in [("18446744073709551616", "3"), ("3", "18446744073709551616")] {
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {{\nblock0:\n v1.i256 = evm_udiv v0 {a}.i256;\n v2.i256 = evm_udiv v1 {b}.i256;\n return v2;\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(dumped.contains("shr 64.i256"), "{dumped}");
            assert!(dumped.contains(" = evm_udiv "), "{dumped}");
        }
    }
    #[test]
    fn preserves_unmatched_word_idioms() {
        for (target, ty, shift, mask, shared) in [
            ("evm-ethereum-osaka", "i256", 13, "255", false),
            ("evm-ethereum-osaka", "i256", 256, "255", false),
            ("evm-ethereum-osaka", "i256", 8, "65535", false),
            ("evm-ethereum-osaka", "i256", 8, "255", true),
            ("evm-ethereum-osaka", "i16", 8, "255", false),
            ("x86_64-unknown-native", "i256", 8, "255", false),
        ] {
            let result = if shared {
                format!("v3.{ty} = add v1 v2; return v3;")
            } else {
                "return v2;".into()
            };
            let source = format!(
                "target = \"{target}\"\nfunc public %f(v0.{ty}) -> {ty} {{\nblock0:\n v1.{ty} = shr {shift}.{ty} v0;\n v2.{ty} = and v1 {mask}.{ty};\n {result}\n}}"
            );
            let (module, f) = parse_test_module(&source.replace("; ", ";\n"));
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(!dumped.contains("evm_byte"), "{dumped}");
        }
    }

    #[test]
    fn selects_bytes_through_shifts_at_every_valid_position() {
        for op in ["shl", "shr"] {
            for count in (8..256).step_by(8) {
                for index in 0..32 {
                    let adjusted = if op == "shl" {
                        index + count / 8
                    } else {
                        index - count / 8
                    };
                    if !(0..32).contains(&adjusted) {
                        continue;
                    }
                    let source = format!(
                        "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {{\nblock0:\n v1.i256 = {op} {count}.i256 v0;\n v2.i256 = evm_byte {index}.i256 v1;\n return v2;\n}}"
                    );
                    let (module, f) = parse_test_module(&source);
                    module.func_store.modify(f, |func| {
                        ScalarCanonicalize::new().run(func);
                    });
                    let dumped = dump_func(&module, f);
                    assert!(
                        dumped.contains(&format!("evm_byte {adjusted}.i256 v0")),
                        "{dumped}"
                    );
                    assert!(!dumped.contains(&format!(" = {op} ")), "{dumped}");
                }
            }
        }
    }

    #[test]
    fn preserves_unmatched_or_shared_shifted_bytes() {
        for (op, count, index, shared, cross_block) in [
            ("shl", "4.i256", "0.i256", false, false),
            ("shr", "v3", "1.i256", false, false),
            ("shl", "8.i256", "v3", false, false),
            ("shl", "256.i256", "0.i256", false, false),
            ("shl", "8.i256", "32.i256", false, false),
            ("shl", "8.i256", "31.i256", false, false),
            ("shr", "8.i256", "0.i256", false, false),
            ("shl", "8.i256", "0.i256", true, false),
            ("shl", "8.i256", "0.i256", false, true),
        ] {
            let branch = if cross_block {
                "jump block1;\nblock1:"
            } else {
                ""
            };
            let tail = if shared {
                "v4.i256 = add v1 v2;\n return v4;"
            } else {
                "return v2;"
            };
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256, v3.i256) -> i256 {{\nblock0:\n v1.i256 = {op} {count} v0;\n {branch}\n v2.i256 = evm_byte {index} v1;\n {tail}\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(
                dumped.contains(&format!(
                    "evm_byte {} v2",
                    if index == "v3" { "v1" } else { index }
                )),
                "{dumped}"
            );
        }
    }

    #[test]
    fn divides_by_dynamic_power_of_two_with_evm_semantics() {
        let source = r#"
target = "evm-ethereum-osaka"
func public %f(v0.i256, v1.i256) -> i256 {
block0:
 v2.i256 = shl v1 1.i256;
 v3.i256 = evm_udiv v0 v2;
 return v3;
}
"#;
        let (module, f) = parse_test_module(source);
        module.func_store.modify(f, |func| {
            ScalarCanonicalize::new().run(func);
        });
        let dumped = dump_func(&module, f);
        assert!(dumped.contains("shr v1 v0"), "{dumped}");
        assert!(!dumped.contains("evm_udiv"), "{dumped}");
    }

    #[test]
    fn preserves_unmatched_dynamic_divisors() {
        for (op, one, shared, cross_block) in [
            ("udiv", 1, false, false),
            ("evm_sdiv", 1, false, false),
            ("evm_udiv", 2, false, false),
            ("evm_udiv", 1, true, false),
            ("evm_udiv", 1, false, true),
        ] {
            let branch = if cross_block {
                "jump block1;\nblock1:"
            } else {
                ""
            };
            let tail = if shared {
                "v4.i256 = add v2 v3;\n return v4;"
            } else {
                "return v3;"
            };
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256, v1.i256) -> i256 {{\nblock0:\n v2.i256 = shl v1 {one}.i256;\n {branch}\n v3.i256 = {op} v0 v2;\n {tail}\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(dumped.contains(&format!("{op} v0 v2")), "{dumped}");
        }
    }

    #[test]
    fn selects_byte_for_each_position_and_mask_order() {
        for shift in (8..=248).step_by(8) {
            for mask in ["and v1 255.i256", "and 255.i256 v1"] {
                let source = format!(
                    "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {{\nblock0:\n v1.i256 = shr {shift}.i256 v0;\n v2.i256 = {mask};\n return v2;\n}}"
                );
                let (module, f) = parse_test_module(&source);
                module.func_store.modify(f, |func| {
                    ScalarCanonicalize::new().run(func);
                });
                let dumped = dump_func(&module, f);
                assert!(
                    dumped.contains(&format!("evm_byte {}.i256 v0", 31 - shift / 8)),
                    "{dumped}"
                );
            }
        }
    }

    #[test]
    fn keeps_cross_block_byte_shift() {
        let source = "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {\nblock0:\n v1.i256 = shr 8.i256 v0;\n jump block1;\nblock1:\n v2.i256 = and v1 255.i256;\n return v2;\n}";
        let (module, f) = parse_test_module(source);
        module.func_store.modify(f, |func| {
            ScalarCanonicalize::new().run(func);
        });
        assert!(!dump_func(&module, f).contains("evm_byte"));
    }
    #[test]
    fn signed_top_fields_use_arithmetic_shifts() {
        for shift in (8..=248).step_by(8) {
            let byte = 31 - shift / 8;
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {{\nblock0:\n v1.i256 = shr {shift}.i256 v0;\n v2.i256 = evm_signextend {byte}.i256 v1;\n return v2;\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(dumped.contains(&format!("sar {shift}.i256 v0")), "{dumped}");
            assert!(!dumped.contains("evm_signextend"), "{dumped}");
        }
        let (module, f) = parse_test_module(
            "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {\nblock0:\n v1.i256 = evm_byte 0.i256 v0;\n v2.i256 = evm_signextend 0.i256 v1;\n return v2;\n}",
        );
        module.func_store.modify(f, |func| {
            ScalarCanonicalize::new().run(func);
        });
        assert!(dump_func(&module, f).contains("sar 248.i256 v0"));
    }

    #[test]
    fn signed_top_fields_keep_mismatched_shared_and_cross_block_sources() {
        for body in [
            "v1.i256 = shr 8.i256 v0; v2.i256 = evm_signextend 1.i256 v1; return v2;",
            "v1.i256 = shr 256.i256 v0; v2.i256 = evm_signextend 0.i256 v1; return v2;",
            "v1.i256 = shr 248.i256 v0; v2.i256 = evm_signextend 32.i256 v1; return v2;",
            "v1.i256 = evm_byte 1.i256 v0; v2.i256 = evm_signextend 0.i256 v1; return v2;",
            "v1.i256 = shr 192.i256 v0; v2.i256 = evm_signextend 7.i256 v1; v3.i256 = add v1 v2; return v3;",
            "v1.i256 = shr 192.i256 v0; jump block1;\nblock1:\n v2.i256 = evm_signextend 7.i256 v1; return v2;",
        ] {
            let source = format!("target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {{\nblock0:\n{body}\n}}").replace("; ", ";\n");
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(dumped.contains("evm_signextend"), "{dumped}");
        }
    }

    #[test]
    fn selects_signextend_for_each_byte_width() {
        for shift in (8..=248).step_by(8) {
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {{\nblock0:\n v1.i256 = shl {shift}.i256 v0;\n v2.i256 = sar {shift}.i256 v1;\n return v2;\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(
                dumped.contains(&format!("evm_signextend {}.i256 v0", 31 - shift / 8)),
                "{dumped}"
            );
        }
    }

    #[test]
    fn preserves_unmatched_sign_shifts() {
        for (target, ty, shift) in [
            ("evm-ethereum-osaka", "i256", 13),
            ("evm-ethereum-osaka", "i256", 256),
            ("evm-ethereum-osaka", "i16", 8),
            ("x86_64-unknown-native", "i256", 8),
        ] {
            let source = format!(
                "target = \"{target}\"\nfunc public %f(v0.{ty}) -> {ty} {{\nblock0:\n v1.{ty} = shl {shift}.{ty} v0;\n v2.{ty} = sar {shift}.{ty} v1;\n return v2;\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            assert!(!dump_func(&module, f).contains("evm_signextend"));
        }
    }
    #[test]
    fn keeps_shared_and_cross_block_sign_shifts() {
        for body in [
            "v1.i256 = shl 248.i256 v0; v2.i256 = sar 240.i256 v1; return v2;",
            "v1.i256 = shl 248.i256 v0; v2.i256 = sar 248.i256 v1; v3.i256 = add v1 v2; return v3;",
            "v1.i256 = shl 248.i256 v0; jump block1;\nblock1:\n v2.i256 = sar 248.i256 v1; return v2;",
        ] {
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {{\nblock0:\n{body}\n}}"
            );
            let (module, f) = parse_test_module(&source.replace("; ", ";\n"));
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(
                !dumped.contains("evm_signextend") && !dumped.contains("evm_byte"),
                "{dumped}"
            );
        }
    }

    #[test]
    fn signed_shift_tests_only_need_the_original_sign() {
        for (ty, target) in [
            ("i8", "x86_64-unknown-native"),
            ("i256", "evm-ethereum-osaka"),
        ] {
            for shift in [1, 7, 8, 64, 127] {
                for (op, bound) in [("slt", "0"), ("sge", "0"), ("sgt", "-1"), ("sle", "-1")] {
                    let source = format!(
                        "target = \"{target}\"\nfunc public %f(v0.{ty}) -> i1 {{\nblock0:\n v1.{ty} = sar {shift}.{ty} v0;\n v2.i1 = {op} v1 {bound}.{ty};\n return v2;\n}}"
                    );
                    let (module, f) = parse_test_module(&source);
                    module.func_store.modify(f, |func| {
                        ScalarCanonicalize::new().run(func);
                    });
                    let dumped = dump_func(&module, f);
                    assert!(
                        dumped.contains(&format!("{op} v0 {bound}.{ty}")),
                        "{dumped}"
                    );
                    assert!(!dumped.contains("sar "), "{dumped}");
                }
            }
        }
    }

    #[test]
    fn shifted_sign_tests_keep_other_bounds_and_shared_or_dynamic_shifts() {
        for body in [
            "v1.i256 = sar 8.i256 v0; v2.i1 = slt v1 1.i256; return v2;",
            "v1.i256 = sar 8.i256 v0; v2.i1 = sgt v1 0.i256; return v2;",
            "v1.i256 = sar v0 v0; v2.i1 = slt v1 0.i256; return v2;",
            "v1.i256 = sar 8.i256 v0; v2.i1 = slt v1 0.i256; v3.i1 = eq v1 1.i256; v4.i1 = or v2 v3; return v4;",
            "v1.i256 = sar 8.i256 v0; jump block1;\nblock1:\n v2.i1 = slt v1 0.i256; return v2;",
        ] {
            let source = format!("target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i1 {{\nblock0:\n{body}\n}}").replace("; ", ";\n");
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(dumped.contains("sar "), "{dumped}");
        }
    }

    #[test]
    fn equality_moves_invertible_constants_into_the_bound() {
        for (ty, target) in [
            ("i8", "x86_64-unknown-native"),
            ("i256", "evm-ethereum-osaka"),
        ] {
            for (op, operands, bound, expected) in [
                ("add", "v0 10", "40", "30"),
                ("add", "10 v0", "40", "30"),
                ("sub", "v0 10", "40", "50"),
                ("sub", "10 v0", "3", "7"),
                ("xor", "v0 10", "40", "34"),
                ("xor", "10 v0", "40", "34"),
            ] {
                let operands = operands.replace("10", &format!("10.{ty}"));
                for comparison in ["eq", "ne"] {
                    for reversed in [false, true] {
                        let args = if reversed {
                            format!("{bound}.{ty} v1")
                        } else {
                            format!("v1 {bound}.{ty}")
                        };
                        let source = format!(
                            "target = \"{target}\"\nfunc public %f(v0.{ty}) -> i1 {{\nblock0:\n v1.{ty} = {op} {operands};\n v2.i1 = {comparison} {args};\n return v2;\n}}"
                        );
                        let (module, f) = parse_test_module(&source);
                        module.func_store.modify(f, |func| {
                            ScalarCanonicalize::new().run(func);
                        });
                        let dumped = dump_func(&module, f);
                        assert!(
                            dumped.contains(&format!("{comparison} v0 {expected}.{ty}")),
                            "{dumped}"
                        );
                        assert!(!dumped.contains(&format!(" = {op} ")), "{dumped}");
                    }
                }
            }
        }
    }

    #[test]
    fn zero_tests_fold_xor_constants() {
        let (module, f) = parse_test_module(
            "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i1 {\nblock0:\n v1.i256 = xor v0 85.i256;\n v2.i1 = is_zero v1;\n return v2;\n}",
        );
        module.func_store.modify(f, |func| {
            ScalarCanonicalize::new().run(func);
        });
        let dumped = dump_func(&module, f);
        assert!(dumped.contains("eq v0 85.i256"), "{dumped}");
        assert!(!dumped.contains("xor "), "{dumped}");
    }

    #[test]
    fn equality_preserves_shared_cross_block_checked_and_costly_producers() {
        for (body, retained) in [
            (
                "v1.i256 = add v0 100.i256; v2.i1 = eq v1 1.i256; return v2;",
                "add ",
            ),
            (
                "v1.i256 = add v0 1.i256; v2.i1 = eq v1 340282366920938463463374607431768211456.i256; return v2;",
                "add ",
            ),
            (
                "v1.i256 = xor v0 85.i256; v2.i1 = eq v1 102.i256; v3.i1 = eq v1 99.i256; v4.i1 = or v2 v3; return v4;",
                "xor ",
            ),
            (
                "v1.i256 = xor v0 85.i256; jump block1;\nblock1:\n v2.i1 = eq v1 102.i256; return v2;",
                "xor ",
            ),
            (
                "(v1.i256, v2.i1) = uaddo v0 100.i256; v3.i1 = eq v1 150.i256; v4.i1 = or v2 v3; return v4;",
                "uaddo ",
            ),
            (
                "v1.i256 = mul v0 10.i256; v2.i1 = eq v1 40.i256; return v2;",
                "mul ",
            ),
        ] {
            let source = format!("target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i1 {{\nblock0:\n{body}\n}}").replace("; ", ";\n");
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(dumped.contains(retained), "{dumped}");
        }
    }

    #[test]
    fn equality_cancels_common_operands_only_for_injective_operations() {
        for ty in ["i8", "i256"] {
            let odd = format!("-3.{ty}");
            let even = format!("6.{ty}");
            for (op, common, left_first, right_first, cancels) in [
                ("add", "v2", true, true, true),
                ("add", "v2", false, true, true),
                ("xor", "v2", true, false, true),
                ("sub", "v2", true, true, true),
                ("sub", "v2", false, false, true),
                ("sub", "v2", true, false, false),
                ("mul", odd.as_str(), false, true, true),
                ("mul", even.as_str(), false, true, false),
                ("mul", "v2", false, false, false),
            ] {
                let operands = |input: &str, first| {
                    if first {
                        format!("{common} {input}")
                    } else {
                        format!("{input} {common}")
                    }
                };
                let left = operands("v0", left_first);
                let right = operands("v1", right_first);
                for comparison in ["eq", "ne", "lt"] {
                    let source = format!(
                        r#"target = "evm-ethereum-osaka"
func public %f(v0.{ty}, v1.{ty}, v2.{ty}) -> i1 {{
block0:
 v3.{ty} = {op} {left};
 v4.{ty} = {op} {right};
 v5.i1 = {comparison} v3 v4;
 return v5;
}}"#
                    );
                    let (module, f) = parse_test_module(&source);
                    module.func_store.modify(f, |func| {
                        ScalarCanonicalize::new().run(func);
                    });
                    let dumped = dump_func(&module, f);
                    if cancels && comparison != "lt" {
                        assert!(dumped.contains(&format!("{comparison} v0 v1;")), "{dumped}");
                        assert!(!dumped.contains(&format!(" = {op} ")), "{dumped}");
                    } else {
                        assert_eq!(dumped.matches(&format!(" = {op} ")).count(), 2, "{dumped}");
                    }
                }
            }
        }
    }

    #[test]
    fn folds_bitwise_pairs_in_each_operand_order() {
        for ty in ["i1", "i8", "i256"] {
            for (outer, a, b, expected) in [
                ("and", "and", "or", "and"),
                ("and", "or", "xor", "xor"),
                ("or", "and", "or", "or"),
                ("or", "and", "xor", "or"),
                ("or", "or", "xor", "or"),
                ("xor", "and", "or", "xor"),
                ("xor", "and", "xor", "or"),
                ("xor", "or", "xor", "and"),
            ] {
                for (a, b) in [(a, b), (b, a)] {
                    for reverse in [false, true] {
                        let (u, v) = if reverse { ("v1", "v0") } else { ("v0", "v1") };
                        let source = format!(
                            "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.{ty}, v1.{ty}) -> {ty} {{\nblock0:\n v2.{ty} = {a} v0 v1;\n v3.{ty} = {b} {u} {v};\n v4.{ty} = {outer} v2 v3;\n return v4;\n}}"
                        );
                        let (module, f) = parse_test_module(&source);
                        module.func_store.modify(f, |func| {
                            ScalarCanonicalize::new().run(func);
                        });
                        let dumped = dump_func(&module, f);
                        assert!(
                            dumped.contains(&format!(" = {expected} v0 v1;")),
                            "{dumped}"
                        );
                        assert_eq!(dumped.matches(" = ").count(), 1, "{dumped}");
                    }
                }
            }
        }
    }

    #[test]
    fn preserves_shared_cross_block_and_mismatched_bitwise_pairs() {
        for (right, shared, cross_block) in [
            ("or v0 v1", true, false),
            ("or v0 v1", false, true),
            ("or v0 v0", false, false),
        ] {
            let branch = if cross_block {
                "jump block1;\nblock1:"
            } else {
                ""
            };
            let tail = if shared {
                "v5.i256 = add v2 v4;\nreturn v5;"
            } else {
                "return v4;"
            };
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256, v1.i256) -> i256 {{\nblock0:\n v2.i256 = and v0 v1;\n {branch}\n v3.i256 = {right};\n v4.i256 = xor v2 v3;\n {tail}\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(dumped.contains("xor v2 v3"), "{dumped}");
        }
    }

    #[test]
    fn quotient_zero_tests_use_unsigned_comparisons() {
        for (ty, div, target) in [
            ("i8", "udiv", "x86_64-unknown-native"),
            ("i256", "evm_udiv", "evm-ethereum-osaka"),
        ] {
            for (test, expected) in [
                ("eq v1 0.TY", "lt v0 10.TY"),
                ("eq 0.TY v1", "lt v0 10.TY"),
                ("is_zero v1", "lt v0 10.TY"),
                ("ne v1 0.TY", "gt v0 9.TY"),
                ("ne 0.TY v1", "gt v0 9.TY"),
            ] {
                let test = test.replace("TY", ty);
                let source = format!(
                    "target = \"{target}\"\nfunc public %f(v0.{ty}) -> i1 {{\nblock0:\n v1.{ty} = {div} v0 10.{ty};\n v2.i1 = {test};\n return v2;\n}}"
                );
                let (module, f) = parse_test_module(&source);
                module.func_store.modify(f, |func| {
                    ScalarCanonicalize::new().run(func);
                });
                let dumped = dump_func(&module, f);
                assert!(dumped.contains(&expected.replace("TY", ty)), "{dumped}");
                assert!(!dumped.contains(&format!(" = {div} ")), "{dumped}");
            }
        }
    }

    #[test]
    fn quotient_zero_tests_keep_unsupported_or_shared_divisions() {
        for body in [
            "v1.i256 = evm_sdiv v0 10.i256; v2.i1 = is_zero v1; return v2;",
            "v1.i256 = evm_udiv v0 0.i256; v2.i1 = is_zero v1; return v2;",
            "v1.i256 = evm_udiv 10.i256 v0; v2.i1 = is_zero v1; return v2;",
            "v1.i256 = evm_udiv v0 10.i256; v2.i1 = is_zero v1; v3.i1 = lt v1 3.i256; v4.i1 = or v2 v3; return v4;",
            "v1.i256 = evm_udiv v0 10.i256; jump block1;\nblock1:\n v2.i1 = is_zero v1; return v2;",
        ] {
            let source = format!("target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i1 {{\nblock0:\n{body}\n}}").replace("; ", ";\n");
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            let dumped = dump_func(&module, f);
            assert!(dumped.contains("div "), "{dumped}");
        }
    }

    #[test]
    fn quotient_zero_tests_preserve_trivial_and_power_of_two_divisors() {
        for divisor in ["1", "256", "18446744073709551616"] {
            for test in ["is_zero v1", "eq v1 0.i256", "ne v1 0.i256"] {
                let source = format!(
                    "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i1 {{\nblock0:\n v1.i256 = evm_udiv v0 {divisor}.i256;\n v2.i1 = {test};\n return v2;\n}}"
                );
                let (module, f) = parse_test_module(&source);
                module.func_store.modify(f, |func| {
                    ScalarCanonicalize::new().run(func);
                });
                let dumped = dump_func(&module, f);
                assert!(
                    !dumped.contains(" = lt ") && !dumped.contains(" = gt "),
                    "{dumped}"
                );
                if divisor == "18446744073709551616" {
                    assert!(dumped.contains("shr 64.i256 v0"), "{dumped}");
                }
            }
        }
    }

    #[test]
    fn folds_complemented_wrapping_arithmetic() {
        for (ty, target) in [
            ("i256", "evm-ethereum-osaka"),
            ("i8", "x86_64-unknown-native"),
        ] {
            for (body, expected) in [
                (
                    format!("v2.{ty} = sub v0 1.{ty};\n v3.{ty} = not v2;"),
                    format!("sub 0.{ty} v0"),
                ),
                (
                    format!("v2.{ty} = not v0;\n v3.{ty} = add v2 v1;\n v4.{ty} = not v3;"),
                    "sub v0 v1".into(),
                ),
                (
                    format!("v2.{ty} = not v0;\n v3.{ty} = add v1 v2;\n v4.{ty} = not v3;"),
                    "sub v0 v1".into(),
                ),
                (
                    format!("v2.{ty} = not v0;\n v3.{ty} = sub v2 v1;\n v4.{ty} = not v3;"),
                    "add v0 v1".into(),
                ),
                (
                    format!("v2.{ty} = not v0;\n v3.{ty} = not v1;\n v4.{ty} = sub v2 v3;"),
                    "sub v1 v0".into(),
                ),
                (
                    format!(
                        "v2.{ty} = shl v0 1.{ty};\n v3.{ty} = sub v2 1.{ty};\n v4.{ty} = not v3;"
                    ),
                    format!("shl v0 -1.{ty}"),
                ),
            ] {
                let result = if body.contains("v4.") { "v4" } else { "v3" };
                let source = format!(
                    "target = \"{target}\"\nfunc public %f(v0.{ty}, v1.{ty}) -> {ty} {{\nblock0:\n {body}\n return {result};\n}}"
                );
                let (module, f) = parse_test_module(&source);
                module.func_store.modify(f, |func| {
                    ScalarCanonicalize::new().run(func);
                    // The pipeline removes newly dead nested producers after rewriting.
                    super::prune_dead_pure_insts(func);
                });
                let dumped = dump_func(&module, f);
                assert!(dumped.contains(&expected), "{dumped}");
                assert_eq!(dumped.matches(" = ").count(), 1, "{dumped}");
            }
        }
    }

    #[test]
    fn preserves_shared_or_cross_block_complemented_arithmetic() {
        for (shared, cross_block) in [(true, false), (false, true)] {
            let branch = if cross_block {
                "jump block1;\nblock1:"
            } else {
                ""
            };
            let tail = if shared {
                "v3.i256 = add v1 v2;\nreturn v3;"
            } else {
                "return v2;"
            };
            let source = format!(
                "target = \"evm-ethereum-osaka\"\nfunc public %f(v0.i256) -> i256 {{\nblock0:\n v1.i256 = sub v0 1.i256;\n {branch}\n v2.i256 = not v1;\n {tail}\n}}"
            );
            let (module, f) = parse_test_module(&source);
            module.func_store.modify(f, |func| {
                ScalarCanonicalize::new().run(func);
            });
            assert!(dump_func(&module, f).contains("not v1"));
        }
    }
}
