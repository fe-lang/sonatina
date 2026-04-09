use rustc_hash::FxHashMap;
use sonatina_ir::{
    Function, I256, Immediate, Inst, InstId, Type, Value, ValueId,
    inst::{BinaryInstKind, CastInstKind, InstClassKind, UnaryInstKind, arith, cast, cmp},
};

use super::simplify_expr::{
    ZextI1CompareRewrite, canonicalize_cast_chain, shift_amount_for_pow2_mul, simplify_cast,
    simplify_zext_i1_compare,
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

            prune_dead_single_result_insts(func);
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

                canonicalize_binary_inst(func, kind, *lhs, *rhs)
                    .filter(|&replacement| supports_inst_spec(func, replacement))
                    .map(|replacement| RewritePlan::ReplaceInst { inst, replacement })
            }
            InstClassKind::Cast(kind) => {
                let values = inst_data.collect_values();
                let [from] = values.as_slice() else {
                    return None;
                };
                let ty = func.dfg.value_ty(*result);
                if let super::simplify_expr::SimplifyExprResult::Copy(replacement) =
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
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
) -> Option<InstSpec> {
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
        BinaryInstKind::Mul => mul_pow2_rewrite(func, lhs, rhs),
        _ => None,
    }
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
        && let Some(shift) = shift_amount_for_pow2_mul(imm)
    {
        return Some(InstSpec::Binary {
            kind: BinaryInstKind::Shl,
            lhs: Operand::Imm(Immediate::from_i256(I256::from(shift), imm.ty())),
            rhs: Operand::Value(rhs),
        });
    }
    if let Some(imm) = func.dfg.value_imm(rhs)
        && let Some(shift) = shift_amount_for_pow2_mul(imm)
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
                BinaryInstKind::Shl => Some(Box::new(arith::Shl::new(is.has_shl()?, lhs, rhs))),
                _ => None,
            }
        }
        InstSpec::Cast { kind, from, ty } => match kind {
            CastInstKind::Zext => Some(Box::new(cast::Zext::new(is.has_zext()?, from, ty))),
            CastInstKind::Sext => Some(Box::new(cast::Sext::new(is.has_sext()?, from, ty))),
            CastInstKind::Trunc => Some(Box::new(cast::Trunc::new(is.has_trunc()?, from, ty))),
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
            BinaryInstKind::Shl => is.has_shl().is_some(),
            _ => false,
        },
        InstSpec::Cast { kind, .. } => match kind {
            CastInstKind::Zext => is.has_zext().is_some(),
            CastInstKind::Sext => is.has_sext().is_some(),
            CastInstKind::Trunc => is.has_trunc().is_some(),
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

fn prune_dead_single_result_insts(func: &mut Function) {
    let blocks: Vec<_> = func.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = func.layout.iter_inst(block).collect();
        for inst in insts {
            if !func.layout.is_inst_inserted(inst) || func.dfg.inst(inst).side_effect().has_effect()
            {
                continue;
            }
            let &[result] = func.dfg.inst_results(inst) else {
                continue;
            };
            if func.dfg.users_num(result) != 0 {
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
}
