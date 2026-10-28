use sonatina_ir::{
    ControlFlowGraph, Function, Immediate, InstId, Type, Value, ValueId,
    inst::{
        BinaryInstKind, InstClassKind, UnaryInstKind,
        arith::{Add, Mul, Sub},
        evm::{EvmSdiv, EvmSmod, EvmUdiv, EvmUmod},
    },
};

use crate::{
    domtree::DomTree,
    loop_analysis::LoopTree,
    range_analysis::{RangeAnalysis, RangeEnv, checked_value_fact},
};

pub struct CheckedArithElim {
    plans: Vec<RewritePlan>,
}

#[derive(Clone, Copy)]
enum PlainOpKind {
    Add,
    Sub,
    Mul,
    SnegAsSubZero,
    EvmUdiv,
    EvmUmod,
    EvmSdiv,
    EvmSmod,
}

#[derive(Clone)]
struct RewritePlan {
    inst: InstId,
    kind: PlainOpKind,
}

impl CheckedArithElim {
    pub fn new() -> Self {
        Self { plans: Vec::new() }
    }

    pub fn run(
        &mut self,
        func: &mut Function,
        cfg: &ControlFlowGraph,
        dom: &DomTree,
        lpt: &LoopTree,
    ) -> bool {
        if !has_supported_checked_arith(func) {
            return false;
        }

        self.plans.clear();

        let mut analysis = RangeAnalysis::default();
        analysis.compute(func, cfg, dom, lpt);

        for block in func.layout.iter_block() {
            if !analysis.is_reachable(block) {
                continue;
            }

            let mut env = analysis.entry_env(block).clone();
            for inst in func.layout.iter_inst(block) {
                if func.dfg.is_phi(inst) {
                    continue;
                }

                if let Some(plan) = plan_inst(func, &analysis, &env, inst) {
                    self.plans.push(plan);
                }

                analysis.transfer_inst(func, &mut env, inst);
            }
        }

        if self.plans.is_empty() {
            return false;
        }

        for plan in self.plans.drain(..) {
            apply_plan(func, plan);
        }

        true
    }
}

/// A checked operation the range facts prove cannot overflow, or an unsigned
/// subtraction a dominating comparison guards.
fn plan_inst(
    func: &Function,
    analysis: &RangeAnalysis,
    env: &RangeEnv,
    inst: InstId,
) -> Option<RewritePlan> {
    let kind = match func.dfg.inst(inst).kind() {
        InstClassKind::Unary(UnaryInstKind::Snego) => PlainOpKind::SnegAsSubZero,
        InstClassKind::Binary(kind) => match kind {
            BinaryInstKind::Uaddo | BinaryInstKind::Saddo => PlainOpKind::Add,
            BinaryInstKind::Usubo | BinaryInstKind::Ssubo => PlainOpKind::Sub,
            BinaryInstKind::Umulo | BinaryInstKind::Smulo => PlainOpKind::Mul,
            BinaryInstKind::EvmUdivo => PlainOpKind::EvmUdiv,
            BinaryInstKind::EvmUmodo => PlainOpKind::EvmUmod,
            BinaryInstKind::EvmSdivo => PlainOpKind::EvmSdiv,
            BinaryInstKind::EvmSmodo => PlainOpKind::EvmSmod,
            _ => return None,
        },
        _ => return None,
    };
    (analysis.is_guarded_sub(inst) || checked_value_fact(func, env, inst).is_some())
        .then_some(RewritePlan { inst, kind })
}

impl Default for CheckedArithElim {
    fn default() -> Self {
        Self::new()
    }
}

pub(crate) fn has_supported_checked_arith(func: &Function) -> bool {
    func.layout.iter_block().any(|block| {
        func.layout.iter_inst(block).any(|inst| {
            matches!(
                func.dfg.inst(inst).kind(),
                InstClassKind::Unary(UnaryInstKind::Snego)
                    | InstClassKind::Binary(
                        BinaryInstKind::Uaddo
                            | BinaryInstKind::Usubo
                            | BinaryInstKind::Umulo
                            | BinaryInstKind::Saddo
                            | BinaryInstKind::Ssubo
                            | BinaryInstKind::Smulo
                            | BinaryInstKind::EvmUdivo
                            | BinaryInstKind::EvmUmodo
                            | BinaryInstKind::EvmSdivo
                            | BinaryInstKind::EvmSmodo
                    )
            )
        })
    })
}

fn apply_plan(func: &mut Function, plan: RewritePlan) {
    if !func.layout.is_inst_inserted(plan.inst) {
        return;
    }

    let Some(value_result) = func.dfg.inst_result_at(plan.inst, 0) else {
        return;
    };
    let Some(overflow_result) = func.dfg.inst_result_at(plan.inst, 1) else {
        return;
    };

    let false_value = func.dfg.make_imm_value(false);
    func.dfg.change_to_alias(overflow_result, false_value);

    if func.dfg.users_num(value_result) != 0 {
        let args = func.dfg.inst(plan.inst).collect_values();
        let plain_value = insert_plain_value(
            func,
            plan.inst,
            plan.kind,
            &args,
            func.dfg.value_ty(value_result),
        );
        func.dfg.change_to_alias(value_result, plain_value);
    }

    func.layout.remove_inst(plan.inst);
    func.erase_inst(plan.inst);
}

fn insert_plain_value(
    func: &mut Function,
    before: InstId,
    kind: PlainOpKind,
    args: &[ValueId],
    ty: Type,
) -> ValueId {
    let is = func.inst_set();
    let inst = match kind {
        PlainOpKind::Add => {
            let [lhs, rhs] = args else {
                panic!("add rewrite requires two arguments");
            };
            func.dfg.make_inst(Add::new_unchecked(is, *lhs, *rhs))
        }
        PlainOpKind::Sub => {
            let [lhs, rhs] = args else {
                panic!("sub rewrite requires two arguments");
            };
            func.dfg.make_inst(Sub::new_unchecked(is, *lhs, *rhs))
        }
        PlainOpKind::Mul => {
            let [lhs, rhs] = args else {
                panic!("mul rewrite requires two arguments");
            };
            func.dfg.make_inst(Mul::new_unchecked(is, *lhs, *rhs))
        }
        PlainOpKind::SnegAsSubZero => {
            let [arg] = args else {
                panic!("sneg rewrite requires one argument");
            };
            let zero = func.dfg.make_imm_value(Immediate::zero(ty));
            func.dfg.make_inst(Sub::new_unchecked(is, zero, *arg))
        }
        PlainOpKind::EvmUdiv => {
            let [lhs, rhs] = args else {
                panic!("evm_udiv rewrite requires two arguments");
            };
            func.dfg.make_inst(EvmUdiv::new_unchecked(is, *lhs, *rhs))
        }
        PlainOpKind::EvmUmod => {
            let [lhs, rhs] = args else {
                panic!("evm_umod rewrite requires two arguments");
            };
            func.dfg.make_inst(EvmUmod::new_unchecked(is, *lhs, *rhs))
        }
        PlainOpKind::EvmSdiv => {
            let [lhs, rhs] = args else {
                panic!("evm_sdiv rewrite requires two arguments");
            };
            func.dfg.make_inst(EvmSdiv::new_unchecked(is, *lhs, *rhs))
        }
        PlainOpKind::EvmSmod => {
            let [lhs, rhs] = args else {
                panic!("evm_smod rewrite requires two arguments");
            };
            func.dfg.make_inst(EvmSmod::new_unchecked(is, *lhs, *rhs))
        }
    };
    let value = func.dfg.make_value(Value::Inst {
        inst,
        result_idx: 0,
        ty,
    });
    func.dfg.attach_result(inst, value);
    func.layout.insert_inst_before(inst, before);
    func.propagate_inst_attribution(inst, before);
    value
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::ir_writer::FuncWriter;

    fn optimized(source: &str) -> String {
        let module = sonatina_parser::parse_module(source).unwrap().module;
        let config = sonatina_verifier::VerifierConfig::for_level(
            sonatina_verifier::VerificationLevel::Full,
        );
        assert!(!sonatina_verifier::verify_module(&module, &config).has_errors());
        let id = module.funcs()[0];
        module.func_store.modify(id, |func| {
            let mut cfg = ControlFlowGraph::default();
            cfg.compute(func);
            let mut dom = DomTree::default();
            dom.compute(&cfg);
            let mut loops = LoopTree::default();
            loops.compute(&cfg, &dom);
            CheckedArithElim::new().run(func, &cfg, &dom, &loops);
        });
        let after = sonatina_verifier::verify_module(&module, &config);
        assert!(!after.has_errors(), "invalid output: {after:?}");
        module
            .func_store
            .view(id, |func| FuncWriter::new(id, func).dump_string())
    }

    #[test]
    fn guarded_unsigned_subtraction_proves_only_the_selected_relation() {
        for (comparison, operands, true_edge, safe) in [
            ("lt", "v1 v0", true, true),
            ("lt", "v0 v1", false, true),
            ("le", "v1 v0", true, true),
            ("le", "v0 v1", false, true),
            ("gt", "v0 v1", true, true),
            ("ge", "v0 v1", true, true),
            ("eq", "v0 v1", true, true),
            ("ne", "v0 v1", false, true),
            ("lt", "v0 v1", true, false),
            ("lt", "v1 v0", false, false),
            ("slt", "v1 v0", true, false),
            ("eq", "v0 v1", false, false),
        ] {
            let destinations = if true_edge {
                "block1 block2"
            } else {
                "block2 block1"
            };
            let text = optimized(&format!(
                r#"
target = "evm-ethereum-osaka"
func public %test() -> i1 {{
 block0:
  v20.i256 = evm_call_value;
  v0.i32 = trunc v20 i32;
  v21.i256 = evm_gas_price;
  v1.i32 = trunc v21 i32;
  v2.i1 = {comparison} {operands};
  br v2 {destinations};
 block1:
  (v3.i32, v4.i1) = usubo v0 v1;
  return v4;
 block2:
  return 0.i1;
}}
"#
            ));
            assert_eq!(
                !text.contains("usubo"),
                safe,
                "{comparison} {operands}, true_edge={true_edge}: {text}"
            );
        }
    }

    #[test]
    fn guarded_subtraction_does_not_cross_an_unguarded_merge() {
        let text = optimized(
            r#"
target = "evm-ethereum-osaka"
func public %test() -> i1 {
 block0:
  v20.i256 = evm_call_value;
  v0.i32 = trunc v20 i32;
  v21.i256 = evm_gas_price;
  v1.i32 = trunc v21 i32;
  v2.i1 = lt v1 v0;
  br v2 block1 block2;
 block1:
  jump block3;
 block2:
  jump block3;
 block3:
  (v3.i32, v4.i1) = usubo v0 v1;
  return v4;
}
"#,
        );
        assert!(text.contains("usubo"), "{text}");
    }

    #[test]
    fn guarded_subtraction_does_not_follow_changed_loop_operands() {
        let text = optimized(
            r#"
target = "evm-ethereum-osaka"
func public %test() -> i1 {
 block0:
  v20.i256 = evm_call_value;
  v0.i32 = trunc v20 i32;
  v21.i256 = evm_gas_price;
  v1.i32 = trunc v21 i32;
  v2.i1 = lt v1 v0;
  br v2 block1 block4;
 block1:
  jump block2;
 block2:
  v3.i32 = phi (v0 block1) (v6 block3);
  (v4.i32, v5.i1) = usubo v3 v1;
  br v5 block4 block3;
 block3:
  v6.i32 = sub v3 1.i32;
  jump block2;
 block4:
  return 0.i1;
}
"#,
        );
        assert!(text.contains("usubo"), "{text}");
    }

    #[test]
    fn guarded_subtraction_keeps_undef_dependent_checks() {
        let text = optimized(
            r#"
target = "evm-ethereum-osaka"
func public %test() -> i1 {
 block0:
  v20.i256 = evm_call_value;
  v0.i32 = trunc v20 i32;
  v1.i32 = add undef.i32 v0;
  v2.i1 = lt v1 v0;
  br v2 block1 block2;
 block1:
  (v3.i32, v4.i1) = usubo v0 v1;
  return v4;
 block2:
  return 0.i1;
}
"#,
        );
        // Each use of `v1` may see a different value, so the comparison
        // proves nothing about the subtraction.
        assert!(text.contains("usubo"), "{text}");
    }
    #[test]
    fn guarded_subtraction_keeps_intrinsically_undefined_checks() {
        for operation in [
            "udiv", "sdiv", "umod", "smod", "evm_udiv", "evm_sdiv", "evm_umod", "evm_smod",
        ] {
            for divisor in ["v1", "0.i256", "7.i256"] {
                let text = optimized(&format!(
                    r#"
target = "evm-ethereum-osaka"
func public %test() -> i1 {{
 block0:
  v0.i256 = evm_call_value;
  v1.i256 = evm_gas_price;
  v2.i256 = {operation} v0 {divisor};
  v3.i1 = ge v0 v2;
  br v3 block1 block2;
 block1:
  (v4.i256, v5.i1) = usubo v0 v2;
  return v5;
 block2:
  return 0.i1;
}}
"#
                ));
                let defined = operation.starts_with("evm_") || divisor == "7.i256";
                assert_eq!(
                    text.contains("usubo"),
                    !defined,
                    "{operation} {divisor}: {text}"
                );
            }
        }
    }

    #[test]
    fn guarded_subtraction_trusts_parameters() {
        for linkage in ["private", "public"] {
            for (args, rhs) in [("undef.i256 7.i256", "v1"), ("7.i256 undef.i256", "v2")] {
                let text = optimized(&format!(
                    r#"
target = "evm-ethereum-osaka"
func {linkage} %test(v0.i256, v1.i256) -> i1 {{
 block0:
  v2.i256 = add v1 1.i256;
  v3.i1 = ge v0 {rhs};
  br v3 block1 block2;
 block1:
  (v4.i256, v5.i1) = usubo v0 {rhs};
  return v5;
 block2:
  return 0.i1;
}}
func public %caller() -> i1 {{
 block0:
  v0.i1 = call %test {args};
  return v0;
}}
"#
                ));
                assert!(!text.contains("usubo"), "{linkage}, {args}: {text}");
            }
        }
    }

    #[test]
    fn guarded_subtraction_trusts_call_and_read_results() {
        for producer in [
            "v2.i256 = call %source;",
            "v7.objref<i256> = obj.alloc i256;\n  v2.i256 = obj.load v7;",
            "v7.*i256 = alloca i256;\n  v2.i256 = mload v7 i256;",
        ] {
            let text = optimized(&format!(
                r#"
target = "evm-ethereum-osaka"
func public %test() -> i1 {{
 block0:
  v0.i256 = evm_call_value;
  {producer}
  v3.i256 = add v2 1.i256;
  v4.i1 = ge v0 v3;
  br v4 block1 block2;
 block1:
  (v5.i256, v6.i1) = usubo v0 v3;
  return v6;
 block2:
  return 0.i1;
}}
func private %source() -> i256 {{
 block0:
  return undef.i256;
}}
"#
            ));
            assert!(!text.contains("usubo"), "{producer}: {text}");
        }
    }

    #[test]
    fn guarded_subtraction_restores_outer_facts_after_nested_duplicate() {
        let text = optimized(
            r#"
target = "evm-ethereum-osaka"
func public %test() -> i1 {
 block0:
  v20.i256 = evm_call_value;
  v0.i32 = trunc v20 i32;
  v21.i256 = evm_gas_price;
  v1.i32 = trunc v21 i32;
  v2.i1 = ge v0 v1;
  br v2 block1 block4;
 block1:
  v3.i1 = ge v0 v1;
  br v3 block2 block3;
 block2:
  (v4.i32, v5.i1) = usubo v0 v1;
  return v5;
 block3:
  (v6.i32, v7.i1) = usubo v0 v1;
  return v7;
 block4:
  (v8.i32, v9.i1) = usubo v0 v1;
  return v9;
}
"#,
        );
        assert_eq!(text.matches("usubo").count(), 1, "{text}");
    }

    #[test]
    fn guarded_subtraction_carries_facts_through_a_long_block_chain() {
        let mut source = String::from(
            r#"
target = "evm-ethereum-osaka"
func public %test() -> i1 {
 block0:
  v20.i256 = evm_call_value;
  v0.i32 = trunc v20 i32;
  v21.i256 = evm_gas_price;
  v1.i32 = trunc v21 i32;
  v2.i1 = ge v0 v1;
  br v2 block1 block2050;
"#,
        );
        for block in 1..2048 {
            source.push_str(&format!(" block{block}:\n  jump block{};\n", block + 1));
        }
        source.push_str(
            r#"
 block2048:
  (v3.i32, v4.i1) = usubo v0 v1;
  return v4;
 block2050:
  return 0.i1;
}
"#,
        );
        let text = optimized(&source);
        assert!(!text.contains("usubo"), "{text}");
    }
}
