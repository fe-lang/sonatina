use rustc_hash::FxHashSet;
use sonatina_ir::{
    BlockId, ControlFlowGraph, Function, Immediate, InstId, Type, Value, ValueId,
    inst::{
        BinaryInstKind, InstClassKind, UnaryInstKind,
        arith::{Add, Mul, Sub},
        control_flow::BranchKind,
        evm::{EvmSdiv, EvmSmod, EvmUdiv, EvmUmod},
    },
};

use crate::{
    domtree::DomTree,
    loop_analysis::LoopTree,
    range_analysis::{RangeAnalysis, checked_value_fact, transfer_inst},
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
        func.rebuild_users();
        // An undef choice cannot establish a reusable relation, so guards that
        // depend on undef (including through phi cycles) prove nothing.
        let undef_dependent = undef_dependent_values(func);

        let mut analysis = RangeAnalysis::default();
        analysis.compute(func, cfg, lpt);

        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            if !analysis.is_reachable(block) {
                continue;
            }

            let mut env = analysis.entry_env(block).clone();
            let guards: Vec<_> = dominating_guards(func, cfg, dom, block)
                .into_iter()
                .filter(|(condition, _)| !undef_dependent.contains(condition))
                .collect();
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if func.dfg.is_phi(inst) {
                    continue;
                }

                if let Some(plan) = self.plan_inst(func, &env, &guards, inst) {
                    self.plans.push(plan);
                }

                transfer_inst(func, &mut env, inst);
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

    fn plan_inst(
        &self,
        func: &Function,
        env: &crate::range_analysis::RangeEnv,
        guards: &[(ValueId, bool)],
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
        if checked_value_fact(func, env, inst).is_none() {
            if func.dfg.inst(inst).kind() != InstClassKind::Binary(BinaryInstKind::Usubo) {
                return None;
            }
            let args = func.dfg.inst(inst).collect_values();
            let [lhs, rhs] = args.as_slice() else {
                return None;
            };
            if !guards.iter().any(|&(condition, truth)| {
                guard_proves_unsigned_ge(func, condition, truth, *lhs, *rhs)
            }) {
                return None;
            }
        }

        Some(RewritePlan { inst, kind })
    }
}

/// Conservative forward taint from undef values, including phi cycles. Each
/// value is queued once. Partial aggregate initialization may overtaint later
/// extracts, which only costs a missed proof.
fn undef_dependent_values(func: &Function) -> FxHashSet<ValueId> {
    let mut tainted: FxHashSet<_> = func
        .dfg
        .values_iter()
        .filter_map(|(id, value)| matches!(value, Value::Undef { .. }).then_some(id))
        .collect();
    let mut pending: Vec<_> = tainted.iter().copied().collect();
    while let Some(value) = pending.pop() {
        for &user in func.dfg.users(value) {
            for &result in func.dfg.inst_results(user) {
                if tainted.insert(result) {
                    pending.push(result);
                }
            }
        }
    }
    tainted
}

/// Collect branch facts only where the selected edge dominates this block.
/// A single-predecessor dominator child certifies that edge without a second
/// graph traversal. Ordinary merges and loop headers with backedges do not
/// create facts. SSA operand identity prevents reuse for a changed value.
fn dominating_guards(
    func: &Function,
    cfg: &ControlFlowGraph,
    dom: &DomTree,
    mut child: BlockId,
) -> Vec<(ValueId, bool)> {
    let mut guards = Vec::new();
    while let Some(parent) = dom.idom_of(child) {
        let mut predecessors = cfg.preds_of(child).copied();
        if predecessors.next() == Some(parent)
            && predecessors.next().is_none()
            && let Some(branch) = func
                .layout
                .last_inst_of(parent)
                .and_then(|term| func.dfg.branch_info(term))
            && let BranchKind::Br(br) = branch.branch_kind()
            && br.nz_dest() != br.z_dest()
        {
            guards.push((*br.cond(), *br.nz_dest() == child));
        }
        child = parent;
    }
    guards
}

/// Deliberately unsigned and pairwise: overlapping independent intervals may
/// lose `lhs >= rhs`, but a dominating comparison of these exact values proves
/// subtraction safe. No transitivity, signed reinterpretation or loop-carried
/// relational environment is assumed.
fn guard_proves_unsigned_ge(
    func: &Function,
    condition: ValueId,
    truth: bool,
    lhs: ValueId,
    rhs: ValueId,
) -> bool {
    let Some(inst) = func.dfg.value_inst(condition) else {
        return false;
    };
    let InstClassKind::Binary(kind) = func.dfg.inst(inst).kind() else {
        return false;
    };
    let args = func.dfg.inst(inst).collect_values();
    let [a, b] = args.as_slice() else {
        return false;
    };
    let forward = *a == lhs && *b == rhs;
    let reverse = *a == rhs && *b == lhs;
    match (kind, truth) {
        (BinaryInstKind::Lt | BinaryInstKind::Le, true)
        | (BinaryInstKind::Gt | BinaryInstKind::Ge, false) => reverse,
        (BinaryInstKind::Lt | BinaryInstKind::Le, false)
        | (BinaryInstKind::Gt | BinaryInstKind::Ge, true) => forward,
        (BinaryInstKind::Eq, true) | (BinaryInstKind::Ne, false) => forward || reverse,
        _ => false,
    }
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
func public %test(v0.i32, v1.i32) -> i1 {{
 block0:
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
func public %test(v0.i32, v1.i32) -> i1 {
 block0:
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
func public %test(v0.i32, v1.i32) -> i1 {
 block0:
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
    fn guarded_subtraction_rejects_undef_dependent_relations() {
        let text = optimized(
            r#"
target = "evm-ethereum-osaka"
func public %test(v0.i32) -> i1 {
 block0:
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
        assert!(text.contains("usubo"), "{text}");
    }
}
