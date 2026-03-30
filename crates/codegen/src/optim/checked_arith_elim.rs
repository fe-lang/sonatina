use sonatina_ir::{
    ControlFlowGraph, Function, Immediate, InstId, Type, Value, ValueId,
    inst::{
        BinaryInstKind, InstClassKind, UnaryInstKind,
        arith::{Add, Mul, Sub},
        evm::{EvmSdiv, EvmSmod, EvmUdiv, EvmUmod},
    },
};

use crate::{
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

    pub fn run(&mut self, func: &mut Function, cfg: &ControlFlowGraph, lpt: &LoopTree) -> bool {
        if !has_supported_checked_arith(func) {
            return false;
        }

        self.plans.clear();

        let mut analysis = RangeAnalysis::default();
        analysis.compute(func, cfg, lpt);

        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            if !analysis.is_reachable(block) {
                continue;
            }

            let mut env = analysis.entry_env(block).clone();
            let insts: Vec<_> = func.layout.iter_inst(block).collect();
            for inst in insts {
                if func.dfg.is_phi(inst) {
                    continue;
                }

                if let Some(plan) = self.plan_inst(func, &env, inst) {
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
        checked_value_fact(func, env, inst)?;

        Some(RewritePlan { inst, kind })
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
    value
}
