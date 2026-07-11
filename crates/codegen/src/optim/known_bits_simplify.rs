use std::cell::RefCell;

use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    ControlFlowGraph, Function, Immediate, InstId, Value, ValueId,
    inst::{BinaryInstKind, InstClassKind},
};

use crate::{
    analysis::{
        known_bits::{KnownBits, type_mask},
        scalar_facts::ScalarFacts,
    },
    domtree::DomTree,
    loop_analysis::LoopTree,
    range_analysis::{RangeAnalysis, RangeEnv, RangeFact, transfer_inst},
};

use super::simplify_expr::{
    ExprFactProvider, SimplifiedResult, simplify_binary_with_facts, simplify_unary_with_same_inner,
};

pub struct KnownBitsSimplify {
    plans: Vec<RewritePlan>,
}

#[derive(Clone, Copy)]
enum RewritePlan {
    Const {
        inst: InstId,
        result: ValueId,
        imm: Immediate,
    },
    Copy {
        inst: InstId,
        result: ValueId,
        replacement: ValueId,
    },
}

#[derive(Clone, Copy)]
enum ResolvedReplacement {
    Const(Immediate),
    Copy(ValueId),
}

struct LocalExprFacts<'a, 'b> {
    func: &'a Function,
    scalar_facts: &'b ScalarFacts<'a, 'b>,
    range_env: Option<&'b RangeEnv>,
    may_be_undef: &'b RefCell<FxHashMap<ValueId, bool>>,
}

impl ExprFactProvider for LocalExprFacts<'_, '_> {
    fn known_imm(&self, v: ValueId) -> Option<Immediate> {
        self.func.dfg.value_imm(v)
    }

    fn known_bits(&self, func: &Function, v: ValueId) -> KnownBits {
        if let Some(imm) = self.known_imm(v) {
            return KnownBits::from_imm(imm);
        }

        debug_assert_eq!(func.dfg.value_ty(v), self.func.dfg.value_ty(v));
        self.scalar_facts.known_bits(v)
    }

    fn range(&self, value: ValueId) -> Option<RangeFact> {
        self.range_env.and_then(|env| env.get(&value).copied())
    }

    fn same_non_undef(&self, lhs: ValueId, rhs: ValueId) -> bool {
        lhs == rhs && !self.may_be_undef(lhs)
    }

    fn may_be_undef(&self, v: ValueId) -> bool {
        if let Some(may_be_undef) = self.may_be_undef.borrow().get(&v).copied() {
            return may_be_undef;
        }

        let mut cache = self.may_be_undef.borrow_mut();
        let mut visiting = FxHashSet::default();
        let mut stack = vec![(v, false)];
        while let Some((value, post_order)) = stack.pop() {
            if cache.contains_key(&value) {
                continue;
            }

            if post_order {
                visiting.remove(&value);
                let may_be_undef = match self.func.dfg.value(value) {
                    Value::Undef { .. } => true,
                    Value::Immediate { .. } | Value::Arg { .. } | Value::Global { .. } => false,
                    Value::Inst { inst, .. } => inst_result_may_be_undef(self.func, *inst, &cache),
                };
                cache.insert(value, may_be_undef);
                continue;
            }

            if !visiting.insert(value) {
                cache.insert(value, true);
                continue;
            }

            stack.push((value, true));
            if let Value::Inst { inst, .. } = self.func.dfg.value(value) {
                for used in self.func.dfg.inst(*inst).collect_values().into_iter().rev() {
                    if cache.contains_key(&used) {
                        continue;
                    }

                    if visiting.contains(&used) {
                        cache.insert(used, true);
                    } else {
                        stack.push((used, false));
                    }
                }
            }
        }

        cache.get(&v).copied().unwrap_or(true)
    }
}

impl KnownBitsSimplify {
    pub fn new() -> Self {
        Self { plans: Vec::new() }
    }

    pub fn run(&mut self, func: &mut Function) -> bool {
        self.plans.clear();

        let scalar_facts = ScalarFacts::new(func);
        let mut range_analysis = None;
        if has_integral_and(func) {
            let mut cfg = ControlFlowGraph::new();
            cfg.compute(func);

            let mut dom = DomTree::new();
            dom.compute(&cfg);

            let mut lpt = LoopTree::new();
            lpt.compute(&cfg, &dom);

            let mut analysis = RangeAnalysis::default();
            analysis.compute(func, &cfg, &lpt);
            range_analysis = Some(analysis);
        }

        let may_be_undef = RefCell::default();
        let blocks: Vec<_> = func.layout.iter_block().collect();
        for block in blocks {
            let mut range_env = range_analysis
                .as_ref()
                .filter(|analysis| analysis.is_reachable(block))
                .map(|analysis| analysis.entry_env(block).clone());

            for inst in func.layout.iter_inst(block) {
                let facts = LocalExprFacts {
                    func,
                    scalar_facts: &scalar_facts,
                    range_env: range_env.as_ref(),
                    may_be_undef: &may_be_undef,
                };
                if let Some(plan) = self.plan_inst(func, &facts, inst) {
                    self.plans.push(plan);
                }

                if let Some(range_env) = range_env.as_mut()
                    && !func.dfg.is_phi(inst)
                {
                    transfer_inst(func, range_env, inst);
                }
            }
        }

        if self.plans.is_empty() {
            return false;
        }

        let resolved = resolve_replacements(&self.plans);
        for &plan in &self.plans {
            apply_plan(func, plan, &resolved);
        }

        for plan in self.plans.drain(..) {
            remove_rewritten_inst(func, plan);
        }

        true
    }

    fn plan_inst(
        &self,
        func: &Function,
        facts: &LocalExprFacts<'_, '_>,
        inst: InstId,
    ) -> Option<RewritePlan> {
        let [result] = func.dfg.inst_results(inst) else {
            return None;
        };
        let inst_data = func.dfg.inst(inst);
        let simplified = match inst_data.kind() {
            InstClassKind::Unary(kind) => {
                let args = inst_data.collect_values();
                let [arg] = args.as_slice() else {
                    return None;
                };

                simplify_unary_with_same_inner(kind, *arg, |arg, expected| {
                    let sonatina_ir::Value::Inst { inst, .. } = func.dfg.value(arg) else {
                        return None;
                    };
                    if !matches!(func.dfg.inst(*inst).kind(), InstClassKind::Unary(inner) if inner == expected)
                    {
                        return None;
                    }

                    let inner_values = func.dfg.inst(*inst).collect_values();
                    let [inner_arg] = inner_values.as_slice() else {
                        return None;
                    };
                    Some(*inner_arg)
                })
            }
            InstClassKind::Binary(kind) => {
                let args = inst_data.collect_values();
                let [lhs, rhs] = args.as_slice() else {
                    return None;
                };
                let shared = simplify_binary_with_facts(func, kind, *lhs, *rhs, facts);
                if !shared.is_no_change() {
                    shared
                } else {
                    simplify_binary_with_demanded_bits(
                        func,
                        kind,
                        *lhs,
                        *rhs,
                        func.dfg.inst_result(inst)?,
                        facts,
                    )
                }
            }
            InstClassKind::Cast(_) => SimplifiedResult::NoChange,
            InstClassKind::Phi | InstClassKind::Opaque => SimplifiedResult::NoChange,
        };

        match simplified {
            SimplifiedResult::Const(imm) if imm.ty() == func.dfg.value_ty(*result) => {
                Some(RewritePlan::Const {
                    inst,
                    result: *result,
                    imm,
                })
            }
            SimplifiedResult::Copy(replacement)
                if func.dfg.value_ty(replacement) == func.dfg.value_ty(*result) =>
            {
                Some(RewritePlan::Copy {
                    inst,
                    result: *result,
                    replacement,
                })
            }
            SimplifiedResult::Const(_) | SimplifiedResult::Copy(_) => None,
            SimplifiedResult::NoChange => None,
        }
    }
}

fn has_integral_and(func: &Function) -> bool {
    func.layout.iter_block().any(|block| {
        func.layout.iter_inst(block).any(|inst| {
            let [result] = func.dfg.inst_results(inst) else {
                return false;
            };
            func.dfg.inst(inst).kind() == InstClassKind::Binary(BinaryInstKind::And)
                && func.dfg.value_ty(*result).is_integral()
        })
    })
}

impl Default for KnownBitsSimplify {
    fn default() -> Self {
        Self::new()
    }
}

fn simplify_binary_with_demanded_bits(
    func: &Function,
    kind: BinaryInstKind,
    lhs: ValueId,
    rhs: ValueId,
    result: ValueId,
    facts: &LocalExprFacts<'_, '_>,
) -> SimplifiedResult {
    match kind {
        BinaryInstKind::And => simplify_copy_when_only_undemanded_bits_change(
            func,
            lhs,
            rhs,
            result,
            facts,
            |ty, imm| type_mask(ty) & !KnownBits::from_imm(imm).known_one,
        )
        .or_else(|| {
            simplify_copy_when_only_undemanded_bits_change(
                func,
                rhs,
                lhs,
                result,
                facts,
                |ty, imm| type_mask(ty) & !KnownBits::from_imm(imm).known_one,
            )
        })
        .map_or(SimplifiedResult::NoChange, SimplifiedResult::Copy),
        BinaryInstKind::Or | BinaryInstKind::Xor => simplify_copy_when_only_undemanded_bits_change(
            func,
            lhs,
            rhs,
            result,
            facts,
            |ty, imm| KnownBits::from_imm(imm).known_one & type_mask(ty),
        )
        .or_else(|| {
            simplify_copy_when_only_undemanded_bits_change(
                func,
                rhs,
                lhs,
                result,
                facts,
                |ty, imm| KnownBits::from_imm(imm).known_one & type_mask(ty),
            )
        })
        .map_or(SimplifiedResult::NoChange, SimplifiedResult::Copy),
        _ => SimplifiedResult::NoChange,
    }
}

fn simplify_copy_when_only_undemanded_bits_change(
    func: &Function,
    value: ValueId,
    const_arg: ValueId,
    result: ValueId,
    facts: &LocalExprFacts<'_, '_>,
    affected_bits: impl Fn(sonatina_ir::Type, Immediate) -> sonatina_ir::U256,
) -> Option<ValueId> {
    if facts.may_be_undef(value) {
        return None;
    }

    let ty = func.dfg.value_ty(value);
    let imm = facts.known_imm(const_arg)?;
    let changed = affected_bits(ty, imm);
    (facts.scalar_facts.demanded_bits(result) & changed == sonatina_ir::U256::zero())
        .then_some(value)
}

fn inst_result_may_be_undef(
    func: &Function,
    inst: InstId,
    cache: &FxHashMap<ValueId, bool>,
) -> bool {
    let inst_data = func.dfg.inst(inst);
    let values = inst_data.collect_values();
    if values
        .iter()
        .copied()
        .any(|value| cache.get(&value).copied().unwrap_or(true))
    {
        return true;
    }

    if let InstClassKind::Binary(kind) = inst_data.kind()
        && matches!(
            kind,
            BinaryInstKind::Udiv
                | BinaryInstKind::Sdiv
                | BinaryInstKind::Umod
                | BinaryInstKind::Smod
        )
    {
        let [_, rhs] = values.as_slice() else {
            return true;
        };
        return func.dfg.value_imm(*rhs).is_none_or(Immediate::is_zero);
    }

    false
}

fn resolve_replacements(plans: &[RewritePlan]) -> FxHashMap<ValueId, ResolvedReplacement> {
    let rewrites: FxHashMap<_, _> = plans
        .iter()
        .copied()
        .map(|plan| {
            (
                plan.result(),
                match plan {
                    RewritePlan::Const { imm, .. } => ResolvedReplacement::Const(imm),
                    RewritePlan::Copy { replacement, .. } => ResolvedReplacement::Copy(replacement),
                },
            )
        })
        .collect();
    let mut resolved = FxHashMap::default();

    for &result in rewrites.keys() {
        resolve_replacement(result, &rewrites, &mut resolved);
    }

    resolved
}

fn resolve_replacement(
    result: ValueId,
    rewrites: &FxHashMap<ValueId, ResolvedReplacement>,
    resolved: &mut FxHashMap<ValueId, ResolvedReplacement>,
) -> ResolvedReplacement {
    if let Some(&replacement) = resolved.get(&result) {
        return replacement;
    }

    let replacement = match rewrites[&result] {
        ResolvedReplacement::Const(imm) => ResolvedReplacement::Const(imm),
        ResolvedReplacement::Copy(value) if rewrites.contains_key(&value) => {
            debug_assert_ne!(value, result, "rewrite cycle on {result:?}");
            resolve_replacement(value, rewrites, resolved)
        }
        ResolvedReplacement::Copy(value) => ResolvedReplacement::Copy(value),
    };
    resolved.insert(result, replacement);
    replacement
}

fn apply_plan(
    func: &mut Function,
    plan: RewritePlan,
    resolved: &FxHashMap<ValueId, ResolvedReplacement>,
) {
    if !func.dfg.has_value(plan.result()) {
        return;
    }

    match resolved[&plan.result()] {
        ResolvedReplacement::Const(imm) => {
            let replacement = func.dfg.make_imm_value(imm);
            func.dfg.change_to_alias(plan.result(), replacement);
        }
        ResolvedReplacement::Copy(replacement) => {
            func.dfg.change_to_alias(plan.result(), replacement);
        }
    }
}

fn remove_rewritten_inst(func: &mut Function, plan: RewritePlan) {
    let inst = plan.inst();
    if !func.layout.is_inst_inserted(inst) {
        return;
    }

    func.layout.remove_inst(inst);
    func.erase_inst(inst);
}

impl RewritePlan {
    fn inst(self) -> InstId {
        match self {
            RewritePlan::Const { inst, .. } | RewritePlan::Copy { inst, .. } => inst,
        }
    }

    fn result(self) -> ValueId {
        match self {
            RewritePlan::Const { result, .. } | RewritePlan::Copy { result, .. } => result,
        }
    }
}
