//! E-graph optimization pass for sonatina IR.

use crate::domtree::DomTree;

use egglog::{CommandOutput, EGraph};
use rustc_hash::{FxHashMap, FxHashSet};

use sonatina_ir::{
    ControlFlowGraph, Function, InstDowncast, InstId, Type, Value, ValueId,
    inst::{arith::*, cast::*, cmp::*, data::*, evm::*, logic::*},
};

use super::{EggTerm, Elaborator, func_to_egglog};

const TYPES: &str = include_str!("types.egg");
const EXPRS: &str = include_str!("expr.egg");
const RULES: &str = include_str!("rules.egg");
const MEMORY: &str = include_str!("memory.egg");

fn has_unknown_call_attrs(func: &Function) -> bool {
    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            if let Some(call) = func.dfg.call_info(inst_id)
                && func.ctx().func_attrs(call.callee()).is_empty()
            {
                return true;
            }
        }
    }

    false
}

/// Run e-graph optimization pass on a function.
/// Returns true if the function was modified.
pub fn run_egraph_pass(func: &mut Function) -> bool {
    if has_unknown_call_attrs(func) {
        debug_assert!(
            false,
            "run func_behavior::analyze_module before egraph on call-containing functions"
        );
        return false;
    }

    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    let mut dom = DomTree::new();
    dom.compute(&cfg);

    // Convert to egglog
    let program = func_to_egglog(func);
    let source_terms = collect_source_terms(func);

    // Build extraction queries for all instruction result values
    let mut full_program = program.clone();
    let mut extract_values = Vec::new();

    // Run rules to apply rewrites
    full_program.push_str("\n(run 10)");

    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            if let Some(result) = func.dfg.inst_result(inst_id) {
                let name = format!("v{}", result.as_u32());
                full_program.push_str(&format!("\n(extract {})", name));
                extract_values.push(result);
            }
        }
    }

    // Run egglog
    let mut egraph = EGraph::default();
    let full_with_rules = format!(
        "{}\n{}\n{}\n{}\n{}",
        TYPES, EXPRS, RULES, MEMORY, full_program
    );

    let results = match egraph.parse_and_run_program(None, &full_with_rules) {
        Ok(r) => r,
        Err(err) => {
            if std::env::var_os("SONATINA_EGRAPH_DEBUG").is_some() {
                eprintln!("{err}");
            }
            return false;
        }
    };

    let mut parsed_terms: FxHashMap<ValueId, EggTerm> = FxHashMap::default();
    let mut extract_results = results.iter().filter_map(extract_output_to_string);
    for &original_val in &extract_values {
        let Some(result) = extract_results.next() else {
            break;
        };
        let result = result.trim();

        let Some(term) = EggTerm::parse(result, func).map(EggTerm::canonicalize) else {
            continue;
        };
        parsed_terms.insert(original_val, term);
    }

    // Check results for simplifications
    let mut changed = false;
    let mut term_value_candidates: FxHashMap<EggTerm, Vec<ValueId>> = FxHashMap::default();
    let mut resolved_terms: FxHashMap<ValueId, EggTerm> = FxHashMap::default();
    let mut resolving_terms: FxHashSet<ValueId> = FxHashSet::default();

    for &original_val in &extract_values {
        let Some(term) = resolve_extracted_term(
            original_val,
            &parsed_terms,
            &source_terms,
            &mut resolved_terms,
            &mut resolving_terms,
        ) else {
            continue;
        };
        let ty = func.dfg.value_ty(original_val);

        match term {
            EggTerm::Const(const_val, _term_ty) => {
                let imm_id = func
                    .dfg
                    .make_imm_value(sonatina_ir::Immediate::from_i256(const_val, ty));
                if imm_id != original_val {
                    func.dfg.change_to_alias(original_val, imm_id);
                    changed = true;
                }
            }
            EggTerm::Value(alias_val) => {
                if can_alias(func, &dom, original_val, alias_val) {
                    func.dfg.change_to_alias(original_val, alias_val);
                    changed = true;
                    continue;
                }

                let value_term = EggTerm::Value(alias_val);
                if let Some(existing_value) = find_dominating_term_value(
                    func,
                    &dom,
                    &term_value_candidates,
                    &value_term,
                    original_val,
                ) {
                    func.dfg.change_to_alias(original_val, existing_value);
                    changed = true;
                    continue;
                }

                if let Some(source_term) = source_terms.get(&original_val).cloned()
                    && !matches!(source_term, EggTerm::Value(value) if value == original_val)
                {
                    if let Some(existing_value) = find_dominating_term_value(
                        func,
                        &dom,
                        &term_value_candidates,
                        &source_term,
                        original_val,
                    ) {
                        func.dfg.change_to_alias(original_val, existing_value);
                        changed = true;
                        continue;
                    }

                    record_term_value_candidate(
                        &mut term_value_candidates,
                        source_term,
                        original_val,
                    );
                }

                record_term_value_candidate(&mut term_value_candidates, value_term, original_val);
            }
            EggTerm::Global(gv, _term_ty) => {
                let Some(original_inst) = func.dfg.value_inst(original_val) else {
                    continue;
                };
                if func.dfg.is_phi(original_inst) {
                    continue;
                }

                let global_val = func.dfg.make_global_value(gv);
                if can_alias(func, &dom, original_val, global_val) {
                    func.dfg.change_to_alias(original_val, global_val);
                    changed = true;
                }
            }
            EggTerm::Undef(term_ty) => {
                let Some(original_inst) = func.dfg.value_inst(original_val) else {
                    continue;
                };
                if func.dfg.is_phi(original_inst) {
                    continue;
                }
                let undef = func.dfg.make_undef_value(term_ty);
                if can_alias(func, &dom, original_val, undef) {
                    func.dfg.change_to_alias(original_val, undef);
                    changed = true;
                }
            }
            term => {
                let is = func.inst_set();
                if term.node_count() > 32
                    || !term.is_supported(is)
                    || term.contains_value(original_val)
                {
                    continue;
                }

                let Some(original_inst) = func.dfg.value_inst(original_val) else {
                    continue;
                };
                if func.dfg.is_phi(original_inst) {
                    continue;
                }

                if let Some(alias_val) = find_dominating_term_value(
                    func,
                    &dom,
                    &term_value_candidates,
                    &term,
                    original_val,
                ) {
                    func.dfg.change_to_alias(original_val, alias_val);
                    changed = true;
                    continue;
                }

                let mut dominates = true;
                term.for_each_value(&mut |value| {
                    dominates &= value_dominates_inst(func, &dom, value, original_inst);
                });
                if !dominates {
                    continue;
                }

                let mut elaborator = Elaborator::new(func, original_inst);
                if let Some(inst) = elaborator.build_inst(&term) {
                    func.dfg.replace_inst(original_inst, inst);
                    record_term_value_candidate(&mut term_value_candidates, term, original_val);
                    changed = true;
                }
            }
        }
    }

    if apply_term_cse(func, &dom, &mut term_value_candidates) {
        changed = true;
    }

    if eliminate_adjacent_dead_stores(func) {
        changed = true;
    }
    if eliminate_dead_pure_insts(func) {
        changed = true;
    }

    changed
}

fn apply_term_cse(
    func: &mut Function,
    dom: &DomTree,
    term_value_candidates: &mut FxHashMap<EggTerm, Vec<ValueId>>,
) -> bool {
    let mut changed = false;

    let blocks: Vec<_> = func.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = func.layout.iter_inst(block).collect();
        for inst_id in insts {
            let Some(result) = func.dfg.inst_result(inst_id) else {
                continue;
            };
            let Some(term) = source_term_for_inst(func, inst_id).map(EggTerm::canonicalize) else {
                continue;
            };
            if term.contains_value(result) {
                continue;
            }

            if let Some(existing_value) =
                find_dominating_term_value(func, dom, term_value_candidates, &term, result)
            {
                func.dfg.change_to_alias(result, existing_value);
                changed = true;
                continue;
            }

            record_term_value_candidate(term_value_candidates, term, result);
        }
    }

    changed
}

fn find_dominating_term_value(
    func: &Function,
    dom: &DomTree,
    term_value_candidates: &FxHashMap<EggTerm, Vec<ValueId>>,
    term: &EggTerm,
    original_val: ValueId,
) -> Option<ValueId> {
    term_value_candidates.get(term).and_then(|candidates| {
        candidates
            .iter()
            .rev()
            .copied()
            .find(|&candidate| can_alias(func, dom, original_val, candidate))
    })
}

fn record_term_value_candidate(
    term_value_candidates: &mut FxHashMap<EggTerm, Vec<ValueId>>,
    term: EggTerm,
    value: ValueId,
) {
    term_value_candidates.entry(term).or_default().push(value);
}

fn resolve_extracted_term(
    value: ValueId,
    parsed_terms: &FxHashMap<ValueId, EggTerm>,
    source_terms: &FxHashMap<ValueId, EggTerm>,
    resolved_terms: &mut FxHashMap<ValueId, EggTerm>,
    resolving_terms: &mut FxHashSet<ValueId>,
) -> Option<EggTerm> {
    if let Some(term) = resolved_terms.get(&value) {
        return Some(term.clone());
    }
    let term = parsed_terms
        .get(&value)
        .cloned()
        .or_else(|| source_terms.get(&value).cloned())?;
    if !resolving_terms.insert(value) {
        return Some(term);
    }

    let resolved = match term {
        EggTerm::Value(alias_val) => resolve_value_term(
            value,
            alias_val,
            parsed_terms,
            source_terms,
            resolved_terms,
            resolving_terms,
        ),
        other => other,
    }
    .canonicalize();

    resolving_terms.remove(&value);
    resolved_terms.insert(value, resolved.clone());
    Some(resolved)
}

fn resolve_value_term(
    current_value: ValueId,
    alias_value: ValueId,
    parsed_terms: &FxHashMap<ValueId, EggTerm>,
    source_terms: &FxHashMap<ValueId, EggTerm>,
    resolved_terms: &mut FxHashMap<ValueId, EggTerm>,
    resolving_terms: &mut FxHashSet<ValueId>,
) -> EggTerm {
    if alias_value != current_value {
        if let Some(alias_term) = resolve_extracted_term(
            alias_value,
            parsed_terms,
            source_terms,
            resolved_terms,
            resolving_terms,
        ) && !matches!(alias_term, EggTerm::Value(value) if value == alias_value)
        {
            return alias_term;
        }

        return EggTerm::Value(alias_value);
    }

    if let Some(source_term) = source_terms.get(&current_value)
        && !matches!(source_term, EggTerm::Value(value) if *value == current_value)
    {
        return source_term.clone();
    }

    EggTerm::Value(alias_value)
}

fn collect_source_terms(func: &Function) -> FxHashMap<ValueId, EggTerm> {
    let mut terms = FxHashMap::default();
    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            let Some(result) = func.dfg.inst_result(inst_id) else {
                continue;
            };
            let Some(term) = source_term_for_inst(func, inst_id).map(EggTerm::canonicalize) else {
                continue;
            };
            terms.insert(result, term);
        }
    }
    terms
}

fn source_term_for_inst(func: &Function, inst_id: InstId) -> Option<EggTerm> {
    let inst = func.dfg.inst(inst_id);
    let is = func.inst_set();

    macro_rules! binary {
        ($inst_ty:ty, $ctor:expr) => {
            if let Some(inst_data) = <&$inst_ty>::downcast(is, inst) {
                return Some($ctor(
                    Box::new(value_to_source_term(func, *inst_data.lhs())),
                    Box::new(value_to_source_term(func, *inst_data.rhs())),
                ));
            }
        };
    }

    macro_rules! unary {
        ($inst_ty:ty, $ctor:expr) => {
            if let Some(inst_data) = <&$inst_ty>::downcast(is, inst) {
                return Some($ctor(Box::new(value_to_source_term(
                    func,
                    *inst_data.arg(),
                ))));
            }
        };
    }

    macro_rules! cast {
        ($inst_ty:ty, $ctor:expr) => {
            if let Some(inst_data) = <&$inst_ty>::downcast(is, inst) {
                return Some($ctor(
                    Box::new(value_to_source_term(func, *inst_data.from())),
                    *inst_data.ty(),
                ));
            }
        };
    }

    macro_rules! ternary {
        ($inst_ty:ty, $ctor:expr, $a:ident, $b:ident, $c:ident) => {
            if let Some(inst_data) = <&$inst_ty>::downcast(is, inst) {
                return Some($ctor(
                    Box::new(value_to_source_term(func, *inst_data.$a())),
                    Box::new(value_to_source_term(func, *inst_data.$b())),
                    Box::new(value_to_source_term(func, *inst_data.$c())),
                ));
            }
        };
    }

    binary!(Add, EggTerm::Add);
    binary!(Sub, EggTerm::Sub);
    binary!(Mul, EggTerm::Mul);
    binary!(Udiv, EggTerm::Udiv);
    binary!(Sdiv, EggTerm::Sdiv);
    binary!(Umod, EggTerm::Umod);
    binary!(Smod, EggTerm::Smod);
    unary!(Neg, EggTerm::Neg);

    binary!(EvmUdiv, EggTerm::Udiv);
    binary!(EvmSdiv, EggTerm::Sdiv);
    binary!(EvmUmod, EggTerm::Umod);
    binary!(EvmSmod, EggTerm::Smod);
    ternary!(EvmAddMod, EggTerm::EvmAddMod, lhs, rhs, modulus);
    ternary!(EvmMulMod, EggTerm::EvmMulMod, lhs, rhs, modulus);

    binary!(And, EggTerm::And);
    binary!(Or, EggTerm::Or);
    binary!(Xor, EggTerm::Xor);
    unary!(Not, EggTerm::Not);

    binary!(Lt, EggTerm::Lt);
    binary!(Gt, EggTerm::Gt);
    binary!(Le, EggTerm::Le);
    binary!(Ge, EggTerm::Ge);
    binary!(Slt, EggTerm::Slt);
    binary!(Sgt, EggTerm::Sgt);
    binary!(Sle, EggTerm::Sle);
    binary!(Sge, EggTerm::Sge);
    binary!(Eq, EggTerm::Eq);
    binary!(Ne, EggTerm::Ne);

    cast!(Sext, EggTerm::Sext);
    cast!(Zext, EggTerm::Zext);
    cast!(Trunc, EggTerm::Trunc);
    cast!(Bitcast, EggTerm::Bitcast);

    if let Some(inst_data) = <&Shl>::downcast(is, inst) {
        return Some(EggTerm::Shl(
            Box::new(value_to_source_term(func, *inst_data.bits())),
            Box::new(value_to_source_term(func, *inst_data.value())),
        ));
    }
    if let Some(inst_data) = <&Shr>::downcast(is, inst) {
        return Some(EggTerm::Shr(
            Box::new(value_to_source_term(func, *inst_data.bits())),
            Box::new(value_to_source_term(func, *inst_data.value())),
        ));
    }
    if let Some(inst_data) = <&Sar>::downcast(is, inst) {
        return Some(EggTerm::Sar(
            Box::new(value_to_source_term(func, *inst_data.bits())),
            Box::new(value_to_source_term(func, *inst_data.value())),
        ));
    }
    if let Some(inst_data) = <&EvmExp>::downcast(is, inst) {
        return Some(EggTerm::EvmExp(
            Box::new(value_to_source_term(func, *inst_data.base())),
            Box::new(value_to_source_term(func, *inst_data.exponent())),
        ));
    }
    if let Some(inst_data) = <&EvmByte>::downcast(is, inst) {
        return Some(EggTerm::EvmByte(
            Box::new(value_to_source_term(func, *inst_data.pos())),
            Box::new(value_to_source_term(func, *inst_data.value())),
        ));
    }
    if let Some(inst_data) = <&EvmClz>::downcast(is, inst) {
        return Some(EggTerm::EvmClz(Box::new(value_to_source_term(
            func,
            *inst_data.word(),
        ))));
    }
    if let Some(inst_data) = <&IsZero>::downcast(is, inst) {
        return Some(EggTerm::IsZero(Box::new(value_to_source_term(
            func,
            *inst_data.lhs(),
        ))));
    }
    if let Some(inst_data) = <&Gep>::downcast(is, inst) {
        let values = inst_data.values();
        if !values.is_empty() {
            let indices = values[1..]
                .iter()
                .map(|&value| value_to_source_term(func, value))
                .collect();
            return Some(EggTerm::Gep {
                base: Box::new(value_to_source_term(func, values[0])),
                indices,
            });
        }
    }

    None
}

fn value_to_source_term(func: &Function, value: ValueId) -> EggTerm {
    match func.dfg.value(value) {
        Value::Immediate { imm, ty } => EggTerm::Const(imm.as_i256(), *ty),
        Value::Global { gv, ty } => EggTerm::Global(*gv, *ty),
        Value::Undef { ty } => EggTerm::Undef(*ty),
        Value::Arg { .. } | Value::Inst { .. } => EggTerm::Value(value),
    }
}

fn extract_output_to_string(output: &CommandOutput) -> Option<String> {
    match output {
        CommandOutput::ExtractBest(termdag, _cost, term) => Some(termdag.to_string(*term)),
        CommandOutput::ExtractVariants(termdag, terms) => {
            terms.first().copied().map(|term| termdag.to_string(term))
        }
        _ => None,
    }
}

fn can_alias(func: &Function, dom: &DomTree, original_val: ValueId, alias_val: ValueId) -> bool {
    if original_val == alias_val {
        return false;
    }

    let Some(original_inst) = func.dfg.value_inst(original_val) else {
        return false;
    };

    value_dominates_inst(func, dom, alias_val, original_inst)
        && !inst_uses_value_directly(func, alias_val, original_val)
}

fn value_dominates_inst(func: &Function, dom: &DomTree, value: ValueId, inst: InstId) -> bool {
    match func.dfg.value(value) {
        Value::Arg { .. }
        | Value::Immediate { .. }
        | Value::Global { .. }
        | Value::Undef { .. } => true,
        Value::Inst { inst: def_inst, .. } => {
            if !func.layout.is_inst_inserted(*def_inst) {
                return false;
            }

            let def_block = func.layout.inst_block(*def_inst);
            let use_block = func.layout.inst_block(inst);
            if def_block != use_block {
                dom.dominates(def_block, use_block)
            } else {
                inst_precedes_or_equal(func, *def_inst, inst)
            }
        }
    }
}

fn inst_precedes_or_equal(func: &Function, earlier: InstId, later: InstId) -> bool {
    if earlier == later {
        return true;
    }

    let mut inst = Some(earlier);
    while let Some(id) = inst {
        if id == later {
            return true;
        }
        inst = func.layout.next_inst_of(id);
    }

    false
}

fn inst_uses_value_directly(func: &Function, inst_value: ValueId, value: ValueId) -> bool {
    let Some(inst_id) = func.dfg.value_inst(inst_value) else {
        return false;
    };

    let mut used = false;
    func.dfg.inst(inst_id).for_each_value(&mut |inst_value| {
        if inst_value == value {
            used = true;
        }
    });

    used
}

fn eliminate_adjacent_dead_stores(func: &mut Function) -> bool {
    let is = func.inst_set();
    let mut changed = false;

    let blocks: Vec<_> = func.layout.iter_block().collect();
    for block in blocks {
        let insts: Vec<_> = func.layout.iter_inst(block).collect();
        let mut prev_store: Option<(sonatina_ir::InstId, ValueId, Type)> = None;

        for inst_id in insts {
            let inst = func.dfg.inst(inst_id);
            if let Some(store) = <&Mstore>::downcast(is, inst) {
                let addr = *store.addr();
                let ty = *store.ty();
                if let Some((prev_id, prev_addr, prev_ty)) = prev_store
                    && prev_addr == addr
                    && prev_ty == ty
                {
                    func.dfg.untrack_inst(prev_id);
                    func.layout.remove_inst(prev_id);
                    changed = true;
                }

                prev_store = Some((inst_id, addr, ty));
            } else {
                prev_store = None;
            }
        }
    }

    changed
}

fn eliminate_dead_pure_insts(func: &mut Function) -> bool {
    let mut worklist = Vec::new();
    for block in func.layout.iter_block() {
        for inst in func.layout.iter_inst(block) {
            if is_trivially_dead_pure_inst(func, inst) {
                worklist.push(inst);
            }
        }
    }

    let mut changed = false;
    while let Some(inst) = worklist.pop() {
        if !func.layout.is_inst_inserted(inst) || !is_trivially_dead_pure_inst(func, inst) {
            continue;
        }

        let operands = func.dfg.inst(inst).collect_values();
        func.dfg.untrack_inst(inst);
        func.layout.remove_inst(inst);
        changed = true;

        for operand in operands {
            if let Some(def_inst) = func.dfg.value_inst(operand)
                && func.layout.is_inst_inserted(def_inst)
                && is_trivially_dead_pure_inst(func, def_inst)
            {
                worklist.push(def_inst);
            }
        }
    }

    changed
}

fn is_trivially_dead_pure_inst(func: &Function, inst: InstId) -> bool {
    if func.dfg.side_effect(inst).has_effect() || func.dfg.is_terminator(inst) {
        return false;
    }

    let Some(result) = func.dfg.inst_result(inst) else {
        return false;
    };

    func.dfg.users_num(result) == 0
}

#[cfg(test)]
mod tests {
    use sonatina_parser::parse_module;

    use super::*;

    #[test]
    fn test_egglog_parses() {
        let full = format!("{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY);
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, &full)
            .expect("egglog should parse successfully");
    }

    #[test]
    fn test_store_load_forward_egglog() {
        // Test the egglog rules directly to verify store-to-load forwarding works
        // Memory state 0 = InitMem, Memory state 1 = after store
        let program = r#"
(let v1 (AllocaResult 1 (I32)))
; Store 42 to v1, creating memory state 1
(set (store-prev 1) 0)
(set (store-addr 1) v1)
(set (store-val 1) (Const (i256 42) (I32)))
(set (store-ty 1) (I32))
; Load from memory state 1 at address v1
(let v2 (LoadResult 2 1 (I32)))
(set (load-addr 2) v1)

(run 10)
(extract v2)
"#;
        let full = format!("{}\n{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY, program);
        let mut egraph = EGraph::default();
        let results = egraph
            .parse_and_run_program(None, &full)
            .expect("egglog should run");
        // v2 should be unified with (Const 42 (I32))
        let mut extracted = results.iter().filter_map(extract_output_to_string);
        let result = extracted.next().expect("extract should return a result");
        assert!(result.contains("0x2a"), "Expected 0x2a, got: {result}");
        assert!(extracted.next().is_none());
    }

    #[test]
    fn test_load_pass_through_egglog() {
        // Test load pass-through: load from addr1 after store to addr2 (different alloca)
        // should read from the previous memory state
        // v1 = alloca1, v3 = alloca2 (different allocas, must-not-alias)
        // mem1 = store 10 to v1
        // mem2 = store 20 to v3
        // v5 = load from v1 at mem2 -> should be 10 (pass through mem2's store)
        let program = r#"
(let v1 (AllocaResult 1 (I32)))
(let v3 (AllocaResult 3 (I32)))
; Store 10 to v1, creating memory state 1
(set (store-prev 1) 0)
(set (store-addr 1) v1)
(set (store-val 1) (Const (i256 10) (I32)))
(set (store-ty 1) (I32))
; Store 20 to v3, creating memory state 2
(set (store-prev 2) 1)
(set (store-addr 2) v3)
(set (store-val 2) (Const (i256 20) (I32)))
(set (store-ty 2) (I32))
; Load from v1 at memory state 2
(let v5 (LoadResult 5 2 (I32)))
(set (load-addr 5) v1)

(run 10)
(extract v5)
"#;
        let full = format!("{}\n{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY, program);
        let mut egraph = EGraph::default();
        let results = egraph
            .parse_and_run_program(None, &full)
            .expect("egglog should run");
        let mut extracted = results.iter().filter_map(extract_output_to_string);
        let result = extracted.next().expect("extract should return a result");
        // v5 should be unified with (Const 10 (I32)) via pass-through
        assert!(result.contains("0xa"), "Expected 0xa, got: {result}");
        assert!(extracted.next().is_none());
    }

    #[test]
    fn test_load_pass_through_multiple_non_aliasing_stores_egglog() {
        // mem1: store A=10
        // mem2: store B=20
        // mem3: store C=30
        // load A from mem3 should walk through mem2 and mem3 and still return 10.
        let program = r#"
(let a (AllocaResult 1 (I32)))
(let b (AllocaResult 2 (I32)))
(let c (AllocaResult 3 (I32)))

(set (store-prev 1) 0)
(set (store-addr 1) a)
(set (store-val 1) (Const (i256 10) (I32)))
(set (store-ty 1) (I32))

(set (store-prev 2) 1)
(set (store-addr 2) b)
(set (store-val 2) (Const (i256 20) (I32)))
(set (store-ty 2) (I32))

(set (store-prev 3) 2)
(set (store-addr 3) c)
(set (store-val 3) (Const (i256 30) (I32)))
(set (store-ty 3) (I32))

(let v4 (LoadResult 4 3 (I32)))
(set (load-addr 4) a)

(run 10)
(extract v4)
"#;
        let full = format!("{}\n{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY, program);
        let mut egraph = EGraph::default();
        let results = egraph
            .parse_and_run_program(None, &full)
            .expect("egglog should run");
        let mut extracted = results.iter().filter_map(extract_output_to_string);
        let result = extracted.next().expect("extract should return a result");
        assert!(result.contains("0xa"), "Expected 0xa, got: {result}");
        assert!(extracted.next().is_none());
    }

    #[test]
    fn test_memphi_load_merge_after_non_aliasing_tail_stores_egglog() {
        // Branch 1: store A=10; store B=99
        // Branch 2: store A=10; store C=77
        // Merge memory with MemPhi and load A -> 10.
        let program = r#"
(let a (AllocaResult 1 (I32)))
(let b (AllocaResult 2 (I32)))
(let c (AllocaResult 3 (I32)))

(set (store-prev 1) 0)
(set (store-addr 1) a)
(set (store-val 1) (Const (i256 10) (I32)))
(set (store-ty 1) (I32))

(set (store-prev 2) 1)
(set (store-addr 2) b)
(set (store-val 2) (Const (i256 99) (I32)))
(set (store-ty 2) (I32))

(set (store-prev 3) 0)
(set (store-addr 3) a)
(set (store-val 3) (Const (i256 10) (I32)))
(set (store-ty 3) (I32))

(set (store-prev 4) 3)
(set (store-addr 4) c)
(set (store-val 4) (Const (i256 77) (I32)))
(set (store-ty 4) (I32))

(is-memphi 5)
(set (memphi-num-preds 5) 2)
(set (memphi-pred 5 0) 2)
(set (memphi-pred 5 1) 4)

(let v6 (LoadResult 6 5 (I32)))
(set (load-addr 6) a)

(run 10)
(extract v6)
"#;
        let full = format!("{}\n{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY, program);
        let mut egraph = EGraph::default();
        let results = egraph
            .parse_and_run_program(None, &full)
            .expect("egglog should run");
        let mut extracted = results.iter().filter_map(extract_output_to_string);
        let result = extracted.next().expect("extract should return a result");
        assert!(result.contains("0xa"), "Expected 0xa, got: {result}");
        assert!(extracted.next().is_none());
    }

    #[test]
    fn test_no_false_elimination_egglog() {
        // Test that loads from different memory states are NOT incorrectly unified
        // when there's an intervening store to the same address
        // v1 = alloca
        // mem1 = store 10 to v1
        // v4 = load from v1 at mem1 -> 10
        // mem2 = store 20 to v1 (same address!)
        // v6 = load from v1 at mem2 -> should be 20, NOT 10
        let program = r#"
(let v1 (AllocaResult 1 (I32)))
; Store 10 to v1, creating memory state 1
(set (store-prev 1) 0)
(set (store-addr 1) v1)
(set (store-val 1) (Const (i256 10) (I32)))
(set (store-ty 1) (I32))
; Load from v1 at memory state 1 -> should be 10
(let v4 (LoadResult 4 1 (I32)))
(set (load-addr 4) v1)
; Store 20 to v1, creating memory state 2
(set (store-prev 2) 1)
(set (store-addr 2) v1)
(set (store-val 2) (Const (i256 20) (I32)))
(set (store-ty 2) (I32))
; Load from v1 at memory state 2 -> should be 20
(let v6 (LoadResult 6 2 (I32)))
(set (load-addr 6) v1)

(run 10)
(extract v4)
(extract v6)
"#;
        let full = format!("{}\n{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY, program);
        let mut egraph = EGraph::default();
        let results = egraph
            .parse_and_run_program(None, &full)
            .expect("egglog should run");
        let mut extracted = results.iter().filter_map(extract_output_to_string);
        let v4_result = extracted
            .next()
            .expect("first extract should return a result");
        let v6_result = extracted
            .next()
            .expect("second extract should return a result");
        // v4 should be 10
        assert!(
            v4_result.contains("0xa"),
            "v4 should be 0xa, got: {v4_result}"
        );
        // v6 should be 20, NOT 10
        assert!(
            v6_result.contains("0x14"),
            "v6 should be 0x14, got: {v6_result}"
        );
        assert!(extracted.next().is_none());
    }

    #[test]
    fn test_dead_store_detection_egglog() {
        // Test that consecutive stores to the same address marks first as dead
        // v1 = alloca
        // mem1 = store 10 to v1 -> should be marked dead
        // mem2 = store 20 to v1
        let program = r#"
(let v1 (AllocaResult 1 (I32)))
; Store 10 to v1, creating memory state 1
(set (store-prev 1) 0)
(set (store-addr 1) v1)
(set (store-val 1) (Const (i256 10) (I32)))
(set (store-ty 1) (I32))
; Store 20 to v1, creating memory state 2 (overwrites mem1)
(set (store-prev 2) 1)
(set (store-addr 2) v1)
(set (store-val 2) (Const (i256 20) (I32)))
(set (store-ty 2) (I32))

(run 10)
(check (dead-store 1))
"#;
        let full = format!("{}\n{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY, program);
        let mut egraph = EGraph::default();
        // If (check ...) fails, parse_and_run_program returns an error
        egraph
            .parse_and_run_program(None, &full)
            .expect("dead-store 1 should be detected");
    }

    #[test]
    fn test_no_dead_store_different_addr_egglog() {
        // Test that stores to different addresses are NOT marked as dead
        // v1, v3 = different allocas
        // mem1 = store 10 to v1 -> should NOT be dead
        // mem2 = store 20 to v3 -> different address
        let program = r#"
(let v1 (AllocaResult 1 (I32)))
(let v3 (AllocaResult 3 (I32)))
; Store 10 to v1, creating memory state 1
(set (store-prev 1) 0)
(set (store-addr 1) v1)
(set (store-val 1) (Const (i256 10) (I32)))
(set (store-ty 1) (I32))
; Store 20 to v3, creating memory state 2 (different address)
(set (store-prev 2) 1)
(set (store-addr 2) v3)
(set (store-val 2) (Const (i256 20) (I32)))
(set (store-ty 2) (I32))

(run 10)
(fail (check (dead-store 1)))
"#;
        let full = format!("{}\n{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY, program);
        let mut egraph = EGraph::default();
        // (fail (check ...)) succeeds if the check fails
        egraph
            .parse_and_run_program(None, &full)
            .expect("dead-store 1 should NOT be detected for different addresses");
    }

    #[test]
    fn test_adjacent_dead_store_elimination_ir() {
        use sonatina_ir::{
            builder::test_util::*,
            inst::{control_flow::Return, data::Alloca},
            isa::Isa,
        };

        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        builder.switch_to_block(b0);

        let ptr_ty = builder.ptr_type(Type::I32);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I32), ptr_ty);

        let v10 = builder.make_imm_value(10i32);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v10, Type::I32));

        let v20 = builder.make_imm_value(20i32);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v20, Type::I32));

        builder.insert_inst_no_result_with(|| Return::new(is, None));
        builder.seal_all();

        assert!(eliminate_adjacent_dead_stores(&mut builder.func));

        let is = builder.func.inst_set();
        let store_count = builder
            .func
            .layout
            .iter_block()
            .flat_map(|block| builder.func.layout.iter_inst(block))
            .filter(|&inst_id| <&Mstore>::downcast(is, builder.func.dfg.inst(inst_id)).is_some())
            .count();
        assert_eq!(store_count, 1);
    }

    #[test]
    fn test_adjacent_dead_store_elimination_preserves_mixed_width() {
        use sonatina_ir::{
            builder::test_util::*,
            inst::{control_flow::Return, data::Alloca},
            isa::Isa,
        };

        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let b0 = builder.append_block();
        builder.switch_to_block(b0);

        let ptr_ty = builder.ptr_type(Type::I64);
        let addr = builder.insert_inst_with(|| Alloca::new(is, Type::I64), ptr_ty);

        let v64 = builder.make_imm_value(10i64);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v64, Type::I64));

        let v8 = builder.make_imm_value(20i8);
        builder.insert_inst_no_result_with(|| Mstore::new(is, addr, v8, Type::I8));

        builder.insert_inst_no_result_with(|| Return::new(is, None));
        builder.seal_all();

        assert!(!eliminate_adjacent_dead_stores(&mut builder.func));

        let is = builder.func.inst_set();
        let store_count = builder
            .func
            .layout
            .iter_block()
            .flat_map(|block| builder.func.layout.iter_inst(block))
            .filter(|&inst_id| <&Mstore>::downcast(is, builder.func.dfg.inst(inst_id)).is_some())
            .count();
        assert_eq!(store_count, 2);
    }

    #[test]
    fn run_egraph_pass_skips_when_call_attrs_unknown() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-london"

declare external %ext();

func private %f() {
    block0:
        call %ext;
        return;
}
"#,
        )
        .expect("parse should succeed");

        let func_ref = parsed.module.funcs()[0];
        parsed.module.func_store.modify(func_ref, |func| {
            assert!(!run_egraph_pass(func));
        });
    }
}
