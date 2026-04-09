//! E-graph optimization pass for sonatina IR.

use crate::domtree::DomTree;

use egglog::{CommandOutput, EGraph};
use rustc_hash::FxHashMap;

use sonatina_ir::{ControlFlowGraph, Function, InstId, Type, Value, ValueId};

use super::{EggTerm, Elaborator, func_to_egglog};

const TYPES: &str = include_str!("types.egg");
const EXPRS: &str = include_str!("expr.egg");
const RULES: &str = include_str!("rules.egg");

fn has_unknown_call_attrs(func: &Function) -> bool {
    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            if let Some(call) = func.dfg.call_info(inst_id)
                && !func.ctx().has_func_effects(call.callee())
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

    // Build value map
    let mut value_map: FxHashMap<String, ValueId> = FxHashMap::default();
    let mut type_map: FxHashMap<String, Type> = FxHashMap::default();

    for &arg_val in &func.arg_values {
        let name = format!("v{}", arg_val.as_u32());
        value_map.insert(name.clone(), arg_val);
        type_map.insert(name, func.dfg.value_ty(arg_val));
    }

    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            for &result in func.dfg.inst_results(inst_id) {
                let name = format!("v{}", result.as_u32());
                value_map.insert(name.clone(), result);
                type_map.insert(name, func.dfg.value_ty(result));
            }
        }
    }

    let mut cfg = ControlFlowGraph::new();
    cfg.compute(func);
    let mut dom = DomTree::new();
    dom.compute(&cfg);

    // Convert to egglog
    let program = func_to_egglog(func);
    let load_mem_map = collect_load_mem_ids(&program);

    // Build extraction queries for all instruction result values
    let mut full_program = program.clone();
    let mut extract_names = Vec::new();

    // Run rules to apply rewrites
    full_program.push_str("\n(run 4)");

    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            for &result in func.dfg.inst_results(inst_id) {
                let name = format!("v{}", result.as_u32());
                full_program.push_str(&format!("\n(extract {})", name));
                extract_names.push(name);
            }
        }
    }

    // Run egglog
    let mut egraph = EGraph::default();
    let full_with_rules = format!("{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, full_program);

    let results = match egraph.parse_and_run_program(None, &full_with_rules) {
        Ok(r) => r,
        Err(err) => {
            if std::env::var_os("SONATINA_EGRAPH_DEBUG").is_some() {
                eprintln!("{err}");
            }
            return false;
        }
    };

    // Check results for simplifications
    let mut changed = false;
    let mut term_value_candidates: FxHashMap<EggTerm, Vec<ValueId>> = FxHashMap::default();

    let mut extract_results = results.iter().filter_map(extract_output_to_string);

    for name in &extract_names {
        let Some(result) = extract_results.next() else {
            break;
        };
        let result = result.trim();
        let original_val = value_map[name];
        let ty = type_map[name];

        let Some(term) = EggTerm::parse(result, func, &load_mem_map).map(EggTerm::canonicalize)
        else {
            continue;
        };

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
            EggTerm::Value(alias_val) | EggTerm::LoadResult(alias_val, _) => {
                if can_alias(func, &dom, original_val, alias_val) {
                    func.dfg.change_to_alias(original_val, alias_val);
                    changed = true;
                }
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

    if eliminate_dead_pure_insts(func) {
        changed = true;
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

fn extract_output_to_string(output: &CommandOutput) -> Option<String> {
    match output {
        CommandOutput::ExtractBest(termdag, _cost, term) => Some(termdag.to_string(*term)),
        CommandOutput::ExtractVariants(termdag, terms) => {
            terms.first().copied().map(|term| termdag.to_string(term))
        }
        _ => None,
    }
}

fn collect_load_mem_ids(program: &str) -> FxHashMap<u32, u32> {
    let mut load_mem_ids = FxHashMap::default();

    for line in program.lines() {
        let Some((_, rest)) = line.split_once("(LoadResult ") else {
            continue;
        };

        let mut fields = rest.split_whitespace();
        let (Some(load_id), Some(mem_id)) = (fields.next(), fields.next()) else {
            continue;
        };

        let (Ok(load_id), Ok(mem_id)) = (load_id.parse::<u32>(), mem_id.parse::<u32>()) else {
            continue;
        };
        load_mem_ids.insert(load_id, mem_id);
    }

    load_mem_ids
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
        func.layout.remove_inst(inst);
        func.erase_inst(inst);
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
    if !func.dfg.can_drop_if_unused(inst) {
        return false;
    }

    func.dfg
        .inst_results(inst)
        .iter()
        .all(|&result| func.dfg.users_num(result) == 0)
}

#[cfg(test)]
mod tests {
    use sonatina_ir::{
        ir_writer::FuncWriter,
        module::{FuncAttrs, FuncRef},
    };
    use sonatina_parser::parse_module;

    use super::*;

    fn find_func_ref(parsed: &sonatina_parser::ParsedModule, name: &str) -> FuncRef {
        parsed
            .module
            .funcs()
            .into_iter()
            .find(|&func_ref| {
                parsed
                    .module
                    .ctx
                    .func_sig(func_ref, |sig| sig.name() == name)
            })
            .unwrap_or_else(|| panic!("function `{name}` should exist"))
    }

    #[test]
    fn test_egglog_parses() {
        let full = format!("{}\n{}\n{}", TYPES, EXPRS, RULES);
        let mut egraph = EGraph::default();
        egraph
            .parse_and_run_program(None, &full)
            .expect("egglog should parse successfully");
    }

    #[test]
    fn run_egraph_pass_does_not_own_memory_forwarding() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-london"

func private %f(v0.*i256) -> i256 {
    block0:
        mstore v0 7.i256 i256;
        v1.i256 = mload v0 i256;
        return v1;
}
"#,
        )
        .expect("parse should succeed");

        let func_ref = find_func_ref(&parsed, "f");
        parsed.module.func_store.modify(func_ref, |func| {
            assert!(
                !run_egraph_pass(func),
                "load/store forwarding should be owned by the LoadStore pass"
            );
        });
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

        let func_ref = find_func_ref(&parsed, "f");
        parsed.module.func_store.modify(func_ref, |func| {
            assert!(has_unknown_call_attrs(func));

            #[cfg(debug_assertions)]
            {
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    run_egraph_pass(func)
                }));
                assert!(result.is_err());
            }

            #[cfg(not(debug_assertions))]
            assert!(!run_egraph_pass(func));
        });
    }

    #[test]
    fn run_egraph_pass_allows_known_empty_call_attrs() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-london"

declare private %pure();

func private %f() {
    block0:
        call %pure;
        return;
}
"#,
        )
        .expect("parse should succeed");

        let pure = find_func_ref(&parsed, "pure");
        let caller = find_func_ref(&parsed, "f");
        parsed
            .module
            .ctx
            .set_legacy_func_attrs(pure, FuncAttrs::empty());

        parsed.module.func_store.view(caller, |func| {
            assert!(!has_unknown_call_attrs(func));
        });
    }

    #[test]
    fn egg_term_parse_rejects_mismatched_load_mem_states() {
        let load_mem_ids: FxHashMap<u32, u32> = [(21, 4), (32, 6), (36, 6)].into_iter().collect();
        let parsed = parse_module(
            r#"
target = "evm-ethereum-london"

func private %f(v0.i256) -> i256 {
    block0:
        return v0;
}
"#,
        )
        .expect("parse should succeed");

        let func_ref = parsed.module.funcs()[0];
        parsed.module.func_store.view(func_ref, |func| {
            assert!(EggTerm::parse("(LoadResult 21 4 (I256))", func, &load_mem_ids).is_some());
            assert!(EggTerm::parse(
                "(EvmMulMod (LoadResult 32 6 (I256)) (LoadResult 36 6 (I256)) (Const (i256 1) (I256)))",
                func,
                &load_mem_ids
            )
            .is_some());
            assert!(EggTerm::parse("(LoadResult 21 7 (I256))", func, &load_mem_ids).is_none());
            assert!(EggTerm::parse(
                "(EvmAddMod (LoadResult 21 4 (I256)) (LoadResult 36 99 (I256)) (Const (i256 1) (I256)))",
                func,
                &load_mem_ids
            )
            .is_none());
        });
    }

    #[test]
    fn egraph_does_not_alias_load_results_across_memory_states() {
        let parsed = parse_module(
            r#"
target = "evm-ethereum-london"

func private %entry(v0.i256) -> i256 {
    block0:
        v1.*i256 = int_to_ptr v0 *i256;
        v2.i256 = ptr_to_int v1 i256;
        v3.i256 = mload v2 i256;
        v4.i256 = add v3 1.i256;
        mstore v2 v4 i256;
        return v4;
}
"#,
        )
        .expect("parse should succeed");

        let func_ref = parsed.module.funcs()[0];
        parsed.module.func_store.modify(func_ref, |func| {
            assert!(run_egraph_pass(func), "expected egraph to change function");
            let dumped = FuncWriter::new(func_ref, func).dump_string();
            assert!(
                dumped.contains(" = add "),
                "cross-memory load aliasing must not eliminate add:\n{dumped}"
            );
            assert!(
                dumped.contains("return v4;"),
                "return value must remain the post-store expression:\n{dumped}"
            );
        });
    }
}
