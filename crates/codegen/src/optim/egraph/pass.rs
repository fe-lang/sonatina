//! E-graph optimization pass for sonatina IR.

use crate::domtree::DomTree;

use egglog::EGraph;
use rustc_hash::FxHashMap;

use sonatina_ir::{Function, InstDowncast, InstId, Type, ValueId, inst::data::Mstore};
use sonatina_ir::{
    ControlFlowGraph, Function, I256, InstDowncast, InstId, Type, U256, Value, ValueId,
    inst::data::Mstore,
};

use super::{EggTerm, Elaborator, func_to_egglog};

const TYPES: &str = include_str!("types.egg");
const EXPRS: &str = include_str!("expr.egg");
const RULES: &str = include_str!("rules.egg");
const MEMORY: &str = include_str!("memory.egg");

/// Run e-graph optimization pass on a function.
/// Returns true if the function was modified.
pub fn run_egraph_pass(func: &mut Function) -> bool {
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
            if let Some(result) = func.dfg.inst_result(inst_id) {
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

    // Build extraction queries for all instruction result values
    let mut full_program = program.clone();
    let mut extract_names = Vec::new();

    // Run rules to apply rewrites
    full_program.push_str("\n(run 10)");

    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            if let Some(result) = func.dfg.inst_result(inst_id) {
                let name = format!("v{}", result.as_u32());
                full_program.push_str(&format!("\n(extract {})", name));
                extract_names.push(name);
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

    // Check results for simplifications
    let mut changed = false;

    for (idx, name) in extract_names.iter().enumerate() {
        if idx >= results.len() {
            break;
        }

        let result = &results[idx];
        let original_val = value_map[name];
        let ty = type_map[name];

        // Check if result is a constant like "(Const 0 (I32))"
        if let Some(const_val) = parse_const_result(result) {
            let imm_id = func
                .dfg
                .make_imm_value(sonatina_ir::Immediate::from_i256(const_val.into(), ty));
            if imm_id != original_val {
                func.dfg.change_to_alias(original_val, imm_id);
                changed = true;
            }
        }
        // Check if result is just another variable like "v0"
        else if let Some(alias_name) = parse_var_result(result) {
            if let Some(&alias_val) = value_map.get(&alias_name)
                && can_alias(func, &dom, original_val, alias_val)
            {
                func.dfg.change_to_alias(original_val, alias_val);
                changed = true;
            }
        }
        // Check if result is a function argument like "(Arg 0 (I32))"
        else if let Some(arg_idx) = parse_arg_result(result) {
            if arg_idx < func.arg_values.len() {
                let arg_val = func.arg_values[arg_idx];
                if can_alias(func, &dom, original_val, arg_val) {
                    func.dfg.change_to_alias(original_val, arg_val);
                    changed = true;
                }
            }
        }
        // Check if result is a side-effect result like "(SideEffectResult N (Type))"
        else if let Some(side_effect_id) = parse_side_effect_result(result) {
            let alias_name = format!("v{side_effect_id}");
            if let Some(&side_effect_val) = value_map.get(&alias_name)
                && can_alias(func, &dom, original_val, side_effect_val)
            {
                func.dfg.change_to_alias(original_val, side_effect_val);
                changed = true;
            }
        }
        // Check if result is an alloca result like "(AllocaResult N (Type))"
        else if let Some(alloca_id) = parse_alloca_result(result) {
            let alias_name = format!("v{alloca_id}");
            if let Some(&alloca_val) = value_map.get(&alias_name)
                && can_alias(func, &dom, original_val, alloca_val)
            {
                func.dfg.change_to_alias(original_val, alloca_val);
                changed = true;
            }
        }
        // Otherwise, try to elaborate the extracted expression back into IR.
        else if let Some(term) = EggTerm::parse(result, func) {
            let is = func.inst_set();
            if term.node_count() > 32 || !term.is_supported(is) || term.contains_value(original_val)
            {
                continue;
            }

            let Some(original_inst) = func.dfg.value_inst(original_val) else {
                continue;
            };
            if func.dfg.is_phi(original_inst) {
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
                changed = true;
            }
        }
    }

    if eliminate_adjacent_dead_stores(func) {
        changed = true;
    }

    changed
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
        let mut prev_store: Option<(sonatina_ir::InstId, ValueId)> = None;

        for inst_id in insts {
            let inst = func.dfg.inst(inst_id);
            if let Some(store) = <&Mstore>::downcast(is, inst) {
                let addr = *store.addr();
                if let Some((prev_id, prev_addr)) = prev_store
                    && prev_addr == addr
                {
                    func.layout.remove_inst(prev_id);
                    changed = true;
                }

                prev_store = Some((inst_id, addr));
            } else {
                prev_store = None;
            }
        }
    }

    changed
}

fn parse_const_result(s: &str) -> Option<i64> {
    // Parse "(Const N (TY))" format
    let s = s.trim();
    if !s.starts_with("(Const ") {
        return None;
    }

    let inner = s.strip_prefix("(Const ")?.strip_suffix(')')?;
    let parts: Vec<_> = inner.splitn(2, ' ').collect();
    if parts.is_empty() {
        return None;
    }

    parts[0].parse().ok()
}

fn parse_var_result(s: &str) -> Option<String> {
    // Parse "vN" format or "(Arg N (Type))" format
    let s = s.trim();
    if s.starts_with('v') && s[1..].chars().all(|c| c.is_ascii_digit()) {
        Some(s.to_string())
    } else if s.starts_with("(Arg ") {
        // Parse "(Arg N (Type))" format - return "vN" where N is the arg index
        // Note: This is a simplification - in reality we'd need to map arg index to value
        None
    } else {
        None
    }
}

fn parse_arg_result(s: &str) -> Option<usize> {
    // Parse "(Arg N (Type))" format, return the argument index
    let s = s.trim();
    if !s.starts_with("(Arg ") {
        return None;
    }
    let inner = s.strip_prefix("(Arg ")?.strip_suffix(')')?;
    let parts: Vec<_> = inner.splitn(2, ' ').collect();
    if parts.is_empty() {
        return None;
    }
    parts[0].parse().ok()
}

fn parse_side_effect_result(s: &str) -> Option<usize> {
    // Parse "(SideEffectResult N (Type))" format, return the value ID
    let s = s.trim();
    if !s.starts_with("(SideEffectResult ") {
        return None;
    }
    let inner = s.strip_prefix("(SideEffectResult ")?.strip_suffix(')')?;
    let parts: Vec<_> = inner.splitn(2, ' ').collect();
    if parts.is_empty() {
        return None;
    }
    parts[0].parse().ok()
}

fn parse_alloca_result(s: &str) -> Option<usize> {
    // Parse "(AllocaResult N (Type))" format, return the value ID
    let s = s.trim();
    if !s.starts_with("(AllocaResult ") {
        return None;
    }
    let inner = s.strip_prefix("(AllocaResult ")?.strip_suffix(')')?;
    let parts: Vec<_> = inner.splitn(2, ' ').collect();
    if parts.is_empty() {
        return None;
    }
    parts[0].parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_const() {
        assert_eq!(parse_const_result("(Const 0 (I32))"), Some(0));
        assert_eq!(parse_const_result("(Const 42 (I64))"), Some(42));
        assert_eq!(parse_const_result("v0"), None);
    }

    #[test]
    fn test_parse_var() {
        assert_eq!(parse_var_result("v0"), Some("v0".to_string()));
        assert_eq!(parse_var_result("v123"), Some("v123".to_string()));
        assert_eq!(parse_var_result("(Const 0 (I32))"), None);
    }

    #[test]
    fn test_parse_arg() {
        assert_eq!(parse_arg_result("(Arg 0 (I32))"), Some(0));
        assert_eq!(parse_arg_result("(Arg 2 (I64))"), Some(2));
        assert_eq!(parse_arg_result("v0"), None);
        assert_eq!(parse_arg_result("(Const 0 (I32))"), None);
    }

    #[test]
    fn test_parse_side_effect() {
        assert_eq!(
            parse_side_effect_result("(SideEffectResult 3 (I32))"),
            Some(3)
        );
        assert_eq!(
            parse_side_effect_result("(SideEffectResult 42 (I64))"),
            Some(42)
        );
        assert_eq!(parse_side_effect_result("v0"), None);
        assert_eq!(parse_side_effect_result("(Const 0 (I32))"), None);
    }

    #[test]
    fn test_parse_alloca() {
        assert_eq!(parse_alloca_result("(AllocaResult 1 (I32))"), Some(1));
        assert_eq!(parse_alloca_result("(AllocaResult 99 (I64))"), Some(99));
        assert_eq!(parse_alloca_result("v0"), None);
        assert_eq!(parse_alloca_result("(Const 0 (I32))"), None);
    }

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
(set (store-val 1) (Const 42 (I32)))
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
        assert_eq!(results.len(), 1);
        let result = &results[0];
        eprintln!("Result: {}", result);
        assert!(result.contains("Const 42") || result == "(Const 42 (I32))");
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
(set (store-val 1) (Const 10 (I32)))
(set (store-ty 1) (I32))
; Store 20 to v3, creating memory state 2
(set (store-prev 2) 1)
(set (store-addr 2) v3)
(set (store-val 2) (Const 20 (I32)))
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
        assert_eq!(results.len(), 1);
        let result = &results[0];
        eprintln!("Load pass-through result: {}", result);
        // v5 should be unified with (Const 10 (I32)) via pass-through
        assert!(
            result.contains("Const 10") || result == "(Const 10 (I32))",
            "Expected Const 10, got: {}",
            result
        );
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
(set (store-val 1) (Const 10 (I32)))
(set (store-ty 1) (I32))
; Load from v1 at memory state 1 -> should be 10
(let v4 (LoadResult 4 1 (I32)))
(set (load-addr 4) v1)
; Store 20 to v1, creating memory state 2
(set (store-prev 2) 1)
(set (store-addr 2) v1)
(set (store-val 2) (Const 20 (I32)))
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
        assert_eq!(results.len(), 2);
        let v4_result = &results[0];
        let v6_result = &results[1];
        eprintln!("v4 result: {}", v4_result);
        eprintln!("v6 result: {}", v6_result);
        // v4 should be 10
        assert!(
            v4_result.contains("Const 10"),
            "v4 should be 10, got: {}",
            v4_result
        );
        // v6 should be 20, NOT 10
        assert!(
            v6_result.contains("Const 20"),
            "v6 should be 20, got: {}",
            v6_result
        );
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
(set (store-val 1) (Const 10 (I32)))
(set (store-ty 1) (I32))
; Store 20 to v1, creating memory state 2 (overwrites mem1)
(set (store-prev 2) 1)
(set (store-addr 2) v1)
(set (store-val 2) (Const 20 (I32)))
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
(set (store-val 1) (Const 10 (I32)))
(set (store-ty 1) (I32))
; Store 20 to v3, creating memory state 2 (different address)
(set (store-prev 2) 1)
(set (store-addr 2) v3)
(set (store-val 2) (Const 20 (I32)))
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
}
