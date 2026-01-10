//! E-graph optimization pass for sonatina IR.

use egglog::EGraph;
use rustc_hash::FxHashMap;

use sonatina_ir::{Function, InstDowncast, InstId, Type, ValueId, inst::data::Mstore};

use super::func_to_egglog;

const TYPES: &str = include_str!("types.egg");
const EXPRS: &str = include_str!("expr.egg");
const RULES: &str = include_str!("rules.egg");
const MEMORY: &str = include_str!("memory.egg");

/// Run e-graph optimization pass on a function.
/// Returns true if the function was modified.
pub fn run_egraph_pass(func: &mut Function) -> bool {
    // Build value map and store map
    let mut value_map: FxHashMap<String, ValueId> = FxHashMap::default();
    let mut type_map: FxHashMap<String, Type> = FxHashMap::default();
    // Map from memory state ID to inst_id for mstore instructions
    let mut store_map: FxHashMap<u32, InstId> = FxHashMap::default();
    let mut mem_counter: u32 = 0;

    for &arg_val in &func.arg_values {
        let name = format!("v{}", arg_val.as_u32());
        value_map.insert(name.clone(), arg_val);
        type_map.insert(name, func.dfg.value_ty(arg_val));
    }

    let is = func.inst_set();
    for block in func.layout.iter_block() {
        for inst_id in func.layout.iter_inst(block) {
            if let Some(result) = func.dfg.inst_result(inst_id) {
                let name = format!("v{}", result.as_u32());
                value_map.insert(name.clone(), result);
                type_map.insert(name, func.dfg.value_ty(result));
            }
            // Track mstore instructions
            let inst = func.dfg.inst(inst_id);
            if <&Mstore>::downcast(is, inst).is_some() {
                mem_counter += 1;
                store_map.insert(mem_counter, inst_id);
            }
        }
    }

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
        Err(_) => return false,
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
                && alias_val != original_val
            {
                func.dfg.change_to_alias(original_val, alias_val);
                changed = true;
            }
        }
        // Check if result is a function argument like "(Arg 0 (I32))"
        else if let Some(arg_idx) = parse_arg_result(result) {
            if arg_idx < func.arg_values.len() {
                let arg_val = func.arg_values[arg_idx];
                if arg_val != original_val {
                    func.dfg.change_to_alias(original_val, arg_val);
                    changed = true;
                }
            }
        }
        // Check if result is a side-effect result like "(SideEffectResult N (Type))"
        else if let Some(side_effect_id) = parse_side_effect_result(result) {
            // Find the value with this ID
            if let Some(&side_effect_val) = value_map
                .values()
                .find(|&&v| v.as_u32() == side_effect_id as u32)
                && side_effect_val != original_val
            {
                func.dfg.change_to_alias(original_val, side_effect_val);
                changed = true;
            }
        }
        // Check if result is an alloca result like "(AllocaResult N (Type))"
        else if let Some(alloca_id) = parse_alloca_result(result) {
            // Find the value with this ID (the alloca instruction result)
            if let Some(&alloca_val) = value_map
                .values()
                .find(|&&v| v.as_u32() == alloca_id as u32)
                && alloca_val != original_val
            {
                func.dfg.change_to_alias(original_val, alloca_val);
                changed = true;
            }
        }
    }

    // Check for dead stores and remove them
    for (&mem_id, &inst_id) in &store_map {
        // Query if this store is dead
        let check_dead = format!(
            "{}\n{}\n{}\n{}\n{}\n(run 10)\n(check (dead-store {}))",
            TYPES, EXPRS, RULES, MEMORY, program, mem_id
        );
        let mut check_egraph = EGraph::default();
        if check_egraph
            .parse_and_run_program(None, &check_dead)
            .is_ok()
        {
            // Store is dead, remove it
            func.layout.remove_inst(inst_id);
            changed = true;
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
}
