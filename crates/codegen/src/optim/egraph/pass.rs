//! E-graph optimization pass for sonatina IR.

use egglog::EGraph;
use rustc_hash::FxHashMap;

use sonatina_ir::{Function, Type, ValueId};

use super::func_to_egglog;

const TYPES: &str = include_str!("types.egg");
const EXPRS: &str = include_str!("expr.egg");
const RULES: &str = include_str!("rules.egg");

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
    let full_with_rules = format!("{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, full_program);

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
            if let Some(&alias_val) = value_map.get(&alias_name) {
                if alias_val != original_val {
                    func.dfg.change_to_alias(original_val, alias_val);
                    changed = true;
                }
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
}
