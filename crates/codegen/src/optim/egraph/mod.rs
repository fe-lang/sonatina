mod elaborate;
mod pass;

pub use elaborate::{EggTerm, Elaborator};
pub use pass::run_egraph_pass;

use std::fmt::Write;

use egglog::EGraph;
use sonatina_ir::{
    inst::{arith::*, cmp::*, control_flow::Phi, data::*, evm::*, logic::*},
    Function, InstDowncast, InstId, Type, Value, ValueId,
};

const TYPES: &str = include_str!("types.egg");
const EXPRS: &str = include_str!("expr.egg");
const RULES: &str = include_str!("rules.egg");
const MEMORY: &str = include_str!("memory.egg");

/// Run egglog optimization on the given program.
pub fn run_egglog(program: &str) -> egglog::EGraph {
    let full_program = format!("{}\n{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, MEMORY, program);
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, &full_program).unwrap();
    egraph
}

pub fn func_to_egglog(func: &Function) -> String {
    let mut out = String::new();
    let mut mem_state_counter = 0;

    // Memory state 0 = initial memory (no explicit definition needed)
    let mut current_mem = "mem0".to_string();

    // Define function arguments
    for (idx, &arg_val) in func.arg_values.iter().enumerate() {
        let ty = func.dfg.value_ty(arg_val);
        writeln!(
            &mut out,
            "(let {} (Arg {} {}))",
            value_name(arg_val),
            idx,
            type_to_egglog(ty)
        )
        .unwrap();
    }

    for block in func.layout.iter_block() {
        writeln!(&mut out, "; block{}", block.as_u32()).unwrap();
        for inst_id in func.layout.iter_inst(block) {
            if let Some((s, new_mem)) = inst_to_egglog_with_mem(func, inst_id, &current_mem, &mut mem_state_counter) {
                writeln!(&mut out, "{}", s).unwrap();
                if let Some(m) = new_mem {
                    current_mem = m;
                }
            }
        }
    }
    out
}

fn inst_to_egglog(func: &Function, inst_id: InstId) -> Option<String> {
    let inst = func.dfg.inst(inst_id);
    let is = func.inst_set();
    let result = func.dfg.inst_result(inst_id);

    macro_rules! try_binary {
        ($inst_ty:ty, $op:literal) => {
            if let Some(i) = <&$inst_ty>::downcast(is, inst) {
                let result = result?;
                return Some(format!(
                    "(let {} ({} {} {}))",
                    value_name(result),
                    $op,
                    value_to_egglog(func, *i.lhs()),
                    value_to_egglog(func, *i.rhs())
                ));
            }
        };
    }

    macro_rules! try_unary {
        ($inst_ty:ty, $op:literal) => {
            if let Some(i) = <&$inst_ty>::downcast(is, inst) {
                let result = result?;
                return Some(format!(
                    "(let {} ({} {}))",
                    value_name(result),
                    $op,
                    value_to_egglog(func, *i.arg())
                ));
            }
        };
    }

    // Arithmetic
    try_binary!(Add, "Add");
    try_binary!(Sub, "Sub");
    try_binary!(Mul, "Mul");
    try_binary!(Udiv, "Udiv");
    try_binary!(Sdiv, "Sdiv");
    try_binary!(Umod, "Umod");
    try_binary!(Smod, "Smod");
    try_unary!(Neg, "Neg");

    // EVM-specific arithmetic (map to generic egraph nodes)
    try_binary!(EvmUdiv, "Udiv");
    try_binary!(EvmSdiv, "Sdiv");
    try_binary!(EvmUmod, "Umod");
    try_binary!(EvmSmod, "Smod");

    // Shifts have different field names (bits, value)
    if let Some(i) = <&Shl>::downcast(is, inst) {
        let result = result?;
        return Some(format!(
            "(let {} (Shl {} {}))",
            value_name(result),
            value_to_egglog(func, *i.bits()),
            value_to_egglog(func, *i.value())
        ));
    }
    if let Some(i) = <&Shr>::downcast(is, inst) {
        let result = result?;
        return Some(format!(
            "(let {} (Shr {} {}))",
            value_name(result),
            value_to_egglog(func, *i.bits()),
            value_to_egglog(func, *i.value())
        ));
    }
    if let Some(i) = <&Sar>::downcast(is, inst) {
        let result = result?;
        return Some(format!(
            "(let {} (Sar {} {}))",
            value_name(result),
            value_to_egglog(func, *i.bits()),
            value_to_egglog(func, *i.value())
        ));
    }

    // Logic
    try_binary!(And, "And");
    try_binary!(Or, "Or");
    try_binary!(Xor, "Xor");
    try_unary!(Not, "Not");

    // Comparisons
    try_binary!(Lt, "Lt");
    try_binary!(Gt, "Gt");
    try_binary!(Le, "Le");
    try_binary!(Ge, "Ge");
    try_binary!(Slt, "Slt");
    try_binary!(Sgt, "Sgt");
    try_binary!(Sle, "Sle");
    try_binary!(Sge, "Sge");
    try_binary!(Eq, "Eq");
    try_binary!(Ne, "Ne");

    if let Some(i) = <&IsZero>::downcast(is, inst) {
        let result = result?;
        return Some(format!(
            "(let {} (IsZero {}))",
            value_name(result),
            value_to_egglog(func, *i.lhs())
        ));
    }

    // Phi instructions produce opaque values in the egraph
    // The phi result can be used by other expressions, but the phi itself is not optimized
    if <&Phi>::downcast(is, inst).is_some() {
        let result = result?;
        let ty = func.dfg.value_ty(result);
        return Some(format!(
            "(let {} (SideEffectResult {} {}))",
            value_name(result),
            result.as_u32(),
            type_to_egglog(ty)
        ));
    }

    // Alloca - creates a unique stack allocation
    if <&Alloca>::downcast(is, inst).is_some() {
        let result = result?;
        let ty = func.dfg.value_ty(result);
        return Some(format!(
            "(let {} (AllocaResult {} {}))",
            value_name(result),
            result.as_u32(),
            type_to_egglog(ty)
        ));
    }

    // Gep - get element pointer (address computation)
    if let Some(gep) = <&Gep>::downcast(is, inst) {
        let result = result?;
        let values = gep.values();
        if values.is_empty() {
            return None;
        }

        // Build nested GEP expression: GepBase -> GepOffset -> GepOffset -> ...
        let mut gep_expr = format!("(GepBase {})", value_to_egglog(func, values[0]));
        for (i, &idx) in values[1..].iter().enumerate() {
            gep_expr = format!(
                "(GepOffset {} {} {})",
                gep_expr,
                value_to_egglog(func, idx),
                i
            );
        }

        return Some(format!("(let {} {})", value_name(result), gep_expr));
    }

    None
}

/// Convert instruction to egglog with memory state tracking.
/// Returns (egglog_string, new_memory_state_name) if instruction can be converted.
fn inst_to_egglog_with_mem(
    func: &Function,
    inst_id: InstId,
    current_mem: &str,
    mem_counter: &mut u32,
) -> Option<(String, Option<String>)> {
    let inst = func.dfg.inst(inst_id);
    let is = func.inst_set();
    let result = func.dfg.inst_result(inst_id);

    // Mload - load from memory, creates a LoadResult with unique ID
    // Also sets the load-addr function for this load
    if let Some(load) = <&Mload>::downcast(is, inst) {
        let result = result?;
        let ty = func.dfg.value_ty(result);
        let addr = value_to_egglog(func, *load.addr());
        let load_id = result.as_u32();
        // Parse current_mem to get mem_id (e.g., "mem0" -> 0, "mem1" -> 1)
        let mem_id: u32 = current_mem
            .strip_prefix("mem")
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        let egglog = format!(
            "(let {} (LoadResult {} {} {}))\n(set (load-addr {}) {})",
            value_name(result),
            load_id,
            mem_id,
            type_to_egglog(ty),
            load_id,
            addr
        );
        return Some((egglog, None));
    }

    // Mstore - store to memory, creates new memory state
    // Sets store-prev, store-addr, store-val, store-ty functions
    if let Some(store) = <&Mstore>::downcast(is, inst) {
        *mem_counter += 1;
        let new_mem_id = *mem_counter;
        let new_mem = format!("mem{}", new_mem_id);
        let addr = value_to_egglog(func, *store.addr());
        let value = value_to_egglog(func, *store.value());
        let ty = func.dfg.value_ty(*store.value());
        // Parse current_mem to get prev_mem_id
        let prev_mem_id: u32 = current_mem
            .strip_prefix("mem")
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        let egglog = format!(
            "(set (store-prev {}) {})\n(set (store-addr {}) {})\n(set (store-val {}) {})\n(set (store-ty {}) {})",
            new_mem_id, prev_mem_id,
            new_mem_id, addr,
            new_mem_id, value,
            new_mem_id, type_to_egglog(ty)
        );
        return Some((egglog, Some(new_mem)));
    }

    // Fall back to non-memory instruction conversion
    inst_to_egglog(func, inst_id).map(|s| (s, None))
}

fn value_name(v: ValueId) -> String {
    format!("v{}", v.as_u32())
}

fn value_to_egglog(func: &Function, v: ValueId) -> String {
    match func.dfg.value(v) {
        Value::Immediate { imm, ty } => {
            format!(
                "(Const {} {})",
                imm.as_i256().trunc_to_i64(),
                type_to_egglog(*ty)
            )
        }
        _ => value_name(v),
    }
}

fn type_to_egglog(ty: Type) -> &'static str {
    match ty {
        Type::I1 => "(I1)",
        Type::I8 => "(I8)",
        Type::I16 => "(I16)",
        Type::I32 => "(I32)",
        Type::I64 => "(I64)",
        Type::I128 => "(I128)",
        Type::I256 => "(I256)",
        Type::Unit => "(UnitTy)",
        Type::Compound(_) => "(CompoundRef 0)",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        assert_eq!(type_to_egglog(Type::I32), "(I32)");
    }
}
