mod elaborate;
mod pass;

pub use elaborate::{EggTerm, Elaborator};
pub use pass::run_egraph_pass;

use std::fmt::Write;

use egglog::EGraph;
use sonatina_ir::{
    inst::{arith::*, cmp::*, control_flow::Phi, evm::*, logic::*},
    Function, InstDowncast, InstId, Type, Value, ValueId,
};

const TYPES: &str = include_str!("types.egg");
const EXPRS: &str = include_str!("expr.egg");
const RULES: &str = include_str!("rules.egg");

/// Run egglog optimization on the given program.
pub fn run_egglog(program: &str) -> egglog::EGraph {
    let full_program = format!("{}\n{}\n{}\n{}", TYPES, EXPRS, RULES, program);
    let mut egraph = EGraph::default();
    egraph.parse_and_run_program(None, &full_program).unwrap();
    egraph
}

pub fn func_to_egglog(func: &Function) -> String {
    let mut out = String::new();

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
            if let Some(s) = inst_to_egglog(func, inst_id) {
                writeln!(&mut out, "{}", s).unwrap();
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

    None
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
