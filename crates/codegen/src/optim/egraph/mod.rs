use std::fmt::Write;

use sonatina_ir::{
    inst::{arith::*, cmp::*, logic::*},
    Function, InstDowncast, InstId, Type, ValueId,
};

pub fn func_to_egglog(func: &Function) -> String {
    let mut out = String::new();

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
                    value_name(*i.lhs()),
                    value_name(*i.rhs())
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
                    value_name(*i.arg())
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

    // Shifts have different field names (bits, value)
    if let Some(i) = <&Shl>::downcast(is, inst) {
        let result = result?;
        return Some(format!(
            "(let {} (Shl {} {}))",
            value_name(result),
            value_name(*i.bits()),
            value_name(*i.value())
        ));
    }
    if let Some(i) = <&Shr>::downcast(is, inst) {
        let result = result?;
        return Some(format!(
            "(let {} (Shr {} {}))",
            value_name(result),
            value_name(*i.bits()),
            value_name(*i.value())
        ));
    }
    if let Some(i) = <&Sar>::downcast(is, inst) {
        let result = result?;
        return Some(format!(
            "(let {} (Sar {} {}))",
            value_name(result),
            value_name(*i.bits()),
            value_name(*i.value())
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
            value_name(*i.lhs())
        ));
    }

    None
}

fn value_name(v: ValueId) -> String {
    format!("v{}", v.as_u32())
}

#[allow(dead_code)]
fn type_to_egglog(ty: Type) -> &'static str {
    match ty {
        Type::I1 => "(I1)",
        Type::I8 => "(I8)",
        Type::I16 => "(I16)",
        Type::I32 => "(I32)",
        Type::I64 => "(I64)",
        Type::I128 => "(I128)",
        Type::I256 => "(I256)",
        Type::Unit => "(Unit)",
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