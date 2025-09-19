use egglog::{ast::Literal, Term, TermDag};
use sonatina_ir::{Type, ValueId};

pub fn type_to_term(dag: &mut TermDag, ty: Type) -> Term {
    let variant = match ty {
        Type::I1 => "I1",
        Type::I8 => "I8",
        Type::I16 => "I16",
        Type::I32 => "I32",
        Type::I64 => "I64",
        Type::I128 => "I128",
        Type::I256 => "I256",
        Type::Unit => "Unit",
        Type::Compound(cmpd) => {
            let id = dag.lit(Literal::Int(cmpd.as_u32() as i64));
            return dag.app("CompoundRef".into(), vec![id]);
        }
    };
    dag.app(variant.into(), vec![])
}

pub fn value_to_term(dag: &mut TermDag, value: ValueId) -> Term {
    dag.var(format!("v{}", value.as_u32()).into())
}

pub fn binary_op(dag: &mut TermDag, op: &str, lhs: ValueId, rhs: ValueId) -> Term {
    let l = value_to_term(dag, lhs);
    let r = value_to_term(dag, rhs);
    dag.app(op.into(), vec![l, r])
}

pub fn unary_op(dag: &mut TermDag, op: &str, arg: ValueId) -> Term {
    let a = value_to_term(dag, arg);
    dag.app(op.into(), vec![a])
}

pub fn cast_op(dag: &mut TermDag, op: &str, from: ValueId, ty: Type) -> Term {
    let f = value_to_term(dag, from);
    let t = type_to_term(dag, ty);
    dag.app(op.into(), vec![f, t])
}