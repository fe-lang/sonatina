//! Elaboration: Convert extracted egglog terms back to sonatina IR.

use rustc_hash::FxHashMap;

use sonatina_ir::{
    Function, I256, Inst, InstId, InstSetBase, Type, U256, Value, ValueId,
    inst::{arith::*, cmp::*, evm::*, logic::*},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EggTerm {
    Value(ValueId),
    Const(I256, Type),
    // Binary ops
    Add(Box<EggTerm>, Box<EggTerm>),
    Sub(Box<EggTerm>, Box<EggTerm>),
    Mul(Box<EggTerm>, Box<EggTerm>),
    Udiv(Box<EggTerm>, Box<EggTerm>),
    Sdiv(Box<EggTerm>, Box<EggTerm>),
    Umod(Box<EggTerm>, Box<EggTerm>),
    Smod(Box<EggTerm>, Box<EggTerm>),
    // Shifts
    Shl(Box<EggTerm>, Box<EggTerm>),
    Shr(Box<EggTerm>, Box<EggTerm>),
    Sar(Box<EggTerm>, Box<EggTerm>),
    // Unary
    Neg(Box<EggTerm>),
    Not(Box<EggTerm>),
    // Logic
    And(Box<EggTerm>, Box<EggTerm>),
    Or(Box<EggTerm>, Box<EggTerm>),
    Xor(Box<EggTerm>, Box<EggTerm>),
    // Comparisons
    Lt(Box<EggTerm>, Box<EggTerm>),
    Gt(Box<EggTerm>, Box<EggTerm>),
    Le(Box<EggTerm>, Box<EggTerm>),
    Ge(Box<EggTerm>, Box<EggTerm>),
    Slt(Box<EggTerm>, Box<EggTerm>),
    Sgt(Box<EggTerm>, Box<EggTerm>),
    Sle(Box<EggTerm>, Box<EggTerm>),
    Sge(Box<EggTerm>, Box<EggTerm>),
    Eq(Box<EggTerm>, Box<EggTerm>),
    Ne(Box<EggTerm>, Box<EggTerm>),
    IsZero(Box<EggTerm>),
}

impl EggTerm {
    pub fn parse(s: &str, func: &Function) -> Option<Self> {
        let tokens = tokenize(s)?;
        let mut pos = 0;
        let sexp = parse_sexp(&tokens, &mut pos)?;
        if pos != tokens.len() {
            return None;
        }

        EggTerm::from_sexp(func, &sexp)
    }

    pub fn node_count(&self) -> usize {
        match self {
            EggTerm::Value(_) | EggTerm::Const(..) => 1,
            EggTerm::Neg(x) | EggTerm::Not(x) | EggTerm::IsZero(x) => 1 + x.node_count(),
            EggTerm::Add(a, b)
            | EggTerm::Sub(a, b)
            | EggTerm::Mul(a, b)
            | EggTerm::Udiv(a, b)
            | EggTerm::Sdiv(a, b)
            | EggTerm::Umod(a, b)
            | EggTerm::Smod(a, b)
            | EggTerm::Shl(a, b)
            | EggTerm::Shr(a, b)
            | EggTerm::Sar(a, b)
            | EggTerm::And(a, b)
            | EggTerm::Or(a, b)
            | EggTerm::Xor(a, b)
            | EggTerm::Lt(a, b)
            | EggTerm::Gt(a, b)
            | EggTerm::Le(a, b)
            | EggTerm::Ge(a, b)
            | EggTerm::Slt(a, b)
            | EggTerm::Sgt(a, b)
            | EggTerm::Sle(a, b)
            | EggTerm::Sge(a, b)
            | EggTerm::Eq(a, b)
            | EggTerm::Ne(a, b) => 1 + a.node_count() + b.node_count(),
        }
    }

    pub fn contains_value(&self, value: ValueId) -> bool {
        let mut found = false;
        self.for_each_value(&mut |v| found |= v == value);
        found
    }

    pub fn for_each_value(&self, f: &mut impl FnMut(ValueId)) {
        match self {
            EggTerm::Value(value) => f(*value),
            EggTerm::Const(..) => {}
            EggTerm::Neg(x) | EggTerm::Not(x) | EggTerm::IsZero(x) => x.for_each_value(f),
            EggTerm::Add(a, b)
            | EggTerm::Sub(a, b)
            | EggTerm::Mul(a, b)
            | EggTerm::Udiv(a, b)
            | EggTerm::Sdiv(a, b)
            | EggTerm::Umod(a, b)
            | EggTerm::Smod(a, b)
            | EggTerm::Shl(a, b)
            | EggTerm::Shr(a, b)
            | EggTerm::Sar(a, b)
            | EggTerm::And(a, b)
            | EggTerm::Or(a, b)
            | EggTerm::Xor(a, b)
            | EggTerm::Lt(a, b)
            | EggTerm::Gt(a, b)
            | EggTerm::Le(a, b)
            | EggTerm::Ge(a, b)
            | EggTerm::Slt(a, b)
            | EggTerm::Sgt(a, b)
            | EggTerm::Sle(a, b)
            | EggTerm::Sge(a, b)
            | EggTerm::Eq(a, b)
            | EggTerm::Ne(a, b) => {
                a.for_each_value(f);
                b.for_each_value(f);
            }
        }
    }

    pub fn is_supported(&self, is: &dyn InstSetBase) -> bool {
        match self {
            EggTerm::Value(_) | EggTerm::Const(..) => true,

            EggTerm::Neg(x) => is.has_neg().is_some() && x.is_supported(is),
            EggTerm::Not(x) => is.has_not().is_some() && x.is_supported(is),

            EggTerm::Add(a, b) => {
                is.has_add().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::Sub(a, b) => {
                is.has_sub().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::Mul(a, b) => {
                is.has_mul().is_some() && a.is_supported(is) && b.is_supported(is)
            }

            EggTerm::Udiv(a, b) => {
                (is.has_evm_udiv().is_some() || is.has_udiv().is_some())
                    && a.is_supported(is)
                    && b.is_supported(is)
            }
            EggTerm::Sdiv(a, b) => {
                (is.has_evm_sdiv().is_some() || is.has_sdiv().is_some())
                    && a.is_supported(is)
                    && b.is_supported(is)
            }
            EggTerm::Umod(a, b) => {
                (is.has_evm_umod().is_some() || is.has_umod().is_some())
                    && a.is_supported(is)
                    && b.is_supported(is)
            }
            EggTerm::Smod(a, b) => {
                (is.has_evm_smod().is_some() || is.has_smod().is_some())
                    && a.is_supported(is)
                    && b.is_supported(is)
            }

            EggTerm::Shl(a, b) => {
                is.has_shl().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::Shr(a, b) => {
                is.has_shr().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::Sar(a, b) => {
                is.has_sar().is_some() && a.is_supported(is) && b.is_supported(is)
            }

            EggTerm::And(a, b) => {
                is.has_and().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::Or(a, b) => is.has_or().is_some() && a.is_supported(is) && b.is_supported(is),
            EggTerm::Xor(a, b) => {
                is.has_xor().is_some() && a.is_supported(is) && b.is_supported(is)
            }

            EggTerm::Lt(a, b) => is.has_lt().is_some() && a.is_supported(is) && b.is_supported(is),
            EggTerm::Gt(a, b) => is.has_gt().is_some() && a.is_supported(is) && b.is_supported(is),
            EggTerm::Le(a, b) => is.has_le().is_some() && a.is_supported(is) && b.is_supported(is),
            EggTerm::Ge(a, b) => is.has_ge().is_some() && a.is_supported(is) && b.is_supported(is),
            EggTerm::Slt(a, b) => {
                is.has_slt().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::Sgt(a, b) => {
                is.has_sgt().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::Sle(a, b) => {
                is.has_sle().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::Sge(a, b) => {
                is.has_sge().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::Eq(a, b) => is.has_eq().is_some() && a.is_supported(is) && b.is_supported(is),
            EggTerm::Ne(a, b) => is.has_ne().is_some() && a.is_supported(is) && b.is_supported(is),
            EggTerm::IsZero(x) => is.has_is_zero().is_some() && x.is_supported(is),
        }
    }

    fn from_sexp(func: &Function, sexp: &Sexp) -> Option<Self> {
        match sexp {
            Sexp::Atom(atom) => parse_value_atom(atom).map(EggTerm::Value),
            Sexp::Str(_) => None,
            Sexp::List(list) => {
                let (head, rest) = list.split_first()?;
                let Sexp::Atom(head) = head else {
                    return None;
                };

                match head.as_str() {
                    "Const" => {
                        let [value, ty] = rest else { return None };
                        let value = match value {
                            Sexp::Str(s) | Sexp::Atom(s) => s.as_str(),
                            _ => return None,
                        };
                        let ty = parse_type(ty)?;
                        let value = parse_i256_decimal(value)?;
                        Some(EggTerm::Const(value, ty))
                    }
                    "Arg" => {
                        let [idx, _ty] = rest else { return None };
                        let idx: usize = parse_usize(idx)?;
                        Some(EggTerm::Value(*func.arg_values.get(idx)?))
                    }
                    "AllocaResult" | "SideEffectResult" => {
                        let [id, _ty] = rest else { return None };
                        let id = parse_u32(id)?;
                        Some(EggTerm::Value(ValueId::from_u32(id)))
                    }
                    "LoadResult" => {
                        let [id, _mem, _ty] = rest else { return None };
                        let id = parse_u32(id)?;
                        Some(EggTerm::Value(ValueId::from_u32(id)))
                    }

                    "Neg" => parse_unary(func, rest, EggTerm::Neg),
                    "Not" => parse_unary(func, rest, EggTerm::Not),
                    "IsZero" => parse_unary(func, rest, EggTerm::IsZero),

                    "Add" => parse_binary(func, rest, EggTerm::Add),
                    "Sub" => parse_binary(func, rest, EggTerm::Sub),
                    "Mul" => parse_binary(func, rest, EggTerm::Mul),
                    "Udiv" => parse_binary(func, rest, EggTerm::Udiv),
                    "Sdiv" => parse_binary(func, rest, EggTerm::Sdiv),
                    "Umod" => parse_binary(func, rest, EggTerm::Umod),
                    "Smod" => parse_binary(func, rest, EggTerm::Smod),
                    "Shl" => parse_binary(func, rest, EggTerm::Shl),
                    "Shr" => parse_binary(func, rest, EggTerm::Shr),
                    "Sar" => parse_binary(func, rest, EggTerm::Sar),

                    "And" => parse_binary(func, rest, EggTerm::And),
                    "Or" => parse_binary(func, rest, EggTerm::Or),
                    "Xor" => parse_binary(func, rest, EggTerm::Xor),

                    "Lt" => parse_binary(func, rest, EggTerm::Lt),
                    "Gt" => parse_binary(func, rest, EggTerm::Gt),
                    "Le" => parse_binary(func, rest, EggTerm::Le),
                    "Ge" => parse_binary(func, rest, EggTerm::Ge),
                    "Slt" => parse_binary(func, rest, EggTerm::Slt),
                    "Sgt" => parse_binary(func, rest, EggTerm::Sgt),
                    "Sle" => parse_binary(func, rest, EggTerm::Sle),
                    "Sge" => parse_binary(func, rest, EggTerm::Sge),
                    "Eq" => parse_binary(func, rest, EggTerm::Eq),
                    "Ne" => parse_binary(func, rest, EggTerm::Ne),

                    _ => None,
                }
            }
        }
    }
}

fn parse_unary(
    func: &Function,
    args: &[Sexp],
    ctor: fn(Box<EggTerm>) -> EggTerm,
) -> Option<EggTerm> {
    let [arg] = args else { return None };
    Some(ctor(Box::new(EggTerm::from_sexp(func, arg)?)))
}

fn parse_binary(
    func: &Function,
    args: &[Sexp],
    ctor: fn(Box<EggTerm>, Box<EggTerm>) -> EggTerm,
) -> Option<EggTerm> {
    let [lhs, rhs] = args else { return None };
    Some(ctor(
        Box::new(EggTerm::from_sexp(func, lhs)?),
        Box::new(EggTerm::from_sexp(func, rhs)?),
    ))
}

fn parse_value_atom(atom: &str) -> Option<ValueId> {
    let rest = atom.strip_prefix('v')?;
    let id: u32 = rest.parse().ok()?;
    Some(ValueId::from_u32(id))
}

fn parse_u32(sexp: &Sexp) -> Option<u32> {
    let Sexp::Atom(atom) = sexp else { return None };
    atom.parse().ok()
}

fn parse_usize(sexp: &Sexp) -> Option<usize> {
    let Sexp::Atom(atom) = sexp else { return None };
    atom.parse().ok()
}

fn parse_type(sexp: &Sexp) -> Option<Type> {
    let Sexp::List(list) = sexp else { return None };
    let [Sexp::Atom(head)] = list.as_slice() else {
        return None;
    };

    match head.as_str() {
        "I1" => Some(Type::I1),
        "I8" => Some(Type::I8),
        "I16" => Some(Type::I16),
        "I32" => Some(Type::I32),
        "I64" => Some(Type::I64),
        "I128" => Some(Type::I128),
        "I256" => Some(Type::I256),
        "UnitTy" => Some(Type::Unit),
        _ => None,
    }
}

fn parse_i256_decimal(token: &str) -> Option<I256> {
    let abs = token.strip_prefix('-');
    let is_negative = abs.is_some();
    let abs = abs.unwrap_or(token);

    let mut i256: I256 = U256::from_dec_str(abs).ok()?.into();
    if is_negative {
        i256 = I256::zero().overflowing_sub(i256).0;
    }

    Some(i256)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    LParen,
    RParen,
    Atom(String),
    Str(String),
}

#[derive(Debug)]
enum Sexp {
    Atom(String),
    Str(String),
    List(Vec<Sexp>),
}

fn tokenize(input: &str) -> Option<Vec<Token>> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();

    let mut idx = 0;
    while idx < bytes.len() {
        match bytes[idx] {
            b'(' => {
                tokens.push(Token::LParen);
                idx += 1;
            }
            b')' => {
                tokens.push(Token::RParen);
                idx += 1;
            }
            b'"' => {
                idx += 1;
                let start = idx;
                while idx < bytes.len() && bytes[idx] != b'"' {
                    idx += 1;
                }
                if idx >= bytes.len() {
                    return None;
                }

                tokens.push(Token::Str(input[start..idx].to_string()));
                idx += 1;
            }
            b if b.is_ascii_whitespace() => idx += 1,
            _ => {
                let start = idx;
                while idx < bytes.len()
                    && !bytes[idx].is_ascii_whitespace()
                    && bytes[idx] != b'('
                    && bytes[idx] != b')'
                {
                    idx += 1;
                }

                tokens.push(Token::Atom(input[start..idx].to_string()));
            }
        }
    }

    Some(tokens)
}

fn parse_sexp(tokens: &[Token], pos: &mut usize) -> Option<Sexp> {
    let token = tokens.get(*pos)?;
    match token {
        Token::LParen => {
            *pos += 1;
            let mut list = Vec::new();
            while *pos < tokens.len() && tokens[*pos] != Token::RParen {
                list.push(parse_sexp(tokens, pos)?);
            }
            if *pos >= tokens.len() {
                return None;
            }
            *pos += 1;
            Some(Sexp::List(list))
        }
        Token::RParen => None,
        Token::Atom(atom) => {
            *pos += 1;
            Some(Sexp::Atom(atom.clone()))
        }
        Token::Str(s) => {
            *pos += 1;
            Some(Sexp::Str(s.clone()))
        }
    }
}

pub struct Elaborator<'a> {
    func: &'a mut Function,
    insert_before: InstId,
    memo: FxHashMap<EggTerm, ValueId>,
}

impl<'a> Elaborator<'a> {
    pub fn new(func: &'a mut Function, insert_before: InstId) -> Self {
        Self {
            func,
            insert_before,
            memo: FxHashMap::default(),
        }
    }

    pub fn elaborate_value(&mut self, term: &EggTerm) -> Option<ValueId> {
        if let Some(&value) = self.memo.get(term) {
            return Some(value);
        }

        let value = match term {
            EggTerm::Value(value) => *value,
            EggTerm::Const(val, ty) => self
                .func
                .dfg
                .make_imm_value(sonatina_ir::Immediate::from_i256(*val, *ty)),
            EggTerm::Add(lhs, rhs) => self.binary::<Add>(lhs, rhs),
            EggTerm::Sub(lhs, rhs) => self.binary::<Sub>(lhs, rhs),
            EggTerm::Mul(lhs, rhs) => self.binary::<Mul>(lhs, rhs),
            EggTerm::Udiv(lhs, rhs) => self.div_mod(lhs, rhs, DivMod::Udiv)?,
            EggTerm::Sdiv(lhs, rhs) => self.div_mod(lhs, rhs, DivMod::Sdiv)?,
            EggTerm::Umod(lhs, rhs) => self.div_mod(lhs, rhs, DivMod::Umod)?,
            EggTerm::Smod(lhs, rhs) => self.div_mod(lhs, rhs, DivMod::Smod)?,
            EggTerm::Shl(bits, value) => self.binary::<Shl>(bits, value),
            EggTerm::Shr(bits, value) => self.binary::<Shr>(bits, value),
            EggTerm::Sar(bits, value) => self.binary::<Sar>(bits, value),
            EggTerm::Neg(arg) => self.unary::<Neg>(arg),
            EggTerm::Not(arg) => self.unary::<Not>(arg),
            EggTerm::And(lhs, rhs) => self.binary::<And>(lhs, rhs),
            EggTerm::Or(lhs, rhs) => self.binary::<Or>(lhs, rhs),
            EggTerm::Xor(lhs, rhs) => self.binary::<Xor>(lhs, rhs),
            EggTerm::Lt(lhs, rhs) => self.cmp::<Lt>(lhs, rhs),
            EggTerm::Gt(lhs, rhs) => self.cmp::<Gt>(lhs, rhs),
            EggTerm::Le(lhs, rhs) => self.cmp::<Le>(lhs, rhs),
            EggTerm::Ge(lhs, rhs) => self.cmp::<Ge>(lhs, rhs),
            EggTerm::Slt(lhs, rhs) => self.cmp::<Slt>(lhs, rhs),
            EggTerm::Sgt(lhs, rhs) => self.cmp::<Sgt>(lhs, rhs),
            EggTerm::Sle(lhs, rhs) => self.cmp::<Sle>(lhs, rhs),
            EggTerm::Sge(lhs, rhs) => self.cmp::<Sge>(lhs, rhs),
            EggTerm::Eq(lhs, rhs) => self.cmp::<Eq>(lhs, rhs),
            EggTerm::Ne(lhs, rhs) => self.cmp::<Ne>(lhs, rhs),
            EggTerm::IsZero(arg) => self.is_zero(arg)?,
        };

        self.memo.insert(term.clone(), value);
        Some(value)
    }

    pub fn build_inst(&mut self, term: &EggTerm) -> Option<Box<dyn Inst>> {
        let is = self.func.inst_set();

        Some(match term {
            EggTerm::Add(lhs, rhs) => {
                Box::new(Add::new(is.has_add()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Sub(lhs, rhs) => {
                Box::new(Sub::new(is.has_sub()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Mul(lhs, rhs) => {
                Box::new(Mul::new(is.has_mul()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Udiv(lhs, rhs) => self.div_mod_inst(lhs, rhs, DivMod::Udiv)?,
            EggTerm::Sdiv(lhs, rhs) => self.div_mod_inst(lhs, rhs, DivMod::Sdiv)?,
            EggTerm::Umod(lhs, rhs) => self.div_mod_inst(lhs, rhs, DivMod::Umod)?,
            EggTerm::Smod(lhs, rhs) => self.div_mod_inst(lhs, rhs, DivMod::Smod)?,
            EggTerm::Shl(bits, value) => {
                Box::new(Shl::new(is.has_shl()?, self.val(bits)?, self.val(value)?))
            }
            EggTerm::Shr(bits, value) => {
                Box::new(Shr::new(is.has_shr()?, self.val(bits)?, self.val(value)?))
            }
            EggTerm::Sar(bits, value) => {
                Box::new(Sar::new(is.has_sar()?, self.val(bits)?, self.val(value)?))
            }
            EggTerm::Neg(arg) => Box::new(Neg::new(is.has_neg()?, self.val(arg)?)),
            EggTerm::Not(arg) => Box::new(Not::new(is.has_not()?, self.val(arg)?)),
            EggTerm::And(lhs, rhs) => {
                Box::new(And::new(is.has_and()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Or(lhs, rhs) => {
                Box::new(Or::new(is.has_or()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Xor(lhs, rhs) => {
                Box::new(Xor::new(is.has_xor()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Lt(lhs, rhs) => {
                Box::new(Lt::new(is.has_lt()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Gt(lhs, rhs) => {
                Box::new(Gt::new(is.has_gt()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Le(lhs, rhs) => {
                Box::new(Le::new(is.has_le()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Ge(lhs, rhs) => {
                Box::new(Ge::new(is.has_ge()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Slt(lhs, rhs) => {
                Box::new(Slt::new(is.has_slt()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Sgt(lhs, rhs) => {
                Box::new(Sgt::new(is.has_sgt()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Sle(lhs, rhs) => {
                Box::new(Sle::new(is.has_sle()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Sge(lhs, rhs) => {
                Box::new(Sge::new(is.has_sge()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Eq(lhs, rhs) => {
                Box::new(Eq::new(is.has_eq()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::Ne(lhs, rhs) => {
                Box::new(Ne::new(is.has_ne()?, self.val(lhs)?, self.val(rhs)?))
            }
            EggTerm::IsZero(arg) => Box::new(IsZero::new(is.has_is_zero()?, self.val(arg)?)),
            EggTerm::Value(_) | EggTerm::Const(..) => return None,
        })
    }

    fn val(&mut self, term: &EggTerm) -> Option<ValueId> {
        self.elaborate_value(term)
    }

    fn binary<I>(&mut self, lhs: &EggTerm, rhs: &EggTerm) -> ValueId
    where
        I: BinaryInst,
    {
        let lhs_val = self
            .elaborate_value(lhs)
            .expect("typechecked by EggTerm::is_supported");
        let rhs_val = self
            .elaborate_value(rhs)
            .expect("typechecked by EggTerm::is_supported");
        let ty = self.func.dfg.value_ty(lhs_val);
        let inst = I::new(self.func.inst_set(), lhs_val, rhs_val);
        self.make_inst_value(inst, ty)
    }

    fn unary<I>(&mut self, arg: &EggTerm) -> ValueId
    where
        I: UnaryInst,
    {
        let arg_val = self
            .elaborate_value(arg)
            .expect("typechecked by EggTerm::is_supported");
        let ty = self.func.dfg.value_ty(arg_val);
        let inst = I::new(self.func.inst_set(), arg_val);
        self.make_inst_value(inst, ty)
    }

    fn cmp<I>(&mut self, lhs: &EggTerm, rhs: &EggTerm) -> ValueId
    where
        I: BinaryInst,
    {
        let lhs_val = self
            .elaborate_value(lhs)
            .expect("typechecked by EggTerm::is_supported");
        let rhs_val = self
            .elaborate_value(rhs)
            .expect("typechecked by EggTerm::is_supported");
        let inst = I::new(self.func.inst_set(), lhs_val, rhs_val);
        self.make_inst_value(inst, Type::I1)
    }

    fn is_zero(&mut self, arg: &EggTerm) -> Option<ValueId> {
        let arg_val = self.elaborate_value(arg)?;
        let inst = IsZero::new(self.func.inst_set().has_is_zero()?, arg_val);
        Some(self.make_inst_value(inst, Type::I1))
    }

    fn make_inst_value<I: sonatina_ir::Inst>(&mut self, inst: I, ty: Type) -> ValueId {
        self.make_inst_value_dyn(Box::new(inst), ty)
    }

    fn make_inst_value_dyn(&mut self, inst: Box<dyn Inst>, ty: Type) -> ValueId {
        let inst_id = self.func.dfg.make_inst_dyn(inst);
        let value = Value::Inst { inst: inst_id, ty };
        let value_id = self.func.dfg.make_value(value);
        self.func.dfg.attach_result(inst_id, value_id);
        self.func
            .layout
            .insert_inst_before(inst_id, self.insert_before);
        value_id
    }

    fn div_mod(&mut self, lhs: &EggTerm, rhs: &EggTerm, op: DivMod) -> Option<ValueId> {
        let lhs_val = self.elaborate_value(lhs)?;
        let ty = self.func.dfg.value_ty(lhs_val);

        let inst = self.div_mod_inst(lhs, rhs, op)?;
        Some(self.make_inst_value_dyn(inst, ty))
    }

    fn div_mod_inst(&mut self, lhs: &EggTerm, rhs: &EggTerm, op: DivMod) -> Option<Box<dyn Inst>> {
        let lhs_val = self.elaborate_value(lhs)?;
        let rhs_val = self.elaborate_value(rhs)?;

        let is = self.func.inst_set();
        let inst: Box<dyn Inst> = match op {
            DivMod::Udiv => {
                if let Some(has) = is.has_evm_udiv() {
                    Box::new(EvmUdiv::new(has, lhs_val, rhs_val))
                } else {
                    Box::new(Udiv::new(is.has_udiv()?, lhs_val, rhs_val))
                }
            }
            DivMod::Sdiv => {
                if let Some(has) = is.has_evm_sdiv() {
                    Box::new(EvmSdiv::new(has, lhs_val, rhs_val))
                } else {
                    Box::new(Sdiv::new(is.has_sdiv()?, lhs_val, rhs_val))
                }
            }
            DivMod::Umod => {
                if let Some(has) = is.has_evm_umod() {
                    Box::new(EvmUmod::new(has, lhs_val, rhs_val))
                } else {
                    Box::new(Umod::new(is.has_umod()?, lhs_val, rhs_val))
                }
            }
            DivMod::Smod => {
                if let Some(has) = is.has_evm_smod() {
                    Box::new(EvmSmod::new(has, lhs_val, rhs_val))
                } else {
                    Box::new(Smod::new(is.has_smod()?, lhs_val, rhs_val))
                }
            }
        };

        Some(inst)
    }
}

#[derive(Clone, Copy)]
enum DivMod {
    Udiv,
    Sdiv,
    Umod,
    Smod,
}

trait BinaryInst: sonatina_ir::Inst + Sized {
    fn new(is: &dyn InstSetBase, lhs: ValueId, rhs: ValueId) -> Self;
}

trait UnaryInst: sonatina_ir::Inst + Sized {
    fn new(is: &dyn InstSetBase, arg: ValueId) -> Self;
}

macro_rules! impl_binary {
    ($ty:ty, $has:ident) => {
        impl BinaryInst for $ty {
            fn new(is: &dyn InstSetBase, lhs: ValueId, rhs: ValueId) -> Self {
                <$ty>::new(is.$has().unwrap(), lhs, rhs)
            }
        }
    };
}

macro_rules! impl_unary {
    ($ty:ty, $has:ident) => {
        impl UnaryInst for $ty {
            fn new(is: &dyn InstSetBase, arg: ValueId) -> Self {
                <$ty>::new(is.$has().unwrap(), arg)
            }
        }
    };
}

impl_binary!(Add, has_add);
impl_binary!(Sub, has_sub);
impl_binary!(Mul, has_mul);
impl_binary!(Shl, has_shl);
impl_binary!(Shr, has_shr);
impl_binary!(Sar, has_sar);
impl_binary!(And, has_and);
impl_binary!(Or, has_or);
impl_binary!(Xor, has_xor);
impl_binary!(Lt, has_lt);
impl_binary!(Gt, has_gt);
impl_binary!(Le, has_le);
impl_binary!(Ge, has_ge);
impl_binary!(Slt, has_slt);
impl_binary!(Sgt, has_sgt);
impl_binary!(Sle, has_sle);
impl_binary!(Sge, has_sge);
impl_binary!(Eq, has_eq);
impl_binary!(Ne, has_ne);

impl_unary!(Neg, has_neg);
impl_unary!(Not, has_not);
