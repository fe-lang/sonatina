//! Elaboration: Convert extracted egglog terms back to sonatina IR.

use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use sonatina_ir::{
    Function, GlobalVariableRef, I256, Inst, InstId, InstSetBase, Type, U256, Value, ValueId,
    inst::{arith::*, cast::*, cmp::*, data::Gep, evm::*, logic::*},
    types::{CompoundType, CompoundTypeRef},
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EggTerm {
    Value(ValueId),
    Global(GlobalVariableRef, Type),
    Undef(Type),
    Const(I256, Type),
    Gep {
        base: Box<EggTerm>,
        indices: Vec<EggTerm>,
    },
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
    EvmAddMod(Box<EggTerm>, Box<EggTerm>, Box<EggTerm>),
    EvmMulMod(Box<EggTerm>, Box<EggTerm>, Box<EggTerm>),
    EvmExp(Box<EggTerm>, Box<EggTerm>),
    EvmByte(Box<EggTerm>, Box<EggTerm>),
    EvmClz(Box<EggTerm>),
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
    Sext(Box<EggTerm>, Type),
    Zext(Box<EggTerm>, Type),
    Trunc(Box<EggTerm>, Type),
    Bitcast(Box<EggTerm>, Type),
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
            EggTerm::Value(_) | EggTerm::Global(..) | EggTerm::Undef(..) | EggTerm::Const(..) => 1,
            EggTerm::Neg(x)
            | EggTerm::Not(x)
            | EggTerm::IsZero(x)
            | EggTerm::EvmClz(x)
            | EggTerm::Sext(x, _)
            | EggTerm::Zext(x, _)
            | EggTerm::Trunc(x, _)
            | EggTerm::Bitcast(x, _) => 1 + x.node_count(),
            EggTerm::Gep { base, indices } => {
                1 + base.node_count() + indices.iter().map(EggTerm::node_count).sum::<usize>()
            }
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
            | EggTerm::Ne(a, b)
            | EggTerm::EvmExp(a, b)
            | EggTerm::EvmByte(a, b) => 1 + a.node_count() + b.node_count(),
            EggTerm::EvmAddMod(a, b, c) | EggTerm::EvmMulMod(a, b, c) => {
                1 + a.node_count() + b.node_count() + c.node_count()
            }
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
            EggTerm::Global(..) | EggTerm::Undef(..) | EggTerm::Const(..) => {}
            EggTerm::Neg(x)
            | EggTerm::Not(x)
            | EggTerm::IsZero(x)
            | EggTerm::EvmClz(x)
            | EggTerm::Sext(x, _)
            | EggTerm::Zext(x, _)
            | EggTerm::Trunc(x, _)
            | EggTerm::Bitcast(x, _) => x.for_each_value(f),
            EggTerm::Gep { base, indices } => {
                base.for_each_value(f);
                for index in indices {
                    index.for_each_value(f);
                }
            }
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
            | EggTerm::Ne(a, b)
            | EggTerm::EvmExp(a, b)
            | EggTerm::EvmByte(a, b) => {
                a.for_each_value(f);
                b.for_each_value(f);
            }
            EggTerm::EvmAddMod(a, b, c) | EggTerm::EvmMulMod(a, b, c) => {
                a.for_each_value(f);
                b.for_each_value(f);
                c.for_each_value(f);
            }
        }
    }

    pub fn is_supported(&self, is: &dyn InstSetBase) -> bool {
        match self {
            EggTerm::Value(_) | EggTerm::Global(..) | EggTerm::Undef(..) | EggTerm::Const(..) => {
                true
            }
            EggTerm::Gep { base, indices } => {
                is.has_gep().is_some()
                    && base.is_supported(is)
                    && indices.iter().all(|index| index.is_supported(is))
            }

            EggTerm::Neg(x) => is.has_neg().is_some() && x.is_supported(is),
            EggTerm::Not(x) => is.has_not().is_some() && x.is_supported(is),
            EggTerm::EvmClz(x) => is.has_evm_clz().is_some() && x.is_supported(is),

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
            EggTerm::EvmExp(a, b) => {
                is.has_evm_exp().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::EvmByte(a, b) => {
                is.has_evm_byte().is_some() && a.is_supported(is) && b.is_supported(is)
            }
            EggTerm::EvmAddMod(a, b, c) => {
                is.has_evm_add_mod().is_some()
                    && a.is_supported(is)
                    && b.is_supported(is)
                    && c.is_supported(is)
            }
            EggTerm::EvmMulMod(a, b, c) => {
                is.has_evm_mul_mod().is_some()
                    && a.is_supported(is)
                    && b.is_supported(is)
                    && c.is_supported(is)
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
            EggTerm::Sext(x, _) => is.has_sext().is_some() && x.is_supported(is),
            EggTerm::Zext(x, _) => is.has_zext().is_some() && x.is_supported(is),
            EggTerm::Trunc(x, _) => is.has_trunc().is_some() && x.is_supported(is),
            EggTerm::Bitcast(x, _) => is.has_bitcast().is_some() && x.is_supported(is),
        }
    }

    pub fn canonicalize(self) -> Self {
        self.canonicalize_with_key().0
    }

    fn canonicalize_with_key(self) -> (Self, String) {
        match self {
            EggTerm::Value(value) => (EggTerm::Value(value), format!("v{}", value.as_u32())),
            EggTerm::Global(gv, ty) => {
                (EggTerm::Global(gv, ty), format!("g{}:{ty:?}", gv.as_u32()))
            }
            EggTerm::Undef(ty) => (EggTerm::Undef(ty), format!("undef:{ty:?}")),
            EggTerm::Const(value, ty) => (EggTerm::Const(value, ty), format!("c{value:?}:{ty:?}")),
            EggTerm::Gep { base, indices } => {
                let (base, base_key) = base.canonicalize_with_key();
                let mut canonical_indices = Vec::with_capacity(indices.len());
                let mut index_keys = Vec::with_capacity(indices.len());
                for index in indices {
                    let (index, index_key) = index.canonicalize_with_key();
                    canonical_indices.push(index);
                    index_keys.push(index_key);
                }
                (
                    EggTerm::Gep {
                        base: Box::new(base),
                        indices: canonical_indices,
                    },
                    format!("gep({base_key};{})", index_keys.join(",")),
                )
            }

            EggTerm::Neg(arg) => Self::canonicalize_unary(*arg, EggTerm::Neg, "neg"),
            EggTerm::Not(arg) => Self::canonicalize_unary(*arg, EggTerm::Not, "not"),
            EggTerm::IsZero(arg) => Self::canonicalize_unary(*arg, EggTerm::IsZero, "is_zero"),
            EggTerm::EvmClz(arg) => Self::canonicalize_unary(*arg, EggTerm::EvmClz, "evm_clz"),
            EggTerm::Sext(arg, ty) => {
                Self::canonicalize_unary_with_ty(*arg, ty, EggTerm::Sext, "sext")
            }
            EggTerm::Zext(arg, ty) => {
                Self::canonicalize_unary_with_ty(*arg, ty, EggTerm::Zext, "zext")
            }
            EggTerm::Trunc(arg, ty) => {
                Self::canonicalize_unary_with_ty(*arg, ty, EggTerm::Trunc, "trunc")
            }
            EggTerm::Bitcast(arg, ty) => {
                Self::canonicalize_unary_with_ty(*arg, ty, EggTerm::Bitcast, "bitcast")
            }

            EggTerm::Add(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Add, "add", true)
            }
            EggTerm::Sub(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Sub, "sub", false)
            }
            EggTerm::Mul(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Mul, "mul", true)
            }
            EggTerm::Udiv(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Udiv, "udiv", false)
            }
            EggTerm::Sdiv(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Sdiv, "sdiv", false)
            }
            EggTerm::Umod(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Umod, "umod", false)
            }
            EggTerm::Smod(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Smod, "smod", false)
            }

            EggTerm::Shl(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Shl, "shl", false)
            }
            EggTerm::Shr(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Shr, "shr", false)
            }
            EggTerm::Sar(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Sar, "sar", false)
            }
            EggTerm::EvmExp(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::EvmExp, "evm_exp", false)
            }
            EggTerm::EvmByte(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::EvmByte, "evm_byte", false)
            }
            EggTerm::EvmAddMod(lhs, rhs, modulus) => Self::canonicalize_ternary(
                *lhs,
                *rhs,
                *modulus,
                EggTerm::EvmAddMod,
                "evm_add_mod",
                true,
            ),
            EggTerm::EvmMulMod(lhs, rhs, modulus) => Self::canonicalize_ternary(
                *lhs,
                *rhs,
                *modulus,
                EggTerm::EvmMulMod,
                "evm_mul_mod",
                true,
            ),

            EggTerm::And(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::And, "and", true)
            }
            EggTerm::Or(lhs, rhs) => Self::canonicalize_binary(*lhs, *rhs, EggTerm::Or, "or", true),
            EggTerm::Xor(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Xor, "xor", true)
            }

            EggTerm::Lt(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Lt, "lt", false)
            }
            EggTerm::Gt(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Gt, "gt", false)
            }
            EggTerm::Le(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Le, "le", false)
            }
            EggTerm::Ge(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Ge, "ge", false)
            }
            EggTerm::Slt(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Slt, "slt", false)
            }
            EggTerm::Sgt(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Sgt, "sgt", false)
            }
            EggTerm::Sle(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Sle, "sle", false)
            }
            EggTerm::Sge(lhs, rhs) => {
                Self::canonicalize_binary(*lhs, *rhs, EggTerm::Sge, "sge", false)
            }
            EggTerm::Eq(lhs, rhs) => Self::canonicalize_binary(*lhs, *rhs, EggTerm::Eq, "eq", true),
            EggTerm::Ne(lhs, rhs) => Self::canonicalize_binary(*lhs, *rhs, EggTerm::Ne, "ne", true),
        }
    }

    fn canonicalize_unary(
        arg: EggTerm,
        ctor: fn(Box<EggTerm>) -> EggTerm,
        op_name: &str,
    ) -> (Self, String) {
        let (arg, arg_key) = arg.canonicalize_with_key();
        (ctor(Box::new(arg)), format!("{op_name}({arg_key})"))
    }

    fn canonicalize_binary(
        lhs: EggTerm,
        rhs: EggTerm,
        ctor: fn(Box<EggTerm>, Box<EggTerm>) -> EggTerm,
        op_name: &str,
        commutative: bool,
    ) -> (Self, String) {
        let (mut lhs, mut lhs_key) = lhs.canonicalize_with_key();
        let (mut rhs, mut rhs_key) = rhs.canonicalize_with_key();

        if commutative && lhs_key > rhs_key {
            std::mem::swap(&mut lhs, &mut rhs);
            std::mem::swap(&mut lhs_key, &mut rhs_key);
        }

        (
            ctor(Box::new(lhs), Box::new(rhs)),
            format!("{op_name}({lhs_key},{rhs_key})"),
        )
    }

    fn canonicalize_unary_with_ty(
        arg: EggTerm,
        ty: Type,
        ctor: fn(Box<EggTerm>, Type) -> EggTerm,
        op_name: &str,
    ) -> (Self, String) {
        let (arg, arg_key) = arg.canonicalize_with_key();
        (
            ctor(Box::new(arg), ty),
            format!("{op_name}({arg_key},{ty:?})"),
        )
    }

    fn canonicalize_ternary(
        lhs: EggTerm,
        rhs: EggTerm,
        third: EggTerm,
        ctor: fn(Box<EggTerm>, Box<EggTerm>, Box<EggTerm>) -> EggTerm,
        op_name: &str,
        commutative_prefix: bool,
    ) -> (Self, String) {
        let (mut lhs, mut lhs_key) = lhs.canonicalize_with_key();
        let (mut rhs, mut rhs_key) = rhs.canonicalize_with_key();
        let (third, third_key) = third.canonicalize_with_key();

        if commutative_prefix && lhs_key > rhs_key {
            std::mem::swap(&mut lhs, &mut rhs);
            std::mem::swap(&mut lhs_key, &mut rhs_key);
        }

        (
            ctor(Box::new(lhs), Box::new(rhs), Box::new(third)),
            format!("{op_name}({lhs_key},{rhs_key},{third_key})"),
        )
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
                        let ty = parse_type(ty)?;
                        let value = parse_i256(value)?;
                        Some(EggTerm::Const(value, ty))
                    }
                    "Global" => {
                        let [id, ty] = rest else { return None };
                        let id = parse_u32(id)?;
                        let ty = parse_type(ty)?;
                        Some(EggTerm::Global(GlobalVariableRef::from_u32(id), ty))
                    }
                    "Undef" => {
                        let [ty] = rest else { return None };
                        Some(EggTerm::Undef(parse_type(ty)?))
                    }
                    "Arg" => {
                        let [idx, _ty] = rest else { return None };
                        let idx: usize = parse_usize(idx)?;
                        Some(EggTerm::Value(*func.arg_values.get(idx)?))
                    }
                    "AllocaResult" | "SideEffectResult" | "PhiResult" => {
                        let [id, _ty] = rest else { return None };
                        let id = parse_u32(id)?;
                        Some(EggTerm::Value(ValueId::from_u32(id)))
                    }
                    "LoadResult" => {
                        let [id, _mem, _ty] = rest else { return None };
                        let id = parse_u32(id)?;
                        Some(EggTerm::Value(ValueId::from_u32(id)))
                    }
                    "GepBase" | "GepOffset" => parse_gep(func, sexp),

                    "Neg" => parse_unary(func, rest, EggTerm::Neg),
                    "Not" => parse_unary(func, rest, EggTerm::Not),
                    "IsZero" => parse_unary(func, rest, EggTerm::IsZero),
                    "EvmClz" => parse_unary(func, rest, EggTerm::EvmClz),

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
                    "EvmExp" => parse_binary(func, rest, EggTerm::EvmExp),
                    "EvmByte" => parse_binary(func, rest, EggTerm::EvmByte),
                    "EvmAddMod" => parse_ternary(func, rest, EggTerm::EvmAddMod),
                    "EvmMulMod" => parse_ternary(func, rest, EggTerm::EvmMulMod),

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
                    "Sext" => parse_unary_with_type(func, rest, EggTerm::Sext),
                    "Zext" => parse_unary_with_type(func, rest, EggTerm::Zext),
                    "Trunc" => parse_unary_with_type(func, rest, EggTerm::Trunc),
                    "Bitcast" => parse_unary_with_type(func, rest, EggTerm::Bitcast),

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

fn parse_unary_with_type(
    func: &Function,
    args: &[Sexp],
    ctor: fn(Box<EggTerm>, Type) -> EggTerm,
) -> Option<EggTerm> {
    let [arg, ty] = args else { return None };
    Some(ctor(
        Box::new(EggTerm::from_sexp(func, arg)?),
        parse_type(ty)?,
    ))
}

fn parse_ternary(
    func: &Function,
    args: &[Sexp],
    ctor: fn(Box<EggTerm>, Box<EggTerm>, Box<EggTerm>) -> EggTerm,
) -> Option<EggTerm> {
    let [a, b, c] = args else { return None };
    Some(ctor(
        Box::new(EggTerm::from_sexp(func, a)?),
        Box::new(EggTerm::from_sexp(func, b)?),
        Box::new(EggTerm::from_sexp(func, c)?),
    ))
}

fn parse_gep(func: &Function, sexp: &Sexp) -> Option<EggTerm> {
    let (base, indices) = parse_gep_chain(func, sexp)?;
    Some(EggTerm::Gep {
        base: Box::new(base),
        indices,
    })
}

fn parse_gep_chain(func: &Function, sexp: &Sexp) -> Option<(EggTerm, Vec<EggTerm>)> {
    let Sexp::List(list) = sexp else { return None };
    let (head, rest) = list.split_first()?;
    let Sexp::Atom(head) = head else { return None };

    match head.as_str() {
        "GepBase" => {
            let [base] = rest else { return None };
            Some((EggTerm::from_sexp(func, base)?, Vec::new()))
        }
        "GepOffset" => {
            let [prev, index, _field_idx] = rest else {
                return None;
            };
            let (base, mut indices) = parse_gep_chain(func, prev)?;
            indices.push(EggTerm::from_sexp(func, index)?);
            Some((base, indices))
        }
        _ => None,
    }
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
    let (head, rest) = list.split_first()?;
    let Sexp::Atom(head) = head else { return None };

    match head.as_str() {
        "I1" => Some(Type::I1),
        "I8" => Some(Type::I8),
        "I16" => Some(Type::I16),
        "I32" => Some(Type::I32),
        "I64" => Some(Type::I64),
        "I128" => Some(Type::I128),
        "I256" => Some(Type::I256),
        "UnitTy" => Some(Type::Unit),
        "CompoundRef" => {
            let [id] = rest else { return None };
            Some(Type::Compound(CompoundTypeRef::from_u32(parse_u32(id)?)))
        }
        _ => None,
    }
}

fn parse_i256(sexp: &Sexp) -> Option<I256> {
    match sexp {
        Sexp::Atom(token) | Sexp::Str(token) => parse_i256_string(token),
        Sexp::List(list) => {
            let (head, rest) = list.split_first()?;
            let Sexp::Atom(head) = head else {
                return None;
            };

            match head.as_str() {
                "i256" => {
                    let [n] = rest else { return None };
                    let n: i64 = parse_i64(n)?;
                    Some(n.into())
                }
                "i256-from-string" => {
                    let [s] = rest else { return None };
                    let s = match s {
                        Sexp::Atom(s) | Sexp::Str(s) => s.as_str(),
                        _ => return None,
                    };
                    parse_i256_string(s)
                }
                _ => None,
            }
        }
    }
}

fn parse_i256_string(token: &str) -> Option<I256> {
    let abs = token.trim().strip_prefix('-');
    let is_negative = abs.is_some();
    let abs = abs.unwrap_or(token).trim();

    let mut i256: I256 = parse_u256_string(abs)?.into();
    if is_negative {
        i256 = I256::zero().overflowing_sub(i256).0;
    }

    Some(i256)
}

fn parse_u256_string(token: &str) -> Option<U256> {
    let token = token.replace('_', "");

    if let Some(rest) = token
        .strip_prefix("0x")
        .or_else(|| token.strip_prefix("0X"))
    {
        return parse_u256_hex(rest);
    }
    if let Some(rest) = token
        .strip_prefix("0b")
        .or_else(|| token.strip_prefix("0B"))
    {
        return parse_u256_binary(rest);
    }
    if let Some(rest) = token
        .strip_prefix("0o")
        .or_else(|| token.strip_prefix("0O"))
    {
        return parse_u256_octal(rest);
    }

    U256::from_dec_str(&token).ok()
}

fn parse_u256_hex(hex: &str) -> Option<U256> {
    fn nibble(hex: u8) -> Option<u8> {
        match hex {
            b'0'..=b'9' => Some(hex - b'0'),
            b'a'..=b'f' => Some(hex - b'a' + 10),
            b'A'..=b'F' => Some(hex - b'A' + 10),
            _ => None,
        }
    }

    let mut bytes = [0u8; 32];
    let mut idx = bytes.len();
    let mut low_nibble: Option<u8> = None;

    for &b in hex.as_bytes().iter().rev() {
        let n = nibble(b)?;
        if let Some(low) = low_nibble {
            idx = idx.checked_sub(1)?;
            bytes[idx] = (n << 4) | low;
            low_nibble = None;
        } else {
            low_nibble = Some(n);
        }
    }

    if let Some(low) = low_nibble {
        idx = idx.checked_sub(1)?;
        bytes[idx] = low;
    }

    Some(U256::from_big_endian(&bytes))
}

fn parse_u256_binary(bin: &str) -> Option<U256> {
    let bin = bin.trim();
    if bin.len() > 256 {
        return None;
    }

    let mut value = U256::zero();
    for b in bin.bytes() {
        let bit = match b {
            b'0' => 0u8,
            b'1' => 1u8,
            _ => return None,
        };
        value = (value << 1) | U256::from(bit);
    }
    Some(value)
}

fn parse_u256_octal(oct: &str) -> Option<U256> {
    let mut value = U256::zero();
    for b in oct.trim().bytes() {
        let digit = match b {
            b'0'..=b'7' => b - b'0',
            _ => return None,
        };

        let (mul, overflow_mul) = value.overflowing_mul(U256::from(8u8));
        if overflow_mul {
            return None;
        }

        let (next, overflow_add) = mul.overflowing_add(U256::from(digit));
        if overflow_add {
            return None;
        }

        value = next;
    }
    Some(value)
}

fn parse_i64(sexp: &Sexp) -> Option<i64> {
    let Sexp::Atom(atom) = sexp else { return None };
    atom.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use sonatina_ir::{
        builder::test_util::*,
        inst::{control_flow::Return, data::Alloca},
        isa::Isa,
    };

    fn const_i32(value: i64) -> EggTerm {
        EggTerm::Const(value.into(), Type::I32)
    }

    #[test]
    fn parse_u256_octal_accepts_boundary_power() {
        let input = format!("1{}", "0".repeat(85));
        let parsed = parse_u256_octal(&input).expect("2^255 should fit in u256");
        assert_eq!(parsed, U256::one() << 255);
    }

    #[test]
    fn parse_u256_octal_rejects_overflow() {
        let input = format!("1{}", "0".repeat(86));
        assert!(parse_u256_octal(&input).is_none());
    }

    #[test]
    fn parse_u256_octal_rejects_invalid_digit() {
        assert!(parse_u256_octal("128").is_none());
    }

    #[test]
    fn canonicalize_commutative_binary_reorders_operands() {
        let term = EggTerm::Add(Box::new(const_i32(20)), Box::new(const_i32(10)));
        let canonical = term.canonicalize();
        assert_eq!(
            canonical,
            EggTerm::Add(Box::new(const_i32(10)), Box::new(const_i32(20)))
        );
    }

    #[test]
    fn canonicalize_recurses_into_nested_commutative_terms() {
        let term = EggTerm::Add(
            Box::new(EggTerm::Mul(Box::new(const_i32(3)), Box::new(const_i32(2)))),
            Box::new(EggTerm::Add(Box::new(const_i32(9)), Box::new(const_i32(1)))),
        );
        let canonical = term.canonicalize();
        assert_eq!(
            canonical,
            EggTerm::Add(
                Box::new(EggTerm::Add(Box::new(const_i32(1)), Box::new(const_i32(9)))),
                Box::new(EggTerm::Mul(Box::new(const_i32(2)), Box::new(const_i32(3))))
            )
        );
    }

    #[test]
    fn canonicalize_keeps_non_commutative_order() {
        let term = EggTerm::Sub(Box::new(const_i32(20)), Box::new(const_i32(10)));
        let canonical = term.canonicalize();
        assert_eq!(
            canonical,
            EggTerm::Sub(Box::new(const_i32(20)), Box::new(const_i32(10)))
        );
    }

    #[test]
    fn elaborate_nested_gep_derives_type_from_indices() {
        let mb = test_module_builder();
        let (evm, mut builder) = test_func_builder(&mb, &[], Type::Unit);
        let is = evm.inst_set();

        let block = builder.append_block();
        builder.switch_to_block(block);

        let array_ty = builder.declare_array_type(Type::I32, 4);
        let ptr_array_ty = builder.ptr_type(array_ty);
        let base_ptr = builder.insert_inst_with(|| Alloca::new(is, array_ty), ptr_array_ty);
        builder.insert_inst_no_result_with(|| Return::new(is, None));
        builder.seal_all();

        let insert_before = builder
            .func
            .layout
            .last_inst_of(block)
            .expect("return should be inserted");

        let first_gep = EggTerm::Gep {
            base: Box::new(EggTerm::Value(base_ptr)),
            indices: vec![
                EggTerm::Const(0.into(), Type::I32),
                EggTerm::Const(2.into(), Type::I32),
            ],
        };
        let nested_gep = EggTerm::Gep {
            base: Box::new(first_gep),
            indices: vec![EggTerm::Const(1.into(), Type::I32)],
        };

        let mut elaborator = Elaborator::new(&mut builder.func, insert_before);
        let result = elaborator
            .elaborate_value(&nested_gep)
            .expect("nested gep should elaborate");
        let result_ty = elaborator.func.dfg.value_ty(result);

        assert_eq!(result_ty, Type::I32.to_ptr(&elaborator.func.dfg.ctx));
    }
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
            EggTerm::Global(gv, _ty) => self.func.dfg.make_global_value(*gv),
            EggTerm::Undef(ty) => self.func.dfg.make_undef_value(*ty),
            EggTerm::Const(val, ty) => self
                .func
                .dfg
                .make_imm_value(sonatina_ir::Immediate::from_i256(*val, *ty)),
            EggTerm::Gep { base, indices } => self.gep(base, indices)?,
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
            EggTerm::EvmAddMod(lhs, rhs, modulus) => {
                self.evm_mod(lhs, rhs, modulus, EvmMod::AddMod)?
            }
            EggTerm::EvmMulMod(lhs, rhs, modulus) => {
                self.evm_mod(lhs, rhs, modulus, EvmMod::MulMod)?
            }
            EggTerm::EvmExp(base, exponent) => self.evm_exp(base, exponent)?,
            EggTerm::EvmByte(pos, value) => self.evm_byte(pos, value)?,
            EggTerm::EvmClz(word) => self.unary::<EvmClz>(word),
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
            EggTerm::Sext(arg, ty) => self.cast(arg, *ty, CastOp::Sext)?,
            EggTerm::Zext(arg, ty) => self.cast(arg, *ty, CastOp::Zext)?,
            EggTerm::Trunc(arg, ty) => self.cast(arg, *ty, CastOp::Trunc)?,
            EggTerm::Bitcast(arg, ty) => self.cast(arg, *ty, CastOp::Bitcast)?,
        };

        self.memo.insert(term.clone(), value);
        Some(value)
    }

    pub fn build_inst(&mut self, term: &EggTerm) -> Option<Box<dyn Inst>> {
        let is = self.func.inst_set();

        Some(match term {
            EggTerm::Gep { base, indices } => self.gep_inst(base, indices)?,
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
            EggTerm::EvmAddMod(lhs, rhs, modulus) => Box::new(EvmAddMod::new(
                is.has_evm_add_mod()?,
                self.val(lhs)?,
                self.val(rhs)?,
                self.val(modulus)?,
            )),
            EggTerm::EvmMulMod(lhs, rhs, modulus) => Box::new(EvmMulMod::new(
                is.has_evm_mul_mod()?,
                self.val(lhs)?,
                self.val(rhs)?,
                self.val(modulus)?,
            )),
            EggTerm::EvmExp(base, exponent) => Box::new(EvmExp::new(
                is.has_evm_exp()?,
                self.val(base)?,
                self.val(exponent)?,
            )),
            EggTerm::EvmByte(pos, value) => Box::new(EvmByte::new(
                is.has_evm_byte()?,
                self.val(pos)?,
                self.val(value)?,
            )),
            EggTerm::EvmClz(word) => Box::new(EvmClz::new(is.has_evm_clz()?, self.val(word)?)),
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
            EggTerm::Sext(arg, ty) => Box::new(Sext::new(is.has_sext()?, self.val(arg)?, *ty)),
            EggTerm::Zext(arg, ty) => Box::new(Zext::new(is.has_zext()?, self.val(arg)?, *ty)),
            EggTerm::Trunc(arg, ty) => Box::new(Trunc::new(is.has_trunc()?, self.val(arg)?, *ty)),
            EggTerm::Bitcast(arg, ty) => {
                Box::new(Bitcast::new(is.has_bitcast()?, self.val(arg)?, *ty))
            }
            EggTerm::Value(_) | EggTerm::Global(..) | EggTerm::Undef(..) | EggTerm::Const(..) => {
                return None;
            }
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

    fn cast(&mut self, arg: &EggTerm, ty: Type, op: CastOp) -> Option<ValueId> {
        let arg_val = self.elaborate_value(arg)?;
        let inst = self.cast_inst(arg_val, ty, op)?;
        Some(self.make_inst_value_dyn(inst, ty))
    }

    fn cast_inst(&self, arg: ValueId, ty: Type, op: CastOp) -> Option<Box<dyn Inst>> {
        let is = self.func.inst_set();
        Some(match op {
            CastOp::Sext => Box::new(Sext::new(is.has_sext()?, arg, ty)),
            CastOp::Zext => Box::new(Zext::new(is.has_zext()?, arg, ty)),
            CastOp::Trunc => Box::new(Trunc::new(is.has_trunc()?, arg, ty)),
            CastOp::Bitcast => Box::new(Bitcast::new(is.has_bitcast()?, arg, ty)),
        })
    }

    fn gep(&mut self, base: &EggTerm, indices: &[EggTerm]) -> Option<ValueId> {
        let values = self.gep_values(base, indices)?;
        let mut current_ty = self.func.dfg.value_ty(values[0]);
        if !current_ty.is_pointer(&self.func.dfg.ctx) {
            return None;
        }

        for &index in &values[1..] {
            let compound = current_ty.resolve_compound(&self.func.dfg.ctx)?;
            current_ty = match compound {
                CompoundType::Ptr(elem) | CompoundType::Array { elem, .. } => elem,
                CompoundType::Struct(data) => {
                    let field_idx = self.func.dfg.value_imm(index)?.as_usize();
                    *data.fields.get(field_idx)?
                }
                CompoundType::Func { .. } => return None,
            };
        }

        let ty = if values.len() == 1 {
            current_ty
        } else {
            current_ty.to_ptr(&self.func.dfg.ctx)
        };
        let inst = Box::new(Gep::new(self.func.inst_set().has_gep()?, values));
        Some(self.make_inst_value_dyn(inst, ty))
    }

    fn gep_inst(&mut self, base: &EggTerm, indices: &[EggTerm]) -> Option<Box<dyn Inst>> {
        let values = self.gep_values(base, indices)?;
        Some(Box::new(Gep::new(self.func.inst_set().has_gep()?, values)))
    }

    fn gep_values(
        &mut self,
        base: &EggTerm,
        indices: &[EggTerm],
    ) -> Option<SmallVec<[ValueId; 8]>> {
        let mut values: SmallVec<[ValueId; 8]> = SmallVec::with_capacity(indices.len() + 1);
        values.push(self.elaborate_value(base)?);
        for index in indices {
            values.push(self.elaborate_value(index)?);
        }
        Some(values)
    }

    fn evm_mod(
        &mut self,
        lhs: &EggTerm,
        rhs: &EggTerm,
        modulus: &EggTerm,
        op: EvmMod,
    ) -> Option<ValueId> {
        let lhs_val = self.elaborate_value(lhs)?;
        let inst = self.evm_mod_inst(lhs, rhs, modulus, op)?;
        let ty = self.func.dfg.value_ty(lhs_val);
        Some(self.make_inst_value_dyn(inst, ty))
    }

    fn evm_mod_inst(
        &mut self,
        lhs: &EggTerm,
        rhs: &EggTerm,
        modulus: &EggTerm,
        op: EvmMod,
    ) -> Option<Box<dyn Inst>> {
        let lhs_val = self.elaborate_value(lhs)?;
        let rhs_val = self.elaborate_value(rhs)?;
        let modulus_val = self.elaborate_value(modulus)?;
        let is = self.func.inst_set();
        Some(match op {
            EvmMod::AddMod => Box::new(EvmAddMod::new(
                is.has_evm_add_mod()?,
                lhs_val,
                rhs_val,
                modulus_val,
            )),
            EvmMod::MulMod => Box::new(EvmMulMod::new(
                is.has_evm_mul_mod()?,
                lhs_val,
                rhs_val,
                modulus_val,
            )),
        })
    }

    fn evm_exp(&mut self, base: &EggTerm, exponent: &EggTerm) -> Option<ValueId> {
        let base_val = self.elaborate_value(base)?;
        let exponent_val = self.elaborate_value(exponent)?;
        let ty = self.func.dfg.value_ty(base_val);
        let inst = EvmExp::new(self.func.inst_set().has_evm_exp()?, base_val, exponent_val);
        Some(self.make_inst_value(inst, ty))
    }

    fn evm_byte(&mut self, pos: &EggTerm, value: &EggTerm) -> Option<ValueId> {
        let pos_val = self.elaborate_value(pos)?;
        let value_val = self.elaborate_value(value)?;
        let ty = self.func.dfg.value_ty(value_val);
        let inst = EvmByte::new(self.func.inst_set().has_evm_byte()?, pos_val, value_val);
        Some(self.make_inst_value(inst, ty))
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

#[derive(Clone, Copy)]
enum CastOp {
    Sext,
    Zext,
    Trunc,
    Bitcast,
}

#[derive(Clone, Copy)]
enum EvmMod {
    AddMod,
    MulMod,
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
impl_unary!(EvmClz, has_evm_clz);
