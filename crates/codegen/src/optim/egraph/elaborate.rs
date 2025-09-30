//! Elaboration: Convert egraph terms back to sonatina IR.

use rustc_hash::FxHashMap;

use sonatina_ir::{
    inst::{arith::*, cmp::*, logic::*},
    BlockId, Function, Type, Value, ValueId,
};

/// Represents an egglog term that can be elaborated back to IR.
#[derive(Debug, Clone)]
pub enum EggTerm {
    Var(String),
    Const(i64, Type),
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

/// Elaborator converts egraph terms back to sonatina IR instructions.
pub struct Elaborator<'a> {
    func: &'a mut Function,
    block: BlockId,
    /// Maps variable names to their ValueIds
    var_map: FxHashMap<String, ValueId>,
}

impl<'a> Elaborator<'a> {
    pub fn new(func: &'a mut Function, block: BlockId) -> Self {
        Self {
            func,
            block,
            var_map: FxHashMap::default(),
        }
    }

    /// Register an existing value with a variable name.
    pub fn bind_var(&mut self, name: String, value: ValueId) {
        self.var_map.insert(name, value);
    }

    /// Elaborate a term into IR, returning the resulting ValueId.
    pub fn elaborate(&mut self, term: &EggTerm, ty: Type) -> ValueId {
        match term {
            EggTerm::Var(name) => *self.var_map.get(name).expect("undefined variable"),
            EggTerm::Const(val, ty) => self
                .func
                .dfg
                .make_imm_value(sonatina_ir::Immediate::from_i256((*val).into(), *ty)),
            EggTerm::Add(lhs, rhs) => self.elaborate_binary::<Add>(lhs, rhs, ty),
            EggTerm::Sub(lhs, rhs) => self.elaborate_binary::<Sub>(lhs, rhs, ty),
            EggTerm::Mul(lhs, rhs) => self.elaborate_binary::<Mul>(lhs, rhs, ty),
            EggTerm::Udiv(lhs, rhs) => self.elaborate_binary::<Udiv>(lhs, rhs, ty),
            EggTerm::Sdiv(lhs, rhs) => self.elaborate_binary::<Sdiv>(lhs, rhs, ty),
            EggTerm::Umod(lhs, rhs) => self.elaborate_binary::<Umod>(lhs, rhs, ty),
            EggTerm::Smod(lhs, rhs) => self.elaborate_binary::<Smod>(lhs, rhs, ty),
            EggTerm::Shl(bits, val) => self.elaborate_shift::<Shl>(bits, val, ty),
            EggTerm::Shr(bits, val) => self.elaborate_shift::<Shr>(bits, val, ty),
            EggTerm::Sar(bits, val) => self.elaborate_shift::<Sar>(bits, val, ty),
            EggTerm::Neg(arg) => self.elaborate_unary::<Neg>(arg, ty),
            EggTerm::Not(arg) => self.elaborate_unary::<Not>(arg, ty),
            EggTerm::And(lhs, rhs) => self.elaborate_binary::<And>(lhs, rhs, ty),
            EggTerm::Or(lhs, rhs) => self.elaborate_binary::<Or>(lhs, rhs, ty),
            EggTerm::Xor(lhs, rhs) => self.elaborate_binary::<Xor>(lhs, rhs, ty),
            EggTerm::Lt(lhs, rhs) => self.elaborate_cmp::<Lt>(lhs, rhs, ty),
            EggTerm::Gt(lhs, rhs) => self.elaborate_cmp::<Gt>(lhs, rhs, ty),
            EggTerm::Le(lhs, rhs) => self.elaborate_cmp::<Le>(lhs, rhs, ty),
            EggTerm::Ge(lhs, rhs) => self.elaborate_cmp::<Ge>(lhs, rhs, ty),
            EggTerm::Slt(lhs, rhs) => self.elaborate_cmp::<Slt>(lhs, rhs, ty),
            EggTerm::Sgt(lhs, rhs) => self.elaborate_cmp::<Sgt>(lhs, rhs, ty),
            EggTerm::Sle(lhs, rhs) => self.elaborate_cmp::<Sle>(lhs, rhs, ty),
            EggTerm::Sge(lhs, rhs) => self.elaborate_cmp::<Sge>(lhs, rhs, ty),
            EggTerm::Eq(lhs, rhs) => self.elaborate_cmp::<Eq>(lhs, rhs, ty),
            EggTerm::Ne(lhs, rhs) => self.elaborate_cmp::<Ne>(lhs, rhs, ty),
            EggTerm::IsZero(arg) => self.elaborate_iszero(arg, ty),
        }
    }

    fn elaborate_binary<I>(&mut self, lhs: &EggTerm, rhs: &EggTerm, ty: Type) -> ValueId
    where
        I: BinaryInst,
    {
        let lhs_val = self.elaborate(lhs, ty);
        let rhs_val = self.elaborate(rhs, ty);
        let is = self.func.inst_set();
        let inst = I::new(is, lhs_val, rhs_val);
        self.make_inst_value(inst, ty)
    }

    fn elaborate_shift<I>(&mut self, bits: &EggTerm, val: &EggTerm, ty: Type) -> ValueId
    where
        I: ShiftInst,
    {
        let bits_val = self.elaborate(bits, ty);
        let val_val = self.elaborate(val, ty);
        let is = self.func.inst_set();
        let inst = I::new(is, bits_val, val_val);
        self.make_inst_value(inst, ty)
    }

    fn elaborate_unary<I>(&mut self, arg: &EggTerm, ty: Type) -> ValueId
    where
        I: UnaryInst,
    {
        let arg_val = self.elaborate(arg, ty);
        let is = self.func.inst_set();
        let inst = I::new(is, arg_val);
        self.make_inst_value(inst, ty)
    }

    fn elaborate_cmp<I>(&mut self, lhs: &EggTerm, rhs: &EggTerm, ty: Type) -> ValueId
    where
        I: BinaryInst,
    {
        let lhs_val = self.elaborate(lhs, ty);
        let rhs_val = self.elaborate(rhs, ty);
        let is = self.func.inst_set();
        let inst = I::new(is, lhs_val, rhs_val);
        self.make_inst_value(inst, Type::I1)
    }

    fn elaborate_iszero(&mut self, arg: &EggTerm, ty: Type) -> ValueId {
        let arg_val = self.elaborate(arg, ty);
        let is = self.func.inst_set();
        let inst = IsZero::new(is.has_is_zero().unwrap(), arg_val);
        self.make_inst_value(inst, Type::I1)
    }

    fn make_inst_value<I: sonatina_ir::Inst>(&mut self, inst: I, ty: Type) -> ValueId {
        let inst_id = self.func.dfg.make_inst(inst);
        let value = Value::Inst { inst: inst_id, ty };
        let value_id = self.func.dfg.make_value(value);
        self.func.dfg.attach_result(inst_id, value_id);
        self.func.layout.append_inst(inst_id, self.block);
        value_id
    }
}

/// Trait for binary instructions that can be constructed.
trait BinaryInst: sonatina_ir::Inst + Sized {
    fn new(is: &dyn sonatina_ir::InstSetBase, lhs: ValueId, rhs: ValueId) -> Self;
}

/// Trait for shift instructions.
trait ShiftInst: sonatina_ir::Inst + Sized {
    fn new(is: &dyn sonatina_ir::InstSetBase, bits: ValueId, value: ValueId) -> Self;
}

/// Trait for unary instructions.
trait UnaryInst: sonatina_ir::Inst + Sized {
    fn new(is: &dyn sonatina_ir::InstSetBase, arg: ValueId) -> Self;
}

// Implement BinaryInst for binary ops
macro_rules! impl_binary {
    ($ty:ty, $has:ident) => {
        impl BinaryInst for $ty {
            fn new(is: &dyn sonatina_ir::InstSetBase, lhs: ValueId, rhs: ValueId) -> Self {
                <$ty>::new(is.$has().unwrap(), lhs, rhs)
            }
        }
    };
}

impl_binary!(Add, has_add);
impl_binary!(Sub, has_sub);
impl_binary!(Mul, has_mul);
impl_binary!(Udiv, has_udiv);
impl_binary!(Sdiv, has_sdiv);
impl_binary!(Umod, has_umod);
impl_binary!(Smod, has_smod);
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

// Implement ShiftInst for shift ops
macro_rules! impl_shift {
    ($ty:ty, $has:ident) => {
        impl ShiftInst for $ty {
            fn new(is: &dyn sonatina_ir::InstSetBase, bits: ValueId, value: ValueId) -> Self {
                <$ty>::new(is.$has().unwrap(), bits, value)
            }
        }
    };
}

impl_shift!(Shl, has_shl);
impl_shift!(Shr, has_shr);
impl_shift!(Sar, has_sar);

// Implement UnaryInst for unary ops
macro_rules! impl_unary {
    ($ty:ty, $has:ident) => {
        impl UnaryInst for $ty {
            fn new(is: &dyn sonatina_ir::InstSetBase, arg: ValueId) -> Self {
                <$ty>::new(is.$has().unwrap(), arg)
            }
        }
    };
}

impl_unary!(Neg, has_neg);
impl_unary!(Not, has_not);
