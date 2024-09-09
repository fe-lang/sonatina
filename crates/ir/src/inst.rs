use sonatina_macros::Inst;
use std::any::{Any, TypeId};

use smallvec::SmallVec;

use crate::{module::FuncRef, Block, Type, Value};

pub trait Inst: Any {
    fn visit_values(&self, f: &mut dyn FnMut(Value));
    fn visit_values_mut(&mut self, f: &mut dyn FnMut(&mut Value));
    fn has_side_effect(&self) -> bool;
    fn as_text(&self) -> &'static str;
}

/// This trait works as a "proof" that a specific ISA contains `I`,
/// and then allows a construction and reflection of type `I` in that specific ISA context.
pub trait HasInst<I: Inst> {
    fn is(&self, inst: &dyn Inst) -> bool {
        inst.type_id() == TypeId::of::<I>()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Not {
    #[inst(visit_value)]
    arg: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Neg {
    #[inst(visit_value)]
    arg: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Add {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Mul {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sub {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Sdiv {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Udiv {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Lt {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Gt {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Slt {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sgt {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Le {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Ge {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sle {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sge {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Eq {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Ne {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct And {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Or {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Xor {
    #[inst(visit_value)]
    lhs: Value,
    #[inst(visit_value)]
    rhs: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Sext {
    #[inst(visit_value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Zext {
    #[inst(visit_value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Trunc {
    #[inst(visit_value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct BitCast {
    #[inst(visit_value)]
    from: Value,
    ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Mload {
    #[inst(visit_value)]
    addr: Value,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Sload {
    #[inst(visit_value)]
    value: Value,
    #[inst(visit_value)]
    addr: Value,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Call {
    #[inst(visit_value)]
    args: SmallVec<[Value; 8]>,
    callee: FuncRef,
    ret_ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Jump {
    dest: Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Br {
    #[inst(visit_value)]
    cond: Value,

    z_dest: Block,
    nz_dest: Block,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct BrTable {
    #[inst(visit_value)]
    scrutinee: Value,
    #[inst(visit_value)]
    table: Vec<(Value, Block)>,

    default: Option<Block>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Alloca {
    ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = true)]
pub struct Return {
    #[inst(visit_value)]
    arg: Option<Value>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Gep {
    #[inst(visit_value)]
    values: SmallVec<[Value; 8]>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Inst)]
#[inst(side_effect = false)]
pub struct Phi {
    #[inst(visit_value)]
    values: Vec<(Value, Block)>,
    ty: Type,
}

pub(crate) trait ValueVisitable {
    fn visit_with(&self, f: &mut dyn FnMut(Value));
    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut Value));
}

impl ValueVisitable for Value {
    fn visit_with(&self, f: &mut dyn FnMut(Value)) {
        f(*self)
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut Value)) {
        f(self)
    }
}

impl<V> ValueVisitable for Option<V>
where
    V: ValueVisitable,
{
    fn visit_with(&self, f: &mut dyn FnMut(Value)) {
        if let Some(value) = self {
            value.visit_with(f)
        }
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut Value)) {
        if let Some(value) = self.as_mut() {
            value.visit_mut_with(f)
        }
    }
}

impl<V, T> ValueVisitable for (V, T)
where
    V: ValueVisitable,
{
    fn visit_with(&self, f: &mut dyn FnMut(Value)) {
        self.0.visit_with(f)
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut Value)) {
        self.0.visit_mut_with(f)
    }
}

impl<V> ValueVisitable for Vec<V>
where
    V: ValueVisitable,
{
    fn visit_with(&self, f: &mut dyn FnMut(Value)) {
        self.iter().for_each(|v| v.visit_with(f))
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut Value)) {
        self.iter_mut().for_each(|v| v.visit_mut_with(f))
    }
}

impl<V> ValueVisitable for [V]
where
    V: ValueVisitable,
{
    fn visit_with(&self, f: &mut dyn FnMut(Value)) {
        self.iter().for_each(|v| v.visit_with(f))
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut Value)) {
        self.iter_mut().for_each(|v| v.visit_mut_with(f))
    }
}

impl<V, const N: usize> ValueVisitable for SmallVec<[V; N]>
where
    V: ValueVisitable,
    [V; N]: smallvec::Array<Item = V>,
{
    fn visit_with(&self, f: &mut dyn FnMut(Value)) {
        self.iter().for_each(|v| v.visit_with(f))
    }

    fn visit_mut_with(&mut self, f: &mut dyn FnMut(&mut Value)) {
        self.iter_mut().for_each(|v| v.visit_mut_with(f))
    }
}
