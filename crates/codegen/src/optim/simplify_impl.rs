// TODO: Implement simplification by reassociation.

use smallvec::SmallVec;

use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};

use crate::ir::{
    insn::{BinaryOp, CastOp, JumpOp, UnaryOp},
    Block, DataFlowGraph, Immediate, Insn, InsnData, Type, Value,
};

#[allow(clippy::all)]
mod generated_code;

use generated_code::{Context, SimplifyResult as SimplifyResultImpl};

pub fn simplify_insn(dfg: &mut DataFlowGraph, insn: Insn) -> Option<SimplifyResult> {
    let mut ctx = SimplifyContext::new(dfg);
    let expr = ctx.make_expr_from_insn(insn);
    ctx.simplify_expr(expr)
}

pub fn simplify_insn_data(dfg: &mut DataFlowGraph, data: InsnData) -> Option<SimplifyResult> {
    let mut ctx = SimplifyContext::new(dfg);
    let expr = ctx.make_expr_from_insn_data(data);
    ctx.simplify_expr(expr)
}

pub enum SimplifyResult {
    Value(Value),
    Insn(InsnData),
}

impl SimplifyResult {
    fn from_impl_result(res: SimplifyResultImpl) -> Option<Self> {
        match res {
            SimplifyResultImpl::Value { val } => Some(Self::Value(val)),
            SimplifyResultImpl::Expr { expr } => expr.as_insn_data().map(Self::Insn),
        }
    }
}

fn try_swap_arg(ctx: &mut SimplifyContext, expr: Expr) -> Option<Expr> {
    match ctx.expr_data(expr) {
        ExprData::Binary {
            code,
            args: [lhs, rhs],
        } if code.is_commutative() => {
            let data = ExprData::Binary {
                code,
                args: [rhs, lhs],
            };
            Some(ctx.make_expr(data))
        }
        _ => None,
    }
}

impl BinaryOp {
    fn is_commutative(self) -> bool {
        use BinaryOp::*;

        matches!(self, Add | Mul | And | Or | Xor)
    }
}

type ArgArray1 = [Box<ExprValue>; 1];
type ArgArray2 = [Box<ExprValue>; 2];
type BlockArray1 = [Block; 1];
type BlockArray2 = [Block; 2];

/// An opaque reference to [`ExprData`]
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct Expr(pub u32);
entity_impl!(Expr);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprData {
    /// Unary instructions.
    Unary { code: UnaryOp, args: ArgArray1 },

    /// Binary instructions.
    Binary { code: BinaryOp, args: ArgArray2 },

    /// Cast operations.
    Cast {
        code: CastOp,
        args: ArgArray1,
        ty: Type,
    },

    /// Load a value from memory.
    Load { args: ArgArray1, ty: Type },

    /// Store a value to memory.
    Store { args: ArgArray2 },
    /// Unconditional jump operaitons.
    Jump { code: JumpOp, dests: BlockArray1 },

    /// Conditional jump operations.
    Branch {
        args: [ExprValue; 1],
        dests: BlockArray2,
    },

    /// Return.
    Return { args: SmallVec<[ExprValue; 8]> },

    /// Phi funcion.
    Phi {
        values: SmallVec<[ExprValue; 8]>,
        blocks: SmallVec<[Block; 8]>,
        ty: Type,
    },
}

impl ExprData {
    pub fn from_insn_data(data: &InsnData) -> Self {
        match data {
            InsnData::Unary { code, args } => Self::Unary {
                code: *code,
                args: [ExprValue::from(args[0]).into()],
            },

            InsnData::Binary { code, args } => Self::Binary {
                code: *code,
                args: [
                    ExprValue::from(args[0]).into(),
                    ExprValue::from(args[1]).into(),
                ],
            },

            InsnData::Cast { code, args, ty } => Self::Cast {
                code: *code,
                args: [ExprValue::from(args[0]).into()],
                ty: ty.clone(),
            },

            InsnData::Load { args, ty } => Self::Load {
                args: [ExprValue::from(args[0]).into()],
                ty: ty.clone(),
            },

            InsnData::Store { args } => Self::Store {
                args: [
                    ExprValue::from(args[0]).into(),
                    ExprValue::from(args[1]).into(),
                ],
            },

            InsnData::Jump { code, dests } => Self::Jump {
                code: *code,
                dests: *dests,
            },

            InsnData::Branch { args, dests } => Self::Branch {
                args: [ExprValue::from(args[0]).into()],
                dests: *dests,
            },

            InsnData::Return { args } => Self::Return {
                args: args
                    .iter()
                    .copied()
                    .map(|val| ExprValue::from(val).into())
                    .collect(),
            },

            InsnData::Phi { values, blocks, ty } => Self::Phi {
                values: values
                    .iter()
                    .copied()
                    .map(|val| ExprValue::from(val).into())
                    .collect(),
                blocks: blocks.clone(),
                ty: ty.clone(),
            },
        }
    }

    pub fn as_insn_data(&self) -> Option<InsnData> {
        Some(match self {
            Self::Unary { code, args } => InsnData::Unary {
                code: *code,
                args: [args[0].as_value()?],
            },

            Self::Binary { code, args } => InsnData::Binary {
                code: *code,
                args: [args[0].as_value()?, args[1].as_value()?],
            },

            Self::Cast { code, args, ty } => InsnData::Cast {
                code: *code,
                args: [args[0].as_value()?],
                ty: ty.clone(),
            },

            Self::Load { args, ty } => InsnData::Load {
                args: [args[0].as_value()?],
                ty: ty.clone(),
            },

            Self::Store { args } => InsnData::Store {
                args: [args[0].as_value()?, args[1].as_value()?],
            },

            Self::Jump { code, dests } => InsnData::Jump {
                code: *code,
                dests: *dests,
            },

            Self::Branch { args, dests } => InsnData::Branch {
                args: [args[0].as_value()?],
                dests: *dests,
            },

            Self::Return { args } => InsnData::Return {
                args: args
                    .iter()
                    .map(|arg| arg.as_value())
                    .collect::<Option<_>>()?,
            },

            Self::Phi { values, blocks, ty } => InsnData::Phi {
                values: values
                    .iter()
                    .map(|val| val.as_value())
                    .collect::<Option<_>>()?,
                blocks: blocks.clone(),
                ty: ty.clone(),
            },
        })
    }
}

#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprValue {
    Value(Value),
    #[allow(unused)]
    Expr(Expr),
}

impl ExprValue {
    fn as_value(&self) -> Option<Value> {
        match self {
            Self::Value(val) => Some(*val),
            Self::Expr(_) => None,
        }
    }
}

impl From<Value> for ExprValue {
    fn from(val: Value) -> Self {
        Self::Value(val)
    }
}

struct SimplifyContext<'a> {
    dfg: &'a mut DataFlowGraph,
    exprs: PrimaryMap<Expr, ExprData>,
    types: SecondaryMap<Expr, Option<Type>>,
}

impl<'a> SimplifyContext<'a> {
    fn new(dfg: &'a mut DataFlowGraph) -> Self {
        Self {
            dfg,
            exprs: PrimaryMap::new(),
            types: SecondaryMap::new(),
        }
    }

    fn simplify_expr(&mut self, expr: Expr) -> Option<SimplifyResult> {
        if let Some(res) = generated_code::constructor_simplify(self, expr) {
            if let Some(res) = SimplifyResult::from_impl_result(res) {
                return Some(res);
            }
        }

        let expr = try_swap_arg(self, expr)?;
        let res = generated_code::constructor_simplify(self, expr)?;
        SimplifyResult::from_impl_result(res)
    }

    fn make_expr_from_insn(&mut self, insn: Insn) -> Expr {
        let insn_data = self.dfg.insn_data(insn);
        let expr_data = ExprData::from_insn_data(&insn_data);

        let expr = self.make_expr(expr_data);
        if let Some(insn_result) = self.dfg.insn_result(insn) {
            let ty = self.dfg.value_ty(insn_result);
            self.types[expr] = Some(ty.clone());
        }

        expr
    }

    fn make_expr_from_insn_data(&mut self, data: InsnData) -> Expr {
        let expr_data = ExprData::from_insn_data(&data);

        let expr = self.make_expr(expr_data);
        if let Some(ty) = data.result_type(&self.dfg) {
            self.types[expr] = Some(ty.clone());
        }

        expr
    }

    fn dfg(&mut self) -> &mut DataFlowGraph {
        self.dfg
    }

    fn make_expr(&mut self, data: ExprData) -> Expr {
        self.exprs.push(data)
    }
}

impl<'a> generated_code::Context for SimplifyContext<'a> {
    fn unpack_arg_array1(&mut self, arg0: &ArgArray1) -> ExprValue {
        *arg0[0].clone()
    }

    fn pack_arg_array1(&mut self, arg0: ExprValue) -> ArgArray1 {
        [arg0.clone().into()]
    }

    fn unpack_arg_array2(&mut self, arg0: &ArgArray2) -> (ExprValue, ExprValue) {
        (*arg0[0].clone(), *arg0[1].clone())
    }

    fn pack_arg_array2(&mut self, arg0: ExprValue, arg1: ExprValue) -> ArgArray2 {
        [arg0.clone().into(), arg1.clone().into()]
    }

    fn value_ty(&mut self, arg0: ExprValue) -> Type {
        match arg0 {
            ExprValue::Value(val) => self.dfg().value_ty(val).clone(),
            ExprValue::Expr(expr) => self.types[expr].clone().unwrap(),
        }
    }

    fn expr_data(&mut self, arg0: Expr) -> ExprData {
        self.exprs[arg0].clone()
    }

    fn value_expr(&mut self, arg0: ExprValue) -> Option<Expr> {
        match arg0 {
            ExprValue::Value(val) => {
                let insn = self.dfg().value_insn(val)?;
                let insn_data = self.dfg().insn_data(insn);
                let data = ExprData::from_insn_data(&insn_data);
                Some(self.make_expr(data))
            }
            ExprValue::Expr(expr) => Some(expr),
        }
    }

    fn is_zero(&mut self, arg0: ExprValue) -> bool {
        if let Some(value) = arg0.as_value() {
            self.dfg()
                .value_imm(value)
                .map(|imm| imm.is_zero())
                .unwrap_or_default()
        } else {
            false
        }
    }

    fn is_one(&mut self, arg0: ExprValue) -> bool {
        if let Some(value) = arg0.as_value() {
            self.dfg()
                .value_imm(value)
                .map(|imm| imm.is_one())
                .unwrap_or_default()
        } else {
            false
        }
    }

    fn is_two(&mut self, arg0: ExprValue) -> bool {
        if let Some(value) = arg0.as_value() {
            self.dfg()
                .value_imm(value)
                .map(|imm| imm.is_two())
                .unwrap_or_default()
        } else {
            false
        }
    }

    fn is_all_one(&mut self, arg0: ExprValue) -> bool {
        if let Some(value) = arg0.as_value() {
            self.dfg()
                .value_imm(value)
                .map(|imm| imm.is_all_one())
                .unwrap_or_default()
        } else {
            false
        }
    }

    fn is_power_of_two(&mut self, arg0: ExprValue) -> bool {
        if let Some(value) = arg0.as_value() {
            self.dfg()
                .value_imm(value)
                .map(|imm| imm.is_power_of_two())
                .unwrap_or_default()
        } else {
            false
        }
    }

    fn is_same(&mut self, arg0: ExprValue, arg1: ExprValue) -> bool {
        match (arg0.as_value(), arg1.as_value()) {
            (Some(val1), Some(val2)) => self.dfg.is_same_value(val1, val2),
            _ => arg0 == arg1,
        }
    }

    fn make_zero(&mut self, arg0: &Type) -> ExprValue {
        let imm = Immediate::zero(arg0);
        let val = self.dfg().make_imm_value(imm);
        ExprValue::Value(val)
    }

    fn make_one(&mut self, arg0: &Type) -> ExprValue {
        let imm = Immediate::one(arg0);
        let val = self.dfg().make_imm_value(imm);
        ExprValue::Value(val)
    }

    fn make_all_one(&mut self, arg0: &Type) -> ExprValue {
        let imm = Immediate::all_one(arg0);
        let val = self.dfg().make_imm_value(imm);
        ExprValue::Value(val)
    }

    fn make_result(&mut self, arg0: ExprValue) -> SimplifyResultImpl {
        match arg0 {
            ExprValue::Value(val) => SimplifyResultImpl::Value { val },
            ExprValue::Expr(expr) => SimplifyResultImpl::Expr {
                expr: self.exprs[expr].clone(),
            },
        }
    }
}
