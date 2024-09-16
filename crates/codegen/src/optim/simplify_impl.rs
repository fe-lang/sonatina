// TODO: Implement simplification by reassociation.

use smallvec::SmallVec;

use cranelift_entity::{entity_impl, PrimaryMap, SecondaryMap};

use sonatina_ir::{
    insn::{BinaryOp, CastOp, DataLocationKind, UnaryOp},
    module::FuncRef,
    Block, DataFlowGraph, Immediate, Insn, InsnData, Type, ValueId,
};

#[allow(clippy::all)]
mod generated_code;

use generated_code::{Context, SimplifyRawResult};

pub fn simplify_insn(dfg: &mut DataFlowGraph, insn: Insn) -> Option<SimplifyResult> {
    if dfg.is_phi(insn) {
        return simplify_phi(dfg.insn_data(insn));
    }

    let mut ctx = SimplifyContext::new(dfg);
    let expr = ctx.make_expr_from_insn(insn);
    ctx.simplify_expr(expr)
}

pub fn simplify_insn_data(dfg: &mut DataFlowGraph, data: InsnData) -> Option<SimplifyResult> {
    if matches!(data, InsnData::Phi { .. }) {
        return simplify_phi(&data);
    }

    let mut ctx = SimplifyContext::new(dfg);
    let expr = ctx.make_expr_from_insn_data(data);
    ctx.simplify_expr(expr)
}

pub enum SimplifyResult {
    Value(ValueId),
    Insn(InsnData),
}

fn simplify_phi(insn_data: &InsnData) -> Option<SimplifyResult> {
    match insn_data {
        InsnData::Phi { values, .. } => {
            let mut values = values.iter().copied();
            let first_value = values.next().unwrap();
            if values.all(|value| value == first_value) {
                Some(SimplifyResult::Value(first_value))
            } else {
                None
            }
        }
        _ => unreachable!(),
    }
}

impl SimplifyResult {
    fn from_raw(res: SimplifyRawResult) -> Option<Self> {
        match res {
            SimplifyRawResult::Value { val } => Some(Self::Value(val)),
            SimplifyRawResult::Expr { expr } => expr.as_insn_data().map(Self::Insn),
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

type Unit = ();
type ArgArray1 = [ExprValue; 1];
type ArgArray2 = [ExprValue; 2];
type BlockArray1 = [Block; 1];
type BlockArray2 = [Block; 2];

type BlockList = SmallVec<[Block; 8]>;
type ArgList = SmallVec<[ExprValue; 8]>;
type BrTableDefaultDest = Option<Block>;

/// An opaque reference to [`ExprData`]
#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash, PartialOrd, Ord)]
pub struct Expr(pub u32);
entity_impl!(Expr);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprData {
    /// Unary instructions.
    Unary {
        code: UnaryOp,
        args: ArgArray1,
    },

    /// Binary instructions.
    Binary {
        code: BinaryOp,
        args: ArgArray2,
    },

    /// Cast operations.
    Cast {
        code: CastOp,
        args: ArgArray1,
        ty: Type,
    },

    /// Load a value from memory or storage.
    Load {
        args: ArgArray1,
        loc: DataLocationKind,
    },

    /// Store a value to memory or storage.
    Store {
        args: ArgArray2,
        loc: DataLocationKind,
    },
    Call {
        func: FuncRef,
        args: ArgList,
        ret_ty: Type,
    },

    /// Unconditional jump operations.
    Jump {
        dests: BlockArray1,
    },

    /// Conditional jump operations.
    Branch {
        args: ArgArray1,
        dests: BlockArray2,
    },

    /// Indirect jump.
    BrTable {
        args: ArgList,
        default: BrTableDefaultDest,
        table: BlockList,
    },

    Alloca {
        ty: Type,
    },

    /// Return.
    Return {
        args: Option<ValueId>,
    },

    Gep {
        args: ArgList,
    },

    /// Phi function.
    Phi {
        values: ArgList,
        blocks: BlockList,
        ty: Type,
    },
}

impl ExprData {
    pub fn from_insn_data(data: &InsnData) -> Self {
        match data {
            InsnData::Unary { code, args } => Self::Unary {
                code: *code,
                args: [args[0].into()],
            },

            InsnData::Binary { code, args } => Self::Binary {
                code: *code,
                args: [args[0].into(), args[1].into()],
            },

            InsnData::Cast { code, args, ty } => Self::Cast {
                code: *code,
                args: [args[0].into()],
                ty: *ty,
            },

            InsnData::Load { args, loc } => Self::Load {
                args: [args[0].into()],
                loc: *loc,
            },

            InsnData::Store { args, loc } => Self::Store {
                args: [args[0].into(), args[1].into()],
                loc: *loc,
            },

            InsnData::Call { func, args, ret_ty } => Self::Call {
                func: *func,
                args: args.iter().copied().map(Into::into).collect(),
                ret_ty: *ret_ty,
            },

            InsnData::Jump { dests } => Self::Jump { dests: *dests },

            InsnData::Branch { args, dests } => Self::Branch {
                args: [args[0].into()],
                dests: *dests,
            },

            InsnData::BrTable {
                args,
                default,
                table,
            } => Self::BrTable {
                args: args.iter().copied().map(Into::into).collect(),
                default: *default,
                table: table.clone(),
            },

            InsnData::Alloca { ty } => Self::Alloca { ty: *ty },

            InsnData::Gep { args } => Self::Gep {
                args: args.iter().copied().map(Into::into).collect(),
            },

            InsnData::Return { args } => Self::Return { args: *args },

            InsnData::Phi { values, blocks, ty } => Self::Phi {
                values: values.iter().copied().map(Into::into).collect(),
                blocks: blocks.clone(),
                ty: *ty,
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
                ty: *ty,
            },

            Self::Load { args, loc } => InsnData::Load {
                args: [args[0].as_value()?],
                loc: *loc,
            },

            Self::Store { args, loc } => InsnData::Store {
                args: [args[0].as_value()?, args[1].as_value()?],
                loc: *loc,
            },

            Self::Call { func, args, ret_ty } => InsnData::Call {
                func: *func,
                args: args
                    .iter()
                    .map(|val| val.as_value())
                    .collect::<Option<_>>()?,
                ret_ty: *ret_ty,
            },

            Self::Jump { dests } => InsnData::Jump { dests: *dests },

            Self::Branch { args, dests } => InsnData::Branch {
                args: [args[0].as_value()?],
                dests: *dests,
            },

            Self::BrTable {
                args,
                default,
                table,
            } => InsnData::BrTable {
                args: args
                    .iter()
                    .map(|val| val.as_value())
                    .collect::<Option<_>>()?,
                default: *default,
                table: table.clone(),
            },

            Self::Alloca { ty } => InsnData::alloca(*ty),

            Self::Gep { args } => InsnData::Gep {
                args: args
                    .iter()
                    .map(|val| val.as_value())
                    .collect::<Option<_>>()?,
            },

            Self::Return { args } => InsnData::Return { args: *args },

            Self::Phi { values, blocks, ty } => InsnData::Phi {
                values: values
                    .iter()
                    .map(|val| val.as_value())
                    .collect::<Option<_>>()?,
                blocks: blocks.clone(),
                ty: *ty,
            },
        })
    }
}

#[doc(hidden)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprValue {
    Value(ValueId),
    #[allow(unused)]
    Expr(Expr),
}

impl ExprValue {
    fn as_value(&self) -> Option<ValueId> {
        match self {
            Self::Value(val) => Some(*val),
            Self::Expr(_) => None,
        }
    }
}

impl From<ValueId> for ExprValue {
    fn from(val: ValueId) -> Self {
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
        if let Some(res) =
            generated_code::constructor_simplify(self, expr).and_then(SimplifyResult::from_raw)
        {
            return Some(res);
        }

        let expr = try_swap_arg(self, expr)?;
        generated_code::constructor_simplify(self, expr).and_then(SimplifyResult::from_raw)
    }

    fn make_expr_from_insn(&mut self, insn: Insn) -> Expr {
        let insn_data = self.dfg.insn_data(insn);
        let expr_data = ExprData::from_insn_data(insn_data);

        let expr = self.make_expr(expr_data);
        if let Some(insn_result) = self.dfg.insn_result(insn) {
            let ty = self.dfg.value_ty(insn_result);
            self.types[expr] = Some(ty);
        }

        expr
    }

    fn make_expr_from_insn_data(&mut self, data: InsnData) -> Expr {
        let expr_data = ExprData::from_insn_data(&data);

        let expr = self.make_expr(expr_data);
        if let Some(ty) = data.result_type(self.dfg) {
            self.types[expr] = Some(ty);
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
        arg0[0]
    }

    fn pack_arg_array1(&mut self, arg0: ExprValue) -> ArgArray1 {
        [arg0]
    }

    fn unpack_arg_array2(&mut self, arg0: &ArgArray2) -> (ExprValue, ExprValue) {
        (arg0[0], arg0[1])
    }

    fn pack_arg_array2(&mut self, arg0: ExprValue, arg1: ExprValue) -> ArgArray2 {
        [arg0, arg1]
    }

    fn value_ty(&mut self, arg0: ExprValue) -> Type {
        match arg0 {
            ExprValue::Value(val) => self.dfg().value_ty(val),
            ExprValue::Expr(expr) => self.types[expr].unwrap(),
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
                let data = ExprData::from_insn_data(insn_data);
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

    fn is_eq(&mut self, arg0: ExprValue, arg1: ExprValue) -> Option<()> {
        match (arg0.as_value(), arg1.as_value()) {
            (Some(val1), Some(val2)) => val1 == val2,
            _ => arg0 == arg1,
        }
        .then_some(())
    }

    fn make_zero(&mut self, arg0: Type) -> ExprValue {
        let imm = Immediate::zero(arg0);
        let val = self.dfg().make_imm_value(imm);
        ExprValue::Value(val)
    }

    fn make_one(&mut self, arg0: Type) -> ExprValue {
        let imm = Immediate::one(arg0);
        let val = self.dfg().make_imm_value(imm);
        ExprValue::Value(val)
    }

    fn make_true(&mut self) -> ExprValue {
        self.make_all_one(Type::I1)
    }

    fn make_false(&mut self) -> ExprValue {
        self.make_zero(Type::I1)
    }

    fn make_all_one(&mut self, arg0: Type) -> ExprValue {
        let imm = Immediate::all_one(arg0);
        let val = self.dfg().make_imm_value(imm);
        ExprValue::Value(val)
    }

    fn make_result(&mut self, arg0: ExprValue) -> SimplifyRawResult {
        match arg0 {
            ExprValue::Value(val) => SimplifyRawResult::Value { val },
            ExprValue::Expr(expr) => SimplifyRawResult::Expr {
                expr: self.exprs[expr].clone(),
            },
        }
    }
}
