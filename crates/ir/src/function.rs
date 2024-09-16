use super::{module::FuncRef, DataFlowGraph, Layout, Type, ValueId};
use crate::{module::ModuleCtx, types::DisplayType, Linkage};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::fmt::{self, Write};

#[derive(Debug, Clone)]
pub struct Function {
    /// Signature of the function.
    pub sig: Signature,
    pub arg_values: smallvec::SmallVec<[ValueId; 8]>,
    pub dfg: DataFlowGraph,
    pub layout: Layout,

    /// Stores signatures of all functions that are called by the function.
    pub callees: FxHashMap<FuncRef, Signature>,
}

impl Function {
    pub fn new(ctx: &ModuleCtx, sig: Signature) -> Self {
        let mut dfg = DataFlowGraph::new(ctx.clone());
        let arg_values = sig
            .args()
            .iter()
            .enumerate()
            .map(|(idx, arg_ty)| {
                let value = dfg.make_arg_value(*arg_ty, idx);
                dfg.make_value(value)
            })
            .collect();

        Self {
            sig,
            arg_values,
            dfg,
            layout: Layout::default(),
            callees: FxHashMap::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Signature {
    /// Name of the function.
    name: String,

    /// Linkage of the function.
    linkage: Linkage,

    args: SmallVec<[Type; 8]>,
    ret_ty: Type,
}

impl Signature {
    pub fn new(name: &str, linkage: Linkage, args: &[Type], ret_ty: Type) -> Self {
        Self {
            name: name.to_string(),
            linkage,
            args: args.into(),
            ret_ty,
        }
    }
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn linkage(&self) -> Linkage {
        self.linkage
    }

    pub fn args(&self) -> &[Type] {
        &self.args
    }

    pub fn ret_ty(&self) -> Type {
        self.ret_ty
    }

    #[doc(hidden)]
    pub fn set_ret_ty(&mut self, ty: Type) {
        self.ret_ty = ty;
    }
}

pub struct DisplaySignature<'a, 'b> {
    sig: &'a Signature,
    dfg: &'b DataFlowGraph,
}

impl<'a, 'b> DisplaySignature<'a, 'b> {
    pub fn new(sig: &'a Signature, dfg: &'b DataFlowGraph) -> Self {
        Self { sig, dfg }
    }
}

impl<'a, 'b> fmt::Display for DisplaySignature<'a, 'b> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Self { sig, dfg } = *self;
        let Signature {
            name,
            linkage,
            args,
            ret_ty,
        } = sig;

        let mut args_ty = String::new();
        for arg_ty in args {
            let ty = DisplayType::new(*arg_ty, dfg);
            write!(&mut args_ty, "{ty} ")?;
        }
        let args_ty = args_ty.trim();

        let ret_ty = DisplayType::new(*ret_ty, dfg);

        write!(f, "func {linkage} %{name}({args_ty}) -> {ret_ty}")
    }
}
