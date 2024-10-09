use std::io;

use rustc_hash::FxHashMap;
use smallvec::SmallVec;

use super::{module::FuncRef, DataFlowGraph, Layout, Type, ValueId};
use crate::{
    ir_writer::{WriteWithFunc, WriteWithModule},
    module::ModuleCtx,
    InstSetBase, Linkage,
};

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

    pub fn ctx(&self) -> &ModuleCtx {
        &self.dfg.ctx
    }

    pub fn inst_set(&self) -> &'static dyn InstSetBase {
        self.dfg.inst_set()
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

impl WriteWithFunc for Signature {
    fn write(&self, func: &Function, w: &mut impl io::Write) -> io::Result<()> {
        let Signature {
            name,
            linkage,
            args,
            ret_ty,
        } = self;

        write!(w, "func {linkage} %{name}(")?;
        let mut args = args.iter();
        if let Some(arg) = args.next() {
            arg.write(func.ctx(), &mut *w)?;
        };

        for arg in args {
            write!(w, " ")?;
            arg.write(func.ctx(), &mut *w)?;
        }
        write!(w, ") -> ")?;

        ret_ty.write(func.ctx(), &mut *w)
    }
}
