use std::io;

use smallvec::SmallVec;

use super::{DataFlowGraph, Layout, Type, ValueId};
use crate::{InstSetBase, Linkage, ir_writer::IrWrite, module::ModuleCtx};

pub struct Function {
    pub arg_values: smallvec::SmallVec<[ValueId; 8]>,
    pub dfg: DataFlowGraph,
    pub layout: Layout,
}

impl Function {
    pub fn new(ctx: &ModuleCtx, sig: &Signature) -> Self {
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
            arg_values,
            dfg,
            layout: Layout::default(),
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

    pub fn update_linkage(&mut self, linkage: Linkage) {
        self.linkage = linkage;
    }

    pub fn args(&self) -> &[Type] {
        &self.args
    }

    pub fn ret_ty(&self) -> Type {
        self.ret_ty
    }

    pub fn func_ptr_type(&self, ctx: &ModuleCtx) -> Type {
        ctx.with_ty_store_mut(|s| {
            let func_ty = s.make_func(&self.args, self.ret_ty);
            s.make_ptr(func_ty)
        })
    }

    #[doc(hidden)]
    pub fn set_ret_ty(&mut self, ty: Type) {
        self.ret_ty = ty;
    }
}

impl<Ctx> IrWrite<Ctx> for Signature
where
    Ctx: AsRef<ModuleCtx>,
{
    fn write<W>(&self, w: &mut W, ctx: &Ctx) -> io::Result<()>
    where
        W: io::Write,
    {
        write!(w, "func ")?;
        self.linkage.write(w, ctx)?;
        write!(w, " %{}(", self.name)?;
        self.args.write_with_delim(w, " ", ctx)?;
        write!(w, ")")?;

        if !self.ret_ty.is_unit() {
            write!(w, " -> ")?;
            self.ret_ty.write(w, ctx)?;
        }

        Ok(())
    }
}
