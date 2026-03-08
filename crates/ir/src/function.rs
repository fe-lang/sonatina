use std::io;

use smallvec::SmallVec;

use super::{BlockId, DataFlowGraph, InstId, Layout, Type, ValueId};
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

    pub fn erase_inst(&mut self, inst: InstId) {
        assert!(self.layout.has_inst_slot(inst));
        assert!(
            !self.layout.is_inst_inserted(inst),
            "instruction {inst:?} must be detached before erase"
        );
        self.dfg.delete_inst(inst);
    }

    pub fn erase_insts(&mut self, insts: &[InstId]) {
        for &inst in insts {
            assert!(self.layout.has_inst_slot(inst));
            assert!(
                !self.layout.is_inst_inserted(inst),
                "instruction {inst:?} must be detached before erase"
            );
            self.dfg.untrack_inst(inst);
        }

        for &inst in insts {
            self.dfg.delete_inst(inst);
        }
    }

    pub fn erase_block(&mut self, block: BlockId) {
        assert!(self.layout.has_block_slot(block));
        assert!(
            !self.layout.is_block_inserted(block),
            "block {block:?} must be detached before erase"
        );
        assert!(
            self.layout.try_first_inst_of(block) == Some(None),
            "block {block:?} must be empty before erase"
        );
        self.dfg.delete_block(block);
    }

    /// Recompute `dfg.users` from scratch using only layout-inserted instructions.
    ///
    /// Call this after passes that may leave stale user entries (e.g. egraph).
    pub fn rebuild_users(&mut self) {
        self.dfg.clear_users();
        for block in self.layout.iter_block() {
            for inst in self.layout.iter_inst(block) {
                self.dfg.attach_user(inst);
            }
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
    ret_tys: SmallVec<[Type; 2]>,
}

impl Signature {
    pub fn new(name: &str, linkage: Linkage, args: &[Type], ret_tys: &[Type]) -> Self {
        Self {
            name: name.to_string(),
            linkage,
            args: args.into(),
            ret_tys: ret_tys.into(),
        }
    }

    pub fn new_unit(name: &str, linkage: Linkage, args: &[Type]) -> Self {
        Self::new(name, linkage, args, &[])
    }

    pub fn new_single(name: &str, linkage: Linkage, args: &[Type], ret_ty: Type) -> Self {
        Self::new(name, linkage, args, &[ret_ty])
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

    pub fn ret_tys(&self) -> &[Type] {
        &self.ret_tys
    }

    pub fn returns_unit(&self) -> bool {
        self.ret_tys.is_empty()
    }

    pub fn returns_single(&self) -> bool {
        self.ret_tys.len() == 1
    }

    pub fn single_ret_ty(&self) -> Option<Type> {
        (self.ret_tys.len() == 1).then(|| self.ret_tys[0])
    }

    pub fn ret_ty(&self) -> Type {
        match self.ret_tys.as_slice() {
            [] => Type::Unit,
            [ret_ty] => *ret_ty,
            _ => panic!("ret_ty called on multi-return signature {}", self.name),
        }
    }

    pub fn func_ptr_type(&self, ctx: &ModuleCtx) -> Type {
        ctx.with_ty_store_mut(|s| {
            let func_ty = s.make_func(&self.args, &self.ret_tys);
            s.make_ptr(func_ty)
        })
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
        self.linkage.write(w, ctx)?;
        write!(w, " %{}(", self.name)?;
        self.args.write_with_delim(w, ", ", ctx)?;
        write!(w, ")")?;

        match self.ret_tys.as_slice() {
            [] => {}
            [ret_ty] => {
                write!(w, " -> ")?;
                ret_ty.write(w, ctx)?;
            }
            ret_tys => {
                write!(w, " -> (")?;
                ret_tys.write_with_delim(w, ", ", ctx)?;
                write!(w, ")")?;
            }
        }

        Ok(())
    }
}
