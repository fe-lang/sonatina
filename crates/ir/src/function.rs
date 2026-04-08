use std::io;

use smallvec::SmallVec;

use super::{BlockId, DataFlowGraph, InstId, Layout, Type, ValueId};
use crate::{InstSetBase, Linkage, ir_writer::IrWrite, module::ModuleCtx};

#[derive(Clone)]
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
        // Some transformations detach instructions without keeping `dfg.users` up-to-date.
        // Rebuild on-demand so deletion does not spuriously panic on stale users.
        if inst_results_have_stale_users(self, &[inst]) {
            self.rebuild_users();
        }
        self.dfg.delete_inst(inst);
    }

    pub fn erase_insts(&mut self, insts: &[InstId]) {
        for &inst in insts {
            assert!(self.layout.has_inst_slot(inst));
            assert!(
                !self.layout.is_inst_inserted(inst),
                "instruction {inst:?} must be detached before erase"
            );
        }

        if inst_results_have_stale_users(self, insts) {
            self.rebuild_users();
        }

        for &inst in insts {
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

    /// Recompute `dfg.users` from scratch using all live DFG instructions.
    ///
    /// Call this after passes that may leave stale user entries (e.g. egraph).
    pub fn rebuild_users(&mut self) {
        self.dfg.clear_users();
        let insts: Vec<_> = self.dfg.inst_ids().collect();
        for inst in insts {
            self.dfg.attach_user(inst);
        }
    }
}

fn inst_results_have_stale_users(func: &Function, insts: &[InstId]) -> bool {
    fn inst_uses_value(func: &Function, user: InstId, value: ValueId) -> bool {
        let mut uses = false;
        func.dfg.inst(user).for_each_value(&mut |v| {
            uses |= v == value;
        });
        uses
    }

    insts.iter().copied().any(|inst| {
        func.dfg.inst_results(inst).iter().copied().any(|value| {
            func.dfg
                .users(value)
                .copied()
                .any(|user| !func.dfg.has_inst(user) || !inst_uses_value(func, user, value))
        })
    })
}

#[cfg(test)]
mod tests {
    use crate::{
        Immediate, Linkage, Signature, Type, builder::test_util::test_module_builder,
        func_cursor::InstInserter, inst::arith::Add,
    };

    #[test]
    fn erase_inst_rebuilds_stale_users_from_mutated_instructions() {
        let mb = test_module_builder();
        let sig = Signature::new_unit("test_func", Linkage::Public, &[]);
        let func_ref = mb.declare_function(sig).unwrap();

        let mut builder = mb.func_builder::<InstInserter>(func_ref);
        let entry = builder.append_block();
        builder.switch_to_block(entry);

        let lhs = builder.make_imm_value(Immediate::I32(1));
        let rhs = builder.make_imm_value(Immediate::I32(2));
        let has_add = builder.inst_set().has_add().unwrap();

        let produced = builder.insert_inst(Add::new(has_add, lhs, rhs), Type::I32);
        let producer_inst = builder.func.dfg.value_inst(produced).unwrap();

        let consumed = builder.insert_inst(Add::new(has_add, produced, lhs), Type::I32);
        let consumer_inst = builder.func.dfg.value_inst(consumed).unwrap();

        builder.insert_return_unit();
        builder.seal_all();

        // Rewrite the consumer to stop using the producer without repairing `dfg.users`.
        builder
            .func
            .dfg
            .inst_mut(consumer_inst)
            .for_each_value_mut(&mut |value| {
                if *value == produced {
                    *value = lhs;
                }
            });

        builder.func.layout.remove_inst(producer_inst);

        // Previously this would panic in `DataFlowGraph::delete_inst` because the producer result
        // still had a stale tracked user entry for the mutated consumer.
        builder.func.erase_inst(producer_inst);

        assert!(!builder.func.dfg.has_inst(producer_inst));
    }

    #[test]
    #[should_panic(expected = "with live result users")]
    fn erase_inst_keeps_detached_live_users_tracked() {
        let mb = test_module_builder();
        let sig = Signature::new_unit("test_func", Linkage::Public, &[]);
        let func_ref = mb.declare_function(sig).unwrap();

        let mut builder = mb.func_builder::<InstInserter>(func_ref);
        let entry = builder.append_block();
        builder.switch_to_block(entry);

        let lhs = builder.make_imm_value(Immediate::I32(1));
        let rhs = builder.make_imm_value(Immediate::I32(2));
        let has_add = builder.inst_set().has_add().unwrap();

        let produced = builder.insert_inst(Add::new(has_add, lhs, rhs), Type::I32);
        let producer_inst = builder.func.dfg.value_inst(produced).unwrap();

        let consumed = builder.insert_inst(Add::new(has_add, produced, lhs), Type::I32);
        let consumer_inst = builder.func.dfg.value_inst(consumed).unwrap();

        builder.insert_return_unit();
        builder.seal_all();

        builder.func.layout.remove_inst(consumer_inst);
        builder.func.layout.remove_inst(producer_inst);

        builder.func.erase_inst(producer_inst);
    }

    #[test]
    fn erase_insts_untracks_batch_before_delete() {
        let mb = test_module_builder();
        let sig = Signature::new_unit("test_func", Linkage::Public, &[]);
        let func_ref = mb.declare_function(sig).unwrap();

        let mut builder = mb.func_builder::<InstInserter>(func_ref);
        let entry = builder.append_block();
        builder.switch_to_block(entry);

        let lhs = builder.make_imm_value(Immediate::I32(1));
        let rhs = builder.make_imm_value(Immediate::I32(2));
        let has_add = builder.inst_set().has_add().unwrap();

        let produced = builder.insert_inst(Add::new(has_add, lhs, rhs), Type::I32);
        let producer_inst = builder.func.dfg.value_inst(produced).unwrap();

        let consumed = builder.insert_inst(Add::new(has_add, produced, lhs), Type::I32);
        let consumer_inst = builder.func.dfg.value_inst(consumed).unwrap();

        builder.insert_return_unit();
        builder.seal_all();

        builder.func.layout.remove_inst(consumer_inst);
        builder.func.layout.remove_inst(producer_inst);
        builder.func.erase_insts(&[producer_inst, consumer_inst]);

        assert!(!builder.func.dfg.has_inst(producer_inst));
        assert!(!builder.func.dfg.has_inst(consumer_inst));
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
