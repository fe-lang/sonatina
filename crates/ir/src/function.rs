use std::io;

use smallvec::SmallVec;

use super::{
    BlockId, DataFlowGraph, DebugInstBundle, DebugLocId, DebugMetadata, DebugTagId, InstId, Layout,
    Type, ValueId,
};
use crate::{InstSetBase, Linkage, ir_writer::IrWrite, module::ModuleCtx};

#[derive(Clone)]
pub struct Function {
    pub arg_values: smallvec::SmallVec<[ValueId; 8]>,
    pub dfg: DataFlowGraph,
    pub layout: Layout,
    pub debug: DebugMetadata,
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
            debug: DebugMetadata::default(),
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
        self.debug.clear_inst_debug(inst);
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
            self.debug.clear_inst_debug(inst);
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
    /// Call this after passes that may leave stale user entries.
    pub fn rebuild_users(&mut self) {
        self.dfg.clear_users();
        let insts: Vec<_> = self.dfg.inst_ids().collect();
        for inst in insts {
            self.dfg.attach_user(inst);
        }
    }

    pub fn set_inst_debug_loc(&mut self, inst: InstId, loc: DebugLocId) {
        debug_assert!(self.dfg.has_inst_slot(inst));
        self.debug.set_inst_debug_loc(inst, loc);
    }

    pub fn clear_inst_debug_loc(&mut self, inst: InstId) {
        self.debug.clear_inst_debug_loc(inst);
    }

    pub fn inst_debug_loc(&self, inst: InstId) -> Option<DebugLocId> {
        self.debug.inst_debug_loc(inst)
    }

    pub fn add_inst_debug_tag(&mut self, inst: InstId, tag: DebugTagId) {
        debug_assert!(self.dfg.has_inst_slot(inst));
        self.debug.add_inst_debug_tag(inst, tag);
    }

    pub fn inst_debug_tags(&self, inst: InstId) -> &[DebugTagId] {
        self.debug.inst_debug_tags(inst)
    }

    pub fn copy_inst_debug(&mut self, from: InstId, to: InstId) {
        debug_assert!(self.dfg.has_inst_slot(from));
        debug_assert!(self.dfg.has_inst_slot(to));
        self.debug.copy_inst_debug(from, to);
    }

    pub fn inst_debug_bundle(&self, inst: InstId) -> DebugInstBundle {
        self.debug.inst_debug_bundle(inst)
    }

    pub fn apply_inst_debug_bundle(
        &mut self,
        inst: InstId,
        bundle: &DebugInstBundle,
        appended_tag: Option<DebugTagId>,
    ) {
        debug_assert!(self.dfg.has_inst_slot(inst));
        self.debug
            .apply_inst_debug_bundle(inst, bundle, appended_tag);
    }

    pub fn import_inst_debug_from(
        &mut self,
        source: &Function,
        from: InstId,
        to: InstId,
        appended_tag: Option<DebugTagId>,
    ) {
        let bundle = source.inst_debug_bundle(from);
        self.apply_inst_debug_bundle(to, &bundle, appended_tag);
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
        DebugConfidence, DebugLoc, DebugTag, DebugTagKind, DebugTagPayload, FrontendOriginKind,
        FrontendOriginRecord, Immediate, Linkage, Signature, Type,
        builder::test_util::test_module_builder, func_cursor::InstInserter, inst::arith::Add,
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

    #[test]
    fn debug_handles_preserve_opaque_frontend_origin() {
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
        let inst = builder.func.dfg.value_inst(produced).unwrap();

        let origin = builder
            .func
            .debug
            .add_frontend_origin(FrontendOriginRecord {
                external_key: Some("fake-dsl://module::expr@7".to_string()),
                source_span: None,
                display_label: Some("fake DSL add".to_string()),
                kind: FrontendOriginKind::SourceExpr,
            });
        let loc = builder.func.debug.add_debug_loc(DebugLoc {
            primary_origin: Some(origin),
            source_span: None,
            confidence: DebugConfidence::Exact,
        });
        let tag = builder.func.debug.add_debug_tag(DebugTag {
            kind: DebugTagKind::FrontendLabel,
            origin: Some(origin),
            payload: DebugTagPayload::Text("non-fe frontend".to_string()),
        });

        builder.func.set_inst_debug_loc(inst, loc);
        builder.func.add_inst_debug_tag(inst, tag);

        assert_eq!(builder.func.inst_debug_loc(inst), Some(loc));
        assert_eq!(builder.func.inst_debug_tags(inst), &[tag]);

        let stored = builder.func.debug.frontend_origin(origin).unwrap();
        assert_eq!(
            stored.external_key.as_deref(),
            Some("fake-dsl://module::expr@7")
        );
        assert_eq!(stored.kind, FrontendOriginKind::SourceExpr);
    }

    #[test]
    fn instructions_without_debug_metadata_do_not_inherit_handles() {
        let mb = test_module_builder();
        let sig = Signature::new_unit("test_func", Linkage::Public, &[]);
        let func_ref = mb.declare_function(sig).unwrap();

        let mut builder = mb.func_builder::<InstInserter>(func_ref);
        let entry = builder.append_block();
        builder.switch_to_block(entry);

        let lhs = builder.make_imm_value(Immediate::I32(1));
        let rhs = builder.make_imm_value(Immediate::I32(2));
        let has_add = builder.inst_set().has_add().unwrap();

        let first = builder.insert_inst(Add::new(has_add, lhs, rhs), Type::I32);
        let first_inst = builder.func.dfg.value_inst(first).unwrap();
        let second = builder.insert_inst(Add::new(has_add, first, lhs), Type::I32);
        let second_inst = builder.func.dfg.value_inst(second).unwrap();

        let origin = builder
            .func
            .debug
            .add_frontend_origin(FrontendOriginRecord {
                external_key: Some("opaque://origin".to_string()),
                source_span: None,
                display_label: None,
                kind: FrontendOriginKind::Unknown,
            });
        let loc = builder.func.debug.add_debug_loc(DebugLoc {
            primary_origin: Some(origin),
            source_span: None,
            confidence: DebugConfidence::Conservative,
        });
        builder.func.set_inst_debug_loc(first_inst, loc);

        assert_eq!(builder.func.inst_debug_loc(first_inst), Some(loc));
        assert_eq!(builder.func.inst_debug_loc(second_inst), None);
        assert!(builder.func.inst_debug_tags(second_inst).is_empty());
    }

    #[test]
    fn imported_debug_bundle_remaps_origin_records_and_appends_callsite_tag() {
        let mb = test_module_builder();
        let source_ref = mb
            .declare_function(Signature::new_unit("source", Linkage::Private, &[]))
            .unwrap();
        let target_ref = mb
            .declare_function(Signature::new_unit("target", Linkage::Private, &[]))
            .unwrap();

        let mut source = mb.func_builder::<InstInserter>(source_ref);
        let source_block = source.append_block();
        source.switch_to_block(source_block);
        let lhs = source.make_imm_value(Immediate::I32(1));
        let rhs = source.make_imm_value(Immediate::I32(2));
        let has_add = source.inst_set().has_add().unwrap();
        let source_value = source.insert_inst(Add::new(has_add, lhs, rhs), Type::I32);
        let source_inst = source.func.dfg.value_inst(source_value).unwrap();

        let origin = source.func.debug.add_frontend_origin(FrontendOriginRecord {
            external_key: Some("source-frontend://expr/1".to_string()),
            source_span: None,
            display_label: Some("source add".to_string()),
            kind: FrontendOriginKind::SourceExpr,
        });
        let loc = source.func.debug.add_debug_loc(DebugLoc {
            primary_origin: Some(origin),
            source_span: None,
            confidence: DebugConfidence::Exact,
        });
        let source_tag = source.func.debug.add_debug_tag(DebugTag {
            kind: DebugTagKind::FrontendLabel,
            origin: Some(origin),
            payload: DebugTagPayload::Text("callee label".to_string()),
        });
        source.func.set_inst_debug_loc(source_inst, loc);
        source.func.add_inst_debug_tag(source_inst, source_tag);

        let mut target = mb.func_builder::<InstInserter>(target_ref);
        let target_block = target.append_block();
        target.switch_to_block(target_block);
        let lhs = target.make_imm_value(Immediate::I32(3));
        let rhs = target.make_imm_value(Immediate::I32(4));
        let has_add = target.inst_set().has_add().unwrap();
        let target_value = target.insert_inst(Add::new(has_add, lhs, rhs), Type::I32);
        let target_inst = target.func.dfg.value_inst(target_value).unwrap();

        let callsite_tag = target.func.debug.add_debug_tag(DebugTag {
            kind: DebugTagKind::InlineCallsite,
            origin: None,
            payload: DebugTagPayload::Text("callsite target->source".to_string()),
        });
        target.func.import_inst_debug_from(
            &source.func,
            source_inst,
            target_inst,
            Some(callsite_tag),
        );

        let imported_loc = target.func.inst_debug_loc(target_inst).unwrap();
        let imported_origin = target
            .func
            .debug
            .debug_loc(imported_loc)
            .unwrap()
            .primary_origin
            .unwrap();
        let imported_record = target.func.debug.frontend_origin(imported_origin).unwrap();
        assert_eq!(
            imported_record.external_key.as_deref(),
            Some("source-frontend://expr/1")
        );

        let tags = target.func.inst_debug_tags(target_inst);
        assert_eq!(tags.len(), 2);
        assert_eq!(
            target.func.debug.debug_tag(tags[0]).unwrap().kind,
            DebugTagKind::FrontendLabel
        );
        assert_eq!(
            target.func.debug.debug_tag(tags[1]).unwrap().kind,
            DebugTagKind::InlineCallsite
        );
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
