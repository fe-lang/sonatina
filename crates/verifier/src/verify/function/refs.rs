use sonatina_ir::{
    BlockId, GlobalVariableRef, Inst, Type, ValueId, module::FuncRef, visitor::Visitor,
};

#[derive(Default)]
pub(super) struct InstRefs {
    pub(super) values: Vec<ValueId>,
    pub(super) blocks: Vec<BlockId>,
    pub(super) funcs: Vec<FuncRef>,
    pub(super) globals: Vec<GlobalVariableRef>,
    pub(super) types: Vec<Type>,
}

pub(super) fn collect_inst_refs(inst: &dyn Inst) -> InstRefs {
    struct RefCollector<'a> {
        refs: &'a mut InstRefs,
    }

    impl Visitor for RefCollector<'_> {
        fn visit_value_id(&mut self, item: ValueId) {
            self.refs.values.push(item);
        }

        fn visit_block_id(&mut self, item: BlockId) {
            self.refs.blocks.push(item);
        }

        fn visit_func_ref(&mut self, item: FuncRef) {
            self.refs.funcs.push(item);
        }

        fn visit_gv_ref(&mut self, item: GlobalVariableRef) {
            self.refs.globals.push(item);
        }

        fn visit_ty(&mut self, item: &Type) {
            self.refs.types.push(*item);
        }
    }

    let mut refs = InstRefs::default();
    let mut collector = RefCollector { refs: &mut refs };
    inst.accept(&mut collector);
    refs
}
