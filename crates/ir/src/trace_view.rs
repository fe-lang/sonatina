use crate::{
    BlockId, DebugLocId, DebugTagId, Function, InstId, Module,
    inst::{
        InstClassKind,
        control_flow::{BranchInfo, BranchKind},
    },
    module::FuncRef,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CfgEdgeKind {
    Jump,
    Branch,
    BranchTable,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CfgEdge {
    pub from: BlockId,
    pub to: BlockId,
    pub terminator: InstId,
    pub ordinal: usize,
    pub kind: CfgEdgeKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InstKindView {
    pub opcode: &'static str,
    pub class: InstClassKind,
    pub terminator: bool,
}

pub trait SonatinaTraceView {
    fn trace_functions(&self) -> Vec<FuncRef>;
    fn trace_blocks(&self, func: FuncRef) -> Vec<BlockId>;
    fn trace_instructions(&self, func: FuncRef, block: BlockId) -> Vec<InstId>;
    fn trace_block_successors(&self, func: FuncRef, block: BlockId) -> Vec<CfgEdge>;
    fn trace_inst_debug_loc(&self, func: FuncRef, inst: InstId) -> Option<DebugLocId>;
    fn trace_inst_debug_tags(&self, func: FuncRef, inst: InstId) -> Vec<DebugTagId>;
    fn trace_inst_kind(&self, func: FuncRef, inst: InstId) -> Option<InstKindView>;
}

impl SonatinaTraceView for Module {
    fn trace_functions(&self) -> Vec<FuncRef> {
        self.funcs()
    }

    fn trace_blocks(&self, func: FuncRef) -> Vec<BlockId> {
        self.func_store
            .try_view(func, |func| func.layout.iter_block().collect())
            .unwrap_or_default()
    }

    fn trace_instructions(&self, func: FuncRef, block: BlockId) -> Vec<InstId> {
        self.func_store
            .try_view(func, |func| trace_instructions(func, block))
            .unwrap_or_default()
    }

    fn trace_block_successors(&self, func: FuncRef, block: BlockId) -> Vec<CfgEdge> {
        self.func_store
            .try_view(func, |func| trace_block_successors(func, block))
            .unwrap_or_default()
    }

    fn trace_inst_debug_loc(&self, func: FuncRef, inst: InstId) -> Option<DebugLocId> {
        self.func_store
            .try_view(func, |func| func.inst_debug_loc(inst))
            .flatten()
    }

    fn trace_inst_debug_tags(&self, func: FuncRef, inst: InstId) -> Vec<DebugTagId> {
        self.func_store
            .try_view(func, |func| func.inst_debug_tags(inst).to_vec())
            .unwrap_or_default()
    }

    fn trace_inst_kind(&self, func: FuncRef, inst: InstId) -> Option<InstKindView> {
        self.func_store.try_view(func, |func| {
            func.dfg.get_inst(inst).map(|inst| InstKindView {
                opcode: inst.as_text(),
                class: inst.kind(),
                terminator: inst.is_terminator(),
            })
        })?
    }
}

fn trace_instructions(func: &Function, block: BlockId) -> Vec<InstId> {
    if !func.layout.has_block_slot(block) || !func.layout.is_block_inserted(block) {
        return Vec::new();
    }

    func.layout.iter_inst(block).collect()
}

fn trace_block_successors(func: &Function, block: BlockId) -> Vec<CfgEdge> {
    let Some(Some(terminator)) = func.layout.try_last_inst_of(block) else {
        return Vec::new();
    };
    let Some(branch) = func.dfg.branch_info(terminator) else {
        return Vec::new();
    };

    let kind = cfg_edge_kind(branch);
    branch
        .dests()
        .into_iter()
        .enumerate()
        .map(|(ordinal, to)| CfgEdge {
            from: block,
            to,
            terminator,
            ordinal,
            kind,
        })
        .collect()
}

fn cfg_edge_kind(branch: &dyn BranchInfo) -> CfgEdgeKind {
    match branch.branch_kind() {
        BranchKind::Jump(_) => CfgEdgeKind::Jump,
        BranchKind::Br(_) => CfgEdgeKind::Branch,
        BranchKind::BrTable(_) => CfgEdgeKind::BranchTable,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        DebugConfidence, DebugLoc, FrontendOriginKind, FrontendOriginRecord, Linkage, Signature,
        Type,
        builder::test_util::{test_isa, test_module_builder},
        func_cursor::InstInserter,
        inst::{
            arith::Add,
            control_flow::{Br, Jump, Return},
        },
        isa::Isa,
    };

    use super::{CfgEdgeKind, InstKindView, SonatinaTraceView};

    #[test]
    fn trace_view_exposes_deterministic_cfg_and_instruction_membership() {
        let mb = test_module_builder();
        let sig = Signature::new_unit("trace_loop", Linkage::Public, &[Type::I1]);
        let func_ref = mb.declare_function(sig).unwrap();
        let evm = test_isa();
        let is = evm.inst_set();

        let mut builder = mb.func_builder::<InstInserter>(func_ref);
        let entry = builder.append_block();
        let header = builder.append_block();
        let body = builder.append_block();
        let exit = builder.append_block();
        let cond = builder.args()[0];

        builder.switch_to_block(entry);
        builder.insert_inst_no_result(Jump::new(is, header));

        builder.switch_to_block(header);
        builder.insert_inst_no_result(Br::new(is, cond, body, exit));

        builder.switch_to_block(body);
        let lhs = builder.make_imm_value(1i32);
        let rhs = builder.make_imm_value(2i32);
        let sum = builder.insert_inst(Add::new(is, lhs, rhs), Type::I32);
        let sum_inst = builder.func.dfg.value_inst(sum).unwrap();
        let origin = builder
            .func
            .debug
            .add_frontend_origin(FrontendOriginRecord {
                external_key: Some("dsl://loop-body/add".to_string()),
                source_span: None,
                display_label: None,
                kind: FrontendOriginKind::SourceExpr,
            });
        let loc = builder.func.debug.add_debug_loc(DebugLoc {
            primary_origin: Some(origin),
            source_span: None,
            confidence: DebugConfidence::Exact,
        });
        builder.func.set_inst_debug_loc(sum_inst, loc);
        builder.insert_inst_no_result(Jump::new(is, header));

        builder.switch_to_block(exit);
        builder.insert_inst_no_result(Return::new_unit(is));
        builder.seal_all();
        builder.finish();

        let module = mb.build();

        assert_eq!(module.trace_functions(), vec![func_ref]);
        assert_eq!(
            module.trace_blocks(func_ref),
            vec![entry, header, body, exit]
        );

        let entry_edges = module.trace_block_successors(func_ref, entry);
        assert_eq!(entry_edges.len(), 1);
        assert_eq!(entry_edges[0].from, entry);
        assert_eq!(entry_edges[0].to, header);
        assert_eq!(entry_edges[0].kind, CfgEdgeKind::Jump);
        assert_eq!(entry_edges[0].ordinal, 0);

        let header_edges = module.trace_block_successors(func_ref, header);
        assert_eq!(
            header_edges
                .iter()
                .map(|edge| (edge.to, edge.kind, edge.ordinal))
                .collect::<Vec<_>>(),
            vec![
                (body, CfgEdgeKind::Branch, 0),
                (exit, CfgEdgeKind::Branch, 1)
            ]
        );

        let body_edges = module.trace_block_successors(func_ref, body);
        assert_eq!(body_edges[0].to, header);
        assert_eq!(body_edges[0].kind, CfgEdgeKind::Jump);

        let body_insts = module.trace_instructions(func_ref, body);
        assert_eq!(body_insts.first().copied(), Some(sum_inst));
        assert_eq!(module.trace_inst_debug_loc(func_ref, sum_inst), Some(loc));

        assert_eq!(
            module.trace_inst_kind(func_ref, sum_inst),
            Some(InstKindView {
                opcode: "add",
                class: crate::inst::InstClassKind::Binary(crate::inst::BinaryInstKind::Add),
                terminator: false,
            })
        );
    }
}
