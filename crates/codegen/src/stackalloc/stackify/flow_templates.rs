use std::collections::{BTreeMap, VecDeque};

use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, InstId, ValueId};

use crate::{
    bitset::BitSet,
    cfg_scc::SccId,
    stackalloc::{Actions, stackify::planner::MemPlan},
};

use super::{
    block_sim::{BlockSimMode, BlockSimState, BrTableEdgeKind, PlannerActionSink, run_block_sim},
    builder::StackifyContext,
    planner::{NormalizeSearchScratch, OperandPrepMode, OperandPrepMode::TemplateSim, Planner},
    slots::{FreeSlotPools, SpillSlotPools},
    spill::SpillSet,
    sym_stack::SymStack,
    templates::{
        BlockInterfaces, BlockTemplate, TransferOrder, canonical_transfer_order, choose_transfer,
        project_transfer,
    },
};

type EdgeCandMap = BTreeMap<(BlockId, BlockId), TransferOrder>;

#[derive(Clone, Debug, Default)]
struct LayoutState {
    transfer: Option<TransferOrder>,
}

struct FlowTemplateSolver<'a, 'ctx> {
    ctx: &'a StackifyContext<'ctx>,
    spill: SpillSet<'a>,
    spill_obj: &'a SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>>,
    slots: &'a mut SpillSlotPools,
    spill_requests: &'a mut BitSet<ValueId>,
    interfaces: &'a BlockInterfaces,
    state: &'a mut SecondaryMap<BlockId, LayoutState>,
    edge_cand: &'a mut EdgeCandMap,
    actions: Actions,
    changed_succs: SmallVec<[BlockId; 4]>,
    search_scratch: NormalizeSearchScratch,
}

pub(super) fn solve_templates_from_flow(
    ctx: &StackifyContext<'_>,
    spill: SpillSet<'_>,
    spill_obj: &SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>>,
    interfaces: &BlockInterfaces,
    spill_requests: &mut BitSet<ValueId>,
) -> SecondaryMap<BlockId, BlockTemplate> {
    let mut state: SecondaryMap<BlockId, LayoutState> = SecondaryMap::new();

    for block in ctx.func.layout.iter_block() {
        state[block] = LayoutState::default();
    }

    let mut edge_cand: EdgeCandMap = EdgeCandMap::new();

    let mut scratch_slots = SpillSlotPools::default();

    let mut solver = FlowTemplateSolver {
        ctx,
        spill: SpillSet::new(spill.bitset()),
        spill_obj,
        slots: &mut scratch_slots,
        spill_requests,
        interfaces,
        state: &mut state,
        edge_cand: &mut edge_cand,
        actions: Actions::new(),
        changed_succs: SmallVec::new(),
        search_scratch: NormalizeSearchScratch::default(),
    };

    for &scc in ctx.scc.topo_order() {
        solver.solve_scc(scc);
    }

    let mut templates: SecondaryMap<BlockId, BlockTemplate> = SecondaryMap::new();
    for block in ctx.func.layout.iter_block() {
        let params = interfaces.params[block].clone();
        let transfer = if ctx.scc.is_reachable(block) {
            state[block].transfer.clone().unwrap_or_else(|| {
                canonical_transfer_order(&interfaces.carry_in[block], &ctx.dom_depth, &ctx.def_info)
            })
        } else {
            TransferOrder::new()
        };
        templates[block] = BlockTemplate { params, transfer };
    }

    templates
}

fn record_edge_candidate(
    edge_cand: &mut EdgeCandMap,
    changed_succs: &mut SmallVec<[BlockId; 4]>,
    pred: BlockId,
    succ: BlockId,
    transfer: TransferOrder,
) {
    if edge_cand.get(&(pred, succ)) != Some(&transfer) {
        edge_cand.insert((pred, succ), transfer);
        if !changed_succs.contains(&succ) {
            changed_succs.push(succ);
        }
    }
}

impl<'a, 'ctx> FlowTemplateSolver<'a, 'ctx> {
    fn template_for(&self, block: BlockId) -> BlockTemplate {
        BlockTemplate {
            params: self.interfaces.params[block].clone(),
            transfer: (&*self.state)[block]
                .transfer
                .clone()
                .unwrap_or_else(|| panic!("missing stack template for {block:?}")),
        }
    }

    fn set_transfer(&mut self, block: BlockId, transfer: TransferOrder) -> bool {
        if (&*self.state)[block].transfer.as_ref() == Some(&transfer) {
            return false;
        }
        self.state[block].transfer = Some(transfer);
        true
    }

    fn simulate_block_and_record_edges(
        &mut self,
        block: BlockId,
        template: &BlockTemplate,
    ) -> SmallVec<[BlockId; 4]> {
        self.actions.clear();
        self.changed_succs.clear();
        let stack = SymStack::from_template(template, self.ctx.has_internal_return);
        let state = BlockSimState::new(
            self.ctx,
            block,
            stack,
            FreeSlotPools::default(),
            Actions::new(),
        );
        run_block_sim(self, state);
        std::mem::take(&mut self.changed_succs)
    }

    fn solve_scc(&mut self, scc: SccId) {
        let ctx = self.ctx;
        let data = ctx.scc.scc_data(scc);

        if !data.is_cycle {
            for &block in &data.blocks_rpo {
                let transfer = choose_transfer_from_available_preds(ctx, block, &*self.edge_cand)
                    .unwrap_or_else(|| {
                        panic!("missing predecessor stack layout for acyclic block {block:?}")
                    });
                self.set_transfer(block, transfer);
                let tmpl = self.template_for(block);
                self.simulate_block_and_record_edges(block, &tmpl);
            }
            return;
        }

        const MAX_ITER: u32 = 32;
        let mut budget = MAX_ITER as usize * data.blocks_rpo.len();
        let mut queue = VecDeque::<BlockId>::new();
        let mut in_queue = BitSet::<BlockId>::default();

        self.seed_cyclic_entries(scc, &mut queue, &mut in_queue);

        while let Some(block) = queue.pop_front() {
            in_queue.remove(block);
            if budget == 0 {
                self.finalize_cyclic_scc(scc);
                return;
            }

            let tmpl = self.template_for(block);
            let changed_succs = self.simulate_block_and_record_edges(block, &tmpl);
            budget -= 1;

            for succ in changed_succs {
                if ctx.scc.scc_of(succ) == Some(scc) && self.recompute_block_transfer(scc, succ) {
                    enqueue_block(&mut queue, &mut in_queue, succ);
                }
            }
        }
    }

    fn seed_cyclic_entries(
        &mut self,
        scc: SccId,
        queue: &mut VecDeque<BlockId>,
        in_queue: &mut BitSet<BlockId>,
    ) {
        let ctx = self.ctx;
        for &block in &ctx.scc.scc_data(scc).entry_blocks {
            let transfer = if block == ctx.entry {
                Some(TransferOrder::new())
            } else {
                choose_external_transfer(ctx, block, scc, &*self.edge_cand)
            };
            if let Some(transfer) = transfer
                && self.set_transfer(block, transfer)
            {
                enqueue_block(queue, in_queue, block);
            }
        }
    }

    fn recompute_block_transfer(&mut self, scc: SccId, block: BlockId) -> bool {
        let transfer = if self.ctx.scc.scc_data(scc).entry_blocks.contains(&block) {
            choose_external_transfer(self.ctx, block, scc, &*self.edge_cand)
        } else {
            None
        }
        .or_else(|| choose_transfer_from_available_preds(self.ctx, block, &*self.edge_cand));

        transfer.is_some_and(|transfer| self.set_transfer(block, transfer))
    }

    fn finalize_cyclic_scc(&mut self, scc: SccId) {
        let ctx = self.ctx;
        for &block in &ctx.scc.scc_data(scc).blocks_rpo {
            let transfer = if ctx.scc.scc_data(scc).entry_blocks.contains(&block) {
                choose_external_transfer(ctx, block, scc, &*self.edge_cand)
            } else {
                None
            }
            .or_else(|| choose_transfer_from_available_preds(ctx, block, &*self.edge_cand))
            .or_else(|| self.state[block].transfer.clone())
            .unwrap_or_else(|| {
                canonical_transfer_order(
                    &self.interfaces.carry_in[block],
                    &ctx.dom_depth,
                    &ctx.def_info,
                )
            });
            self.state[block].transfer = Some(transfer);
        }
    }
}

impl<'a, 'ctx> BlockSimMode<'ctx> for FlowTemplateSolver<'a, 'ctx> {
    fn ctx(&self) -> &StackifyContext<'ctx> {
        self.ctx
    }

    fn operand_prep_mode(&self) -> OperandPrepMode {
        TemplateSim
    }

    fn call_uses_stack_continuation(&self, _inst: InstId) -> bool {
        true
    }

    fn scratch_slots(&self) -> &super::slots::SlotPool {
        &self.slots.scratch
    }

    fn clear_inst_actions(&mut self, _inst: InstId) {
        self.actions.clear();
    }

    fn pre_actions_len(&self, _inst: InstId) -> usize {
        self.actions.len()
    }

    fn with_pre_actions<R>(&mut self, _inst: InstId, f: impl FnOnce(&mut Actions) -> R) -> R {
        f(&mut self.actions)
    }

    fn with_planner<R>(
        &mut self,
        stack: &mut SymStack,
        free_slots: &mut FreeSlotPools,
        sink: PlannerActionSink<'_>,
        f: impl FnOnce(&mut Planner<'_, '_>) -> R,
    ) -> R {
        let ctx = self.ctx;
        let mut case_actions;
        let actions = match sink {
            PlannerActionSink::BrTableCase { .. } => {
                case_actions = Actions::new();
                &mut case_actions
            }
            PlannerActionSink::Pre(_) | PlannerActionSink::Post(_) => &mut self.actions,
        };
        let mem = MemPlan::new(
            self.spill,
            &mut *self.spill_requests,
            ctx,
            self.spill_obj,
            &ctx.exact_local_addr,
            free_slots,
            &mut *self.slots,
        );
        let mut planner = Planner::new(ctx, stack, actions, mem, &mut self.search_scratch);
        f(&mut planner)
    }

    fn on_jump(
        &mut self,
        state: &mut BlockSimState,
        _inst: InstId,
        dest: BlockId,
        stack: SymStack,
        _action_start: usize,
    ) {
        record_edge_candidate(
            self.edge_cand,
            &mut self.changed_succs,
            state.block,
            dest,
            project_transfer(&stack, &self.interfaces.carry_in[dest]),
        );
    }

    fn on_branch_edge(
        &mut self,
        state: &mut BlockSimState,
        _inst: InstId,
        succ: BlockId,
        stack: SymStack,
    ) {
        record_edge_candidate(
            self.edge_cand,
            &mut self.changed_succs,
            state.block,
            succ,
            project_transfer(&stack, &self.interfaces.carry_in[succ]),
        );
    }

    fn on_br_table_edge(
        &mut self,
        state: &mut BlockSimState,
        _inst: InstId,
        succ: BlockId,
        stack: SymStack,
        _kind: BrTableEdgeKind,
    ) {
        record_edge_candidate(
            self.edge_cand,
            &mut self.changed_succs,
            state.block,
            succ,
            project_transfer(&stack, &self.interfaces.carry_in[succ]),
        );
    }
}

fn enqueue_block(queue: &mut VecDeque<BlockId>, in_queue: &mut BitSet<BlockId>, block: BlockId) {
    if in_queue.insert(block) {
        queue.push_back(block);
    }
}

fn reachable_preds<'a>(
    ctx: &'a StackifyContext<'_>,
    block: BlockId,
) -> impl Iterator<Item = BlockId> + 'a {
    ctx.cfg
        .preds_of(block)
        .copied()
        .filter(move |pred| ctx.scc.is_reachable(*pred))
}

fn choose_transfer_from_available_preds(
    ctx: &StackifyContext<'_>,
    block: BlockId,
    edge_cand: &EdgeCandMap,
) -> Option<TransferOrder> {
    if block == ctx.entry {
        return Some(TransferOrder::new());
    }

    let candidates: Vec<(BlockId, &TransferOrder)> = reachable_preds(ctx, block)
        .filter_map(|pred| edge_cand.get(&(pred, block)).map(|cand| (pred, cand)))
        .collect();
    (!candidates.is_empty()).then(|| choose_transfer(ctx, block, &candidates))
}

fn choose_external_transfer(
    ctx: &StackifyContext<'_>,
    block: BlockId,
    scc: SccId,
    edge_cand: &EdgeCandMap,
) -> Option<TransferOrder> {
    let candidates: Vec<(BlockId, &TransferOrder)> = reachable_preds(ctx, block)
        .filter(|pred| ctx.scc.scc_of(*pred) != Some(scc))
        .filter_map(|pred| edge_cand.get(&(pred, block)).map(|cand| (pred, cand)))
        .collect();
    (!candidates.is_empty()).then(|| choose_transfer(ctx, block, &candidates))
}
