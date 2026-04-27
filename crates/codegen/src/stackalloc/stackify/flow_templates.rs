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
        BlockTemplate, TransferOrder, canonical_transfer_order, choose_transfer, project_transfer,
        seed_block_templates,
    },
};

type EdgeCandMap = BTreeMap<(BlockId, BlockId), TransferOrder>;

#[derive(Clone, Debug, Default)]
struct LayoutState {
    transfer: TransferOrder,
    pinned: bool,
}

struct FlowTemplateSolver<'a, 'ctx> {
    ctx: &'a StackifyContext<'ctx>,
    spill: SpillSet<'a>,
    spill_obj: &'a SecondaryMap<ValueId, Option<crate::isa::evm::static_arena_alloc::StackObjId>>,
    slots: &'a mut SpillSlotPools,
    spill_requests: &'a mut BitSet<ValueId>,
    params_map: &'a SecondaryMap<BlockId, SmallVec<[ValueId; 4]>>,
    carry_in: &'a SecondaryMap<BlockId, BitSet<ValueId>>,
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
    spill_requests: &mut BitSet<ValueId>,
) -> SecondaryMap<BlockId, BlockTemplate> {
    let seed = seed_block_templates(ctx, spill);
    let params_map = seed.params_map;
    let carry_in = seed.carry_in;
    let mut state: SecondaryMap<BlockId, LayoutState> = SecondaryMap::new();

    for block in ctx.func.layout.iter_block() {
        state[block] = LayoutState {
            transfer: seed.templates[block].transfer.clone(),
            pinned: false,
        };
    }

    let mut edge_cand: EdgeCandMap = EdgeCandMap::new();

    let mut scratch_slots = SpillSlotPools::default();

    let mut solver = FlowTemplateSolver {
        ctx,
        spill: SpillSet::new(spill.bitset()),
        spill_obj,
        slots: &mut scratch_slots,
        spill_requests,
        params_map: &params_map,
        carry_in: &carry_in,
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
        let params = params_map[block].clone();
        let transfer = if ctx.scc.is_reachable(block) {
            state[block].transfer.clone()
        } else {
            canonical_transfer_order(&carry_in[block], &ctx.dom_depth, &ctx.def_info)
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
            params: self.params_map[block].clone(),
            transfer: (&*self.state)[block].transfer.clone(),
        }
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
                self.state[block].transfer = choose_transfer_from_preds(
                    ctx,
                    block,
                    self.carry_in,
                    &*self.edge_cand,
                    None,
                    None,
                );
                let tmpl = self.template_for(block);
                self.simulate_block_and_record_edges(block, &tmpl);
            }
            return;
        }

        self.seed_cyclic_scc(scc);

        const MAX_ITER: u32 = 32;
        let mut budget = MAX_ITER as usize * data.blocks_rpo.len();
        let mut queue = VecDeque::<BlockId>::new();
        let mut in_queue = BitSet::<BlockId>::default();

        for &block in &data.blocks_rpo {
            let tmpl = self.template_for(block);
            self.simulate_block_and_record_edges(block, &tmpl);
            budget = budget.saturating_sub(1);
        }

        if let Some(header) = self.maybe_pin_header(scc) {
            enqueue_block(&mut queue, &mut in_queue, header);
        }
        for &block in &data.blocks_rpo {
            if self.recompute_block_transfer(scc, block) {
                enqueue_block(&mut queue, &mut in_queue, block);
            }
        }

        while let Some(block) = queue.pop_front() {
            in_queue.remove(block);
            if budget == 0 {
                self.finalize_cyclic_scc(scc);
                return;
            }

            let tmpl = self.template_for(block);
            let changed_succs = self.simulate_block_and_record_edges(block, &tmpl);
            budget -= 1;

            if let Some(header) = data.header()
                && changed_succs.contains(&header)
                && let Some(header) = self.maybe_pin_header(scc)
            {
                enqueue_block(&mut queue, &mut in_queue, header);
            }

            for succ in changed_succs {
                if ctx.scc.scc_of(succ) == Some(scc) && self.recompute_block_transfer(scc, succ) {
                    enqueue_block(&mut queue, &mut in_queue, succ);
                }
            }
        }
    }

    fn seed_cyclic_scc(&mut self, scc: SccId) {
        let ctx = self.ctx;
        let carry_in = self.carry_in;
        let edge_cand = &*self.edge_cand;

        let data = ctx.scc.scc_data(scc);
        for &block in &data.blocks_rpo {
            self.state[block].pinned = false;
            if block == ctx.entry {
                self.state[block].transfer =
                    canonical_transfer_order(&carry_in[block], &ctx.dom_depth, &ctx.def_info);
                continue;
            }

            let external: Vec<(BlockId, &TransferOrder)> = reachable_preds(ctx, block)
                .filter(|pred| ctx.scc.scc_of(*pred) != Some(scc))
                .map(|pred| (pred, edge_candidate(edge_cand, pred, block)))
                .collect();

            if data.entry_blocks.contains(&block) && !external.is_empty() {
                self.state[block].transfer = choose_transfer(ctx, block, &external);
            } else {
                self.state[block].transfer =
                    canonical_transfer_order(&carry_in[block], &ctx.dom_depth, &ctx.def_info);
            }
        }
    }

    fn maybe_pin_header(&mut self, scc: SccId) -> Option<BlockId> {
        let ctx = self.ctx;
        let header = ctx.scc.scc_data(scc).header()?;
        if header == ctx.entry || self.state[header].pinned {
            return None;
        }

        let backedge_cand = best_backedge_candidate(ctx, scc, header, &*self.edge_cand)?;
        if !header_has_conflict(ctx, header, &*self.edge_cand) {
            return None;
        }

        let changed = self.state[header].transfer != backedge_cand;
        self.state[header].transfer = backedge_cand;
        self.state[header].pinned = true;
        changed.then_some(header)
    }

    fn recompute_block_transfer(&mut self, scc: SccId, block: BlockId) -> bool {
        if self.state[block].pinned {
            return false;
        }

        let fallback = self.state[block].transfer.clone();
        let transfer = choose_transfer_from_preds(
            self.ctx,
            block,
            self.carry_in,
            &*self.edge_cand,
            Some(scc),
            Some(&fallback),
        );
        if transfer == fallback {
            return false;
        }

        self.state[block].transfer = transfer;
        true
    }

    fn finalize_cyclic_scc(&mut self, scc: SccId) {
        let ctx = self.ctx;
        for &block in &ctx.scc.scc_data(scc).blocks_rpo {
            if self.state[block].pinned {
                continue;
            }
            let fallback = self.state[block].transfer.clone();
            let cand = choose_transfer_from_preds(
                ctx,
                block,
                self.carry_in,
                &*self.edge_cand,
                Some(scc),
                Some(&fallback),
            );
            self.state[block].transfer = if cand.is_empty() {
                canonical_transfer_order(&self.carry_in[block], &ctx.dom_depth, &ctx.def_info)
            } else {
                cand
            };
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
            project_transfer(&stack, &self.carry_in[dest]),
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
            project_transfer(&stack, &self.carry_in[succ]),
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
            project_transfer(&stack, &self.carry_in[succ]),
        );
    }
}

fn enqueue_block(queue: &mut VecDeque<BlockId>, in_queue: &mut BitSet<BlockId>, block: BlockId) {
    if in_queue.insert(block) {
        queue.push_back(block);
    }
}

fn edge_candidate(edge_cand: &EdgeCandMap, pred: BlockId, succ: BlockId) -> &TransferOrder {
    edge_cand
        .get(&(pred, succ))
        .unwrap_or_else(|| panic!("missing edge candidate for {pred:?}->{succ:?}"))
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

fn choose_transfer_from_preds(
    ctx: &StackifyContext<'_>,
    block: BlockId,
    carry_in: &SecondaryMap<BlockId, BitSet<ValueId>>,
    edge_cand: &EdgeCandMap,
    scc: Option<SccId>,
    fallback: Option<&TransferOrder>,
) -> TransferOrder {
    if block == ctx.entry {
        return canonical_transfer_order(&carry_in[block], &ctx.dom_depth, &ctx.def_info);
    }

    let mut all: Vec<(BlockId, &TransferOrder)> = Vec::new();
    let mut external: Vec<(BlockId, &TransferOrder)> = Vec::new();

    for pred in reachable_preds(ctx, block) {
        let cand = edge_candidate(edge_cand, pred, block);
        all.push((pred, cand));
        if let Some(scc) = scc
            && ctx.scc.scc_of(pred) != Some(scc)
        {
            external.push((pred, cand));
        }
    }

    if all.is_empty() {
        return fallback.cloned().unwrap_or_else(|| {
            canonical_transfer_order(&carry_in[block], &ctx.dom_depth, &ctx.def_info)
        });
    }

    if let Some(scc) = scc {
        let data = ctx.scc.scc_data(scc);
        if data.is_multi_entry() && data.entry_blocks.contains(&block) && !external.is_empty() {
            return choose_transfer(ctx, block, &external);
        }
    }

    choose_transfer(ctx, block, &all)
}

fn best_backedge_candidate(
    ctx: &StackifyContext<'_>,
    scc: SccId,
    block: BlockId,
    edge_cand: &EdgeCandMap,
) -> Option<TransferOrder> {
    reachable_preds(ctx, block)
        .filter(|pred| ctx.scc.scc_of(*pred) == Some(scc) && ctx.dom.dominates(block, *pred))
        .min_by_key(|pred| pred.as_u32())
        .map(|pred| edge_candidate(edge_cand, pred, block).clone())
}

fn header_has_conflict(ctx: &StackifyContext<'_>, block: BlockId, edge_cand: &EdgeCandMap) -> bool {
    let mut first: Option<&TransferOrder> = None;
    for pred in reachable_preds(ctx, block) {
        let cand = edge_candidate(edge_cand, pred, block);
        match first {
            None => first = Some(cand),
            Some(first_cand) if first_cand != cand => return true,
            Some(_) => {}
        }
    }
    false
}
