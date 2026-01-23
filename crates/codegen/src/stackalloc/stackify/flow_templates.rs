use std::{cmp::Ordering, collections::BTreeMap};

use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, ValueId, inst::control_flow::BranchKind};

use crate::{
    bitset::BitSet,
    cfg_scc::SccId,
    stackalloc::{Actions, stackify::planner::MemPlan},
};

use super::{
    builder::StackifyContext,
    iteration::{
        clean_dead_stack_prefix, count_block_uses, improve_reachability_before_operands,
        last_use_values_in_inst, operand_order_for_evm,
    },
    planner::{self, Planner},
    slots::{FreeSlotPools, SpillSlotPools},
    spill::SpillSet,
    sym_stack::{StackItem, SymStack},
    templates::{BlockTemplate, canonical_transfer_order, live_in_non_params},
};

type TransferOrder = SmallVec<[ValueId; 8]>;
type EdgeCandMap = BTreeMap<(BlockId, BlockId), TransferOrder>;

#[derive(Clone, Debug, Default)]
struct LayoutState {
    transfer: TransferOrder,
    pinned: bool,
}

struct FlowTemplateSolver<'a, 'ctx> {
    ctx: &'a StackifyContext<'ctx>,
    spill: SpillSet<'a>,
    slots: &'a mut SpillSlotPools,
    spill_requests: &'a mut BitSet<ValueId>,
    params_map: &'a SecondaryMap<BlockId, SmallVec<[ValueId; 4]>>,
    carry_in: &'a SecondaryMap<BlockId, BitSet<ValueId>>,
    state: &'a mut SecondaryMap<BlockId, LayoutState>,
    edge_cand: &'a mut EdgeCandMap,
}

pub(super) fn solve_templates_from_flow(
    ctx: &StackifyContext<'_>,
    spill: SpillSet<'_>,
    spill_requests: &mut BitSet<ValueId>,
) -> SecondaryMap<BlockId, BlockTemplate> {
    let mut params_map: SecondaryMap<BlockId, SmallVec<[ValueId; 4]>> = SecondaryMap::new();
    let mut carry_in: SecondaryMap<BlockId, BitSet<ValueId>> = SecondaryMap::new();
    let mut state: SecondaryMap<BlockId, LayoutState> = SecondaryMap::new();

    for block in ctx.func.layout.iter_block() {
        let mut params = SmallVec::<[ValueId; 4]>::new();
        if block == ctx.entry {
            params.extend(ctx.func.arg_values.iter().copied());
        }
        params.extend(ctx.phi_results[block].iter().copied());
        params_map[block] = params;

        let carry = live_in_non_params(
            ctx.liveness,
            ctx.func,
            block,
            ctx.entry,
            &ctx.phi_results,
            spill,
        );
        let transfer = canonical_transfer_order(&carry, &ctx.dom_depth, &ctx.def_info);
        carry_in[block] = carry;
        state[block] = LayoutState {
            transfer,
            pinned: false,
        };
    }

    let mut edge_cand: EdgeCandMap = EdgeCandMap::new();

    let mut scratch_slots = SpillSlotPools::default();

    let mut solver = FlowTemplateSolver {
        ctx,
        spill: SpillSet::new(spill.bitset()),
        slots: &mut scratch_slots,
        spill_requests,
        params_map: &params_map,
        carry_in: &carry_in,
        state: &mut state,
        edge_cand: &mut edge_cand,
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

fn choose_transfer(
    ctx: &StackifyContext<'_>,
    block: BlockId,
    candidates: &[(BlockId, &TransferOrder)],
) -> TransferOrder {
    debug_assert!(!candidates.is_empty());

    let first = candidates[0].1;
    if candidates.iter().all(|(_, cand)| *cand == first) {
        return first.clone();
    }

    if let Some((_pred, cand)) = candidates
        .iter()
        .filter(|(pred, _)| ctx.dom.dominates(block, *pred))
        .min_by_key(|(pred, _)| pred.as_u32())
    {
        return (*cand).clone();
    }

    candidates
        .iter()
        .min_by(|(a_pred, a), (b_pred, b)| {
            lex_cmp(a, b).then_with(|| a_pred.as_u32().cmp(&b_pred.as_u32()))
        })
        .map(|(_, cand)| (*cand).clone())
        .unwrap_or_default()
}

fn lex_cmp(a: &[ValueId], b: &[ValueId]) -> Ordering {
    a.iter()
        .map(|v| v.as_u32())
        .cmp(b.iter().map(|v| v.as_u32()))
}

fn project_transfer(stack: &SymStack, carry_in: &BitSet<ValueId>) -> TransferOrder {
    let mut out = TransferOrder::new();
    let mut seen: BitSet<ValueId> = BitSet::default();

    let limit = stack.len_above_func_ret();
    for i in 0..limit {
        let Some(StackItem::Value(v)) = stack.item_at(i) else {
            continue;
        };
        if carry_in.contains(*v) && seen.insert(*v) {
            out.push(*v);
        }
    }

    out
}

fn with_planner<'a, 'ctx, F>(
    ctx: &'a StackifyContext<'ctx>,
    mem: MemPlan<'a>,
    stack: &'a mut SymStack,
    actions: &'a mut Actions,
    f: F,
) where
    F: FnOnce(&mut Planner<'a, 'ctx>),
{
    let mut planner = Planner::new(ctx, stack, actions, mem);
    f(&mut planner);
}

impl<'a, 'ctx> FlowTemplateSolver<'a, 'ctx> {
    fn template_for(&self, block: BlockId) -> BlockTemplate {
        BlockTemplate {
            params: self.params_map[block].clone(),
            transfer: (&*self.state)[block].transfer.clone(),
        }
    }

    fn simulate_block_and_record_edges(&mut self, block: BlockId, template: &BlockTemplate) {
        let ctx = self.ctx;
        let spill = self.spill;
        let slots = &mut *self.slots;
        let spill_requests = &mut *self.spill_requests;
        let carry_in = self.carry_in;
        let edge_cand = &mut *self.edge_cand;

        let mut free_slots: FreeSlotPools = FreeSlotPools::default();
        let mut actions: Actions = Actions::new();

        let (mut remaining_uses, mut live_future) = count_block_uses(ctx.func, block);

        let mut live_out = ctx.liveness.block_live_outs(block).clone();
        live_out.union_with(&ctx.phi_out_sources[block]);

        let mut stack = SymStack::from_template(template, ctx.has_internal_return);

        let empty_last_use: BitSet<ValueId> = BitSet::default();

        for inst in ctx.func.layout.iter_inst(block) {
            if ctx.func.dfg.is_phi(inst) {
                continue;
            }

            actions.clear();

            let is_call = ctx.func.dfg.is_call(inst);
            let is_normal =
                ctx.func.dfg.branch_info(inst).is_none() && !ctx.func.dfg.is_return(inst);

            let mut args = SmallVec::<[ValueId; 8]>::new();
            let mut consume_last_use: BitSet<ValueId> = BitSet::default();
            if is_normal {
                args = operand_order_for_evm(ctx.func, inst);
                consume_last_use =
                    last_use_values_in_inst(ctx.func, &args, &remaining_uses, &live_out);
            }
            let last_use = if is_normal {
                &consume_last_use
            } else {
                &empty_last_use
            };

            clean_dead_stack_prefix(ctx.reach, &mut stack, &live_future, &live_out, &mut actions);

            if is_normal {
                improve_reachability_before_operands(
                    ctx.func,
                    &args,
                    ctx.reach,
                    &mut stack,
                    &live_future,
                    &live_out,
                    &mut actions,
                );
            }

            if is_call {
                stack.push_call_continuation(&mut actions);
            }

            if let Some(branch) = ctx.func.dfg.branch_info(inst) {
                match branch.branch_kind() {
                    BranchKind::Jump(jump) => {
                        let dest = *jump.dest();
                        edge_cand.insert((block, dest), project_transfer(&stack, &carry_in[dest]));
                        return;
                    }
                    BranchKind::Br(br) => {
                        let cond = *br.cond();
                        let consume_last_use =
                            last_use_values_in_inst(ctx.func, &[cond], &remaining_uses, &live_out);

                        improve_reachability_before_operands(
                            ctx.func,
                            &[cond],
                            ctx.reach,
                            &mut stack,
                            &live_future,
                            &live_out,
                            &mut actions,
                        );

                        let mem = planner::MemPlan::new(
                            spill,
                            spill_requests,
                            ctx,
                            &mut free_slots,
                            slots,
                        );
                        with_planner(ctx, mem, &mut stack, &mut actions, |planner| {
                            planner.prepare_operands(&[cond], &consume_last_use)
                        });

                        // The backend consumes the condition value for the actual branch.
                        let mut post_branch_stack = stack.clone();
                        post_branch_stack.pop_operand();

                        for succ in branch.dests().iter().copied() {
                            edge_cand.insert(
                                (block, succ),
                                project_transfer(&post_branch_stack, &carry_in[succ]),
                            );
                        }
                        return;
                    }
                    BranchKind::BrTable(table) => {
                        let scrutinee = *table.scrutinee();

                        improve_reachability_before_operands(
                            ctx.func,
                            &[scrutinee],
                            ctx.reach,
                            &mut stack,
                            &live_future,
                            &live_out,
                            &mut actions,
                        );

                        // As in final planning, all taken paths inherit the base stack state.
                        for &(_, dest) in table.table().iter() {
                            edge_cand
                                .insert((block, dest), project_transfer(&stack, &carry_in[dest]));
                        }
                        if let Some(default) = table.default() {
                            edge_cand.insert(
                                (block, *default),
                                project_transfer(&stack, &carry_in[*default]),
                            );
                        }
                        return;
                    }
                }
            }

            if ctx.func.dfg.is_return(inst) {
                let mem = planner::MemPlan::new(spill, spill_requests, ctx, &mut free_slots, slots);
                with_planner(ctx, mem, &mut stack, &mut actions, |planner| {
                    planner.plan_internal_return(inst)
                });
                return;
            }

            // Normal instruction.
            let mem = planner::MemPlan::new(spill, spill_requests, ctx, &mut free_slots, slots);

            with_planner(ctx, mem, &mut stack, &mut actions, |planner| {
                planner.prepare_operands_for_inst(inst, &mut args, last_use)
            });

            let res = ctx.func.dfg.inst_result(inst);

            for &v in args.iter() {
                if !ctx.func.dfg.value_is_imm(v)
                    && let Some(n) = remaining_uses.get_mut(&v)
                {
                    let before = *n;
                    *n = n.saturating_sub(1);
                    if before != 0 && *n == 0 {
                        live_future.remove(v);
                        if !live_out.contains(v) {
                            slots
                                .persistent
                                .release_if_assigned(v, &mut free_slots.persistent);
                            slots
                                .scratch
                                .release_if_assigned(v, &mut free_slots.scratch);
                            slots
                                .transient
                                .release_if_assigned(v, &mut free_slots.transient);
                        }
                    }
                }
            }

            stack.pop_n_operands(args.len());

            if is_call {
                stack.remove_call_ret_addr();
            }

            if let Some(res) = res {
                stack.push_value(res);
                if live_future.contains(res) || live_out.contains(res) {
                    let mem =
                        planner::MemPlan::new(spill, spill_requests, ctx, &mut free_slots, slots);
                    with_planner(ctx, mem, &mut stack, &mut actions, |planner| {
                        planner.emit_store_if_spilled(res)
                    });
                }
            }
        }
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
        for _iter in 0..MAX_ITER {
            for &block in &data.blocks_rpo {
                let tmpl = self.template_for(block);
                self.simulate_block_and_record_edges(block, &tmpl);
            }

            let mut changed = false;

            // For single-entry cyclic SCCs (reducible loops), pin the header transfer once we have
            // evidence of a real join conflict, preferring the backedge-derived candidate. This
            // biases the fixed point toward the loop's steady-state layout instead of the function
            // entry edge and avoids oscillation between competing layouts.
            if let Some(header) = data.header()
                && header != ctx.entry
                && !self.state[header].pinned
                && let Some(backedge_cand) =
                    best_backedge_candidate(ctx, scc, header, &*self.edge_cand)
                && header_has_conflict(ctx, header, &*self.edge_cand)
            {
                if self.state[header].transfer != backedge_cand {
                    self.state[header].transfer = backedge_cand;
                    changed = true;
                }
                self.state[header].pinned = true;
            }

            for &block in &data.blocks_rpo {
                if self.state[block].pinned {
                    continue;
                }
                let fallback = self.state[block].transfer.clone();
                let new_t = choose_transfer_from_preds(
                    ctx,
                    block,
                    self.carry_in,
                    &*self.edge_cand,
                    Some(scc),
                    Some(&fallback),
                );
                if new_t != fallback {
                    self.state[block].transfer = new_t;
                    changed = true;
                }
            }
            if !changed {
                return;
            }
        }

        for &block in &data.blocks_rpo {
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
