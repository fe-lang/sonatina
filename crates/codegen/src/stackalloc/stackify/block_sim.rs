use std::collections::BTreeMap;

use smallvec::SmallVec;
use sonatina_ir::{BlockId, InstId, ValueId, inst::control_flow::BranchKind};

use crate::{bitset::BitSet, stackalloc::Actions};

use super::{
    br_table::plan_br_table_compare_chain,
    builder::StackifyContext,
    iteration::{
        clean_dead_stack_prefix, consume_operand_uses, count_block_uses,
        improve_reachability_before_operands, inst_is_noop_alias_cast, last_use_values_in_inst,
        operand_order_for_evm, skip_pre_exit_cleanup,
    },
    planner::Planner,
    slots::{FreeSlotPools, SlotPool},
    sym_stack::SymStack,
};

pub(super) struct BlockSimState {
    pub(super) block: BlockId,
    pub(super) free_slots: FreeSlotPools,
    pub(super) prologue: Actions,
    pub(super) injected_prologue: bool,
    remaining_uses: BTreeMap<ValueId, u32>,
    live_future: BitSet<ValueId>,
    live_out: BitSet<ValueId>,
    pub(super) stack: SymStack,
}

impl BlockSimState {
    pub(super) fn block_live_sets(
        ctx: &StackifyContext<'_>,
        block: BlockId,
    ) -> (BTreeMap<ValueId, u32>, BitSet<ValueId>, BitSet<ValueId>) {
        let (remaining_uses, live_future) = count_block_uses(ctx.func, block, &ctx.value_aliases);
        let mut live_out = ctx.liveness.block_live_outs(block).clone();
        live_out.union_with(&ctx.phi_out_sources[block]);
        (remaining_uses, live_future, live_out)
    }

    pub(super) fn with_live_sets(
        block: BlockId,
        stack: SymStack,
        free_slots: FreeSlotPools,
        prologue: Actions,
        remaining_uses: BTreeMap<ValueId, u32>,
        live_future: BitSet<ValueId>,
        live_out: BitSet<ValueId>,
    ) -> Self {
        Self {
            block,
            free_slots,
            prologue,
            injected_prologue: false,
            remaining_uses,
            live_future,
            live_out,
            stack,
        }
    }

    pub(super) fn live_future(&self) -> &BitSet<ValueId> {
        &self.live_future
    }

    pub(super) fn live_out(&self) -> &BitSet<ValueId> {
        &self.live_out
    }
}

pub(super) enum PlannerActionSink<'a> {
    Pre(InstId),
    Post(InstId),
    BrTableCase {
        inst: InstId,
        case_idx: usize,
        prefix: Option<&'a Actions>,
    },
}

pub(super) enum BrTableEdgeKind {
    Case,
    Default,
}

enum TerminatorInfo {
    Jump(BlockId),
    Br {
        cond: ValueId,
        dests: SmallVec<[BlockId; 2]>,
    },
    BrTable {
        scrutinee: ValueId,
        table: Vec<(ValueId, BlockId)>,
        default: Option<BlockId>,
    },
}

pub(super) trait BlockSimMode<'ctx> {
    fn ctx(&self) -> &StackifyContext<'ctx>;
    fn call_uses_stack_continuation(&self, inst: InstId) -> bool;
    fn scratch_slots(&self) -> &SlotPool;

    fn clear_inst_actions(&mut self, _inst: InstId) {}
    fn pre_actions_len(&self, _inst: InstId) -> usize {
        0
    }

    fn with_pre_actions<R>(&mut self, inst: InstId, f: impl FnOnce(&mut Actions) -> R) -> R;

    fn take_pre_actions_for_br_table(&mut self, _inst: InstId) -> Actions {
        Actions::new()
    }

    fn with_planner<R>(
        &mut self,
        stack: &mut SymStack,
        free_slots: &mut FreeSlotPools,
        sink: PlannerActionSink<'_>,
        f: impl FnOnce(&mut Planner<'_, '_>) -> R,
    ) -> R;

    fn on_inst_start(
        &mut self,
        _state: &mut BlockSimState,
        _inst: InstId,
        _last_use: &BitSet<ValueId>,
    ) {
    }
    fn on_alias_noop(&mut self, _inst: InstId, _args: &[ValueId], _results: &[ValueId]) {}
    fn on_cleanup_actions(&mut self, _inst: InstId, _start: usize, _end: usize) {}
    fn on_pre_actions(&mut self, _inst: InstId, _start: usize) {}
    fn on_post_actions(&mut self, _inst: InstId) {}
    fn on_normal_inst(&mut self, _inst: InstId, _args: &[ValueId], _results: &[ValueId]) {}
    fn on_return(&mut self, _inst: InstId, _start: usize) {}
    fn on_jump(
        &mut self,
        _state: &mut BlockSimState,
        _inst: InstId,
        _dest: BlockId,
        _stack: SymStack,
        _action_start: usize,
    ) {
    }
    fn on_branch(&mut self, _inst: InstId, _cond: ValueId, _dests: &[BlockId]) {}
    fn on_branch_edge(
        &mut self,
        _state: &mut BlockSimState,
        _inst: InstId,
        _succ: BlockId,
        _stack: SymStack,
    ) {
    }
    fn on_br_table_edge(
        &mut self,
        _state: &mut BlockSimState,
        _inst: InstId,
        _succ: BlockId,
        _stack: SymStack,
        _kind: BrTableEdgeKind,
    ) {
    }
    fn on_br_table(&mut self, _inst: InstId) {}
}

fn take_stack(stack: &mut SymStack, has_internal_return: bool) -> SymStack {
    std::mem::replace(stack, SymStack::opaque_prefix_empty(has_internal_return))
}

fn terminator_info(ctx: &StackifyContext<'_>, inst: InstId) -> Option<TerminatorInfo> {
    let branch = ctx.func.dfg.branch_info(inst)?;
    match branch.branch_kind() {
        BranchKind::Jump(jump) => Some(TerminatorInfo::Jump(*jump.dest())),
        BranchKind::Br(br) => Some(TerminatorInfo::Br {
            cond: ctx.canonicalize_value(*br.cond()),
            dests: branch.dests(),
        }),
        BranchKind::BrTable(table) => Some(TerminatorInfo::BrTable {
            scrutinee: ctx.canonicalize_value(*table.scrutinee()),
            table: table.table().to_vec(),
            default: *table.default(),
        }),
    }
}

pub(super) fn run_block_sim<'ctx, M: BlockSimMode<'ctx>>(
    mode: &mut M,
    mut state: BlockSimState,
) -> BlockSimState {
    let empty_last_use: BitSet<ValueId> = BitSet::default();

    let insts: Vec<_> = mode.ctx().func.layout.iter_inst(state.block).collect();
    for inst in insts {
        if mode.ctx().func.dfg.is_phi(inst) {
            continue;
        }

        mode.clear_inst_actions(inst);

        let is_call = mode.ctx().func.dfg.is_call(inst);
        let call_has_stack_continuation = is_call && mode.call_uses_stack_continuation(inst);
        let terminator = terminator_info(mode.ctx(), inst);
        let is_normal = terminator.is_none() && !mode.ctx().func.dfg.is_return(inst);
        let skip_cleanup = skip_pre_exit_cleanup(mode.ctx().func, inst);

        let mut args = SmallVec::<[ValueId; 8]>::new();
        let mut consume_last_use: BitSet<ValueId> = BitSet::default();
        if is_normal {
            args = operand_order_for_evm(mode.ctx().func, inst, &mode.ctx().value_aliases);
            consume_last_use = last_use_values_in_inst(
                mode.ctx().func,
                &args,
                &state.remaining_uses,
                &state.live_out,
            );
        }
        let last_use = if is_normal {
            &consume_last_use
        } else {
            &empty_last_use
        };
        mode.on_inst_start(&mut state, inst, last_use);

        let results: SmallVec<[ValueId; 4]> = mode
            .ctx()
            .func
            .dfg
            .inst_results(inst)
            .iter()
            .map(|&v| mode.ctx().canonicalize_value(v))
            .collect();
        let res = match results.as_slice() {
            [res] => Some(*res),
            _ => None,
        };
        if is_normal && inst_is_noop_alias_cast(mode.ctx(), inst, &args, res) {
            mode.on_alias_noop(inst, &args, &results);
            consume_operand_uses(
                mode.ctx().func,
                &args,
                &mut state.remaining_uses,
                &mut state.live_future,
                &state.live_out,
                mode.scratch_slots(),
                &mut state.free_slots.scratch,
            );
            continue;
        }

        let before_cleanup_len = mode.pre_actions_len(inst);
        if !skip_cleanup {
            let reach = mode.ctx().reach;
            mode.with_pre_actions(inst, |actions| {
                clean_dead_stack_prefix(
                    reach,
                    &mut state.stack,
                    &state.live_future,
                    &state.live_out,
                    actions,
                );
            });
        }

        if is_normal && !skip_cleanup {
            let func = mode.ctx().func;
            let reach = mode.ctx().reach;
            mode.with_pre_actions(inst, |actions| {
                improve_reachability_before_operands(
                    func,
                    &args,
                    reach,
                    &mut state.stack,
                    &state.live_future,
                    &state.live_out,
                    actions,
                );
            });
        }
        let after_cleanup_len = mode.pre_actions_len(inst);
        mode.on_cleanup_actions(inst, before_cleanup_len, after_cleanup_len);

        if let Some(terminator) = terminator {
            match terminator {
                TerminatorInfo::Jump(dest) => {
                    let stack = state.stack.clone();
                    mode.on_jump(&mut state, inst, dest, stack, after_cleanup_len);
                    return state;
                }
                TerminatorInfo::Br { cond, dests } => {
                    let consume_last_use = last_use_values_in_inst(
                        mode.ctx().func,
                        &[cond],
                        &state.remaining_uses,
                        &state.live_out,
                    );

                    let func = mode.ctx().func;
                    let reach = mode.ctx().reach;
                    mode.with_pre_actions(inst, |actions| {
                        improve_reachability_before_operands(
                            func,
                            &[cond],
                            reach,
                            &mut state.stack,
                            &state.live_future,
                            &state.live_out,
                            actions,
                        );
                    });
                    let mut stack = take_stack(&mut state.stack, mode.ctx().has_internal_return);
                    mode.with_planner(
                        &mut stack,
                        &mut state.free_slots,
                        PlannerActionSink::Pre(inst),
                        |planner| planner.prepare_operands(&[cond], &consume_last_use),
                    );
                    state.stack = stack;

                    mode.on_pre_actions(inst, after_cleanup_len);
                    mode.on_branch(inst, cond, dests.as_slice());

                    let mut post_branch_stack = state.stack.clone();
                    post_branch_stack.pop_operand();

                    for succ in dests.iter().copied() {
                        mode.on_branch_edge(&mut state, inst, succ, post_branch_stack.clone());
                    }
                    return state;
                }
                TerminatorInfo::BrTable {
                    scrutinee,
                    table,
                    default,
                } => {
                    let func = mode.ctx().func;
                    let reach = mode.ctx().reach;
                    mode.with_pre_actions(inst, |actions| {
                        improve_reachability_before_operands(
                            func,
                            &[scrutinee],
                            reach,
                            &mut state.stack,
                            &state.live_future,
                            &state.live_out,
                            actions,
                        );
                    });

                    let base_actions = mode.take_pre_actions_for_br_table(inst);
                    let (case_stacks, default_stack) = plan_br_table_compare_chain(
                        &table,
                        &state.stack,
                        |case_idx, case_val, case_stack| {
                            let prefix = (case_idx == 0).then_some(&base_actions);
                            mode.with_planner(
                                case_stack,
                                &mut state.free_slots,
                                PlannerActionSink::BrTableCase {
                                    inst,
                                    case_idx,
                                    prefix,
                                },
                                |planner| {
                                    let consume_last_use = BitSet::<ValueId>::default();
                                    let mut compare_args = smallvec::smallvec![scrutinee, case_val];
                                    planner.prepare_operands_for_commutative_pair(
                                        &mut compare_args,
                                        &consume_last_use,
                                    );
                                },
                            );
                        },
                    );

                    for case in case_stacks {
                        mode.on_br_table_edge(
                            &mut state,
                            inst,
                            case.dest,
                            case.post_compare_stack,
                            BrTableEdgeKind::Case,
                        );
                    }
                    if let Some(default) = default {
                        mode.on_br_table_edge(
                            &mut state,
                            inst,
                            default,
                            default_stack,
                            BrTableEdgeKind::Default,
                        );
                    }

                    mode.on_br_table(inst);
                    return state;
                }
            }
        }

        if mode.ctx().func.dfg.is_return(inst) {
            let mut stack = take_stack(&mut state.stack, mode.ctx().has_internal_return);
            mode.with_planner(
                &mut stack,
                &mut state.free_slots,
                PlannerActionSink::Pre(inst),
                |planner| planner.plan_internal_return(inst),
            );
            state.stack = stack;
            mode.on_return(inst, after_cleanup_len);
            return state;
        }

        let mut stack = take_stack(&mut state.stack, mode.ctx().has_internal_return);
        mode.with_planner(
            &mut stack,
            &mut state.free_slots,
            PlannerActionSink::Pre(inst),
            |planner| planner.prepare_operands_for_inst(inst, &mut args, last_use),
        );
        state.stack = stack;

        if call_has_stack_continuation {
            mode.with_pre_actions(inst, |actions| {
                state.stack.push_call_continuation(actions);
                state
                    .stack
                    .position_call_ret_below_operands(args.len(), actions);
            });
        }

        mode.on_pre_actions(inst, after_cleanup_len);
        mode.on_normal_inst(inst, &args, &results);

        consume_operand_uses(
            mode.ctx().func,
            &args,
            &mut state.remaining_uses,
            &mut state.live_future,
            &state.live_out,
            mode.scratch_slots(),
            &mut state.free_slots.scratch,
        );

        state.stack.pop_n_operands(args.len());

        if call_has_stack_continuation {
            state.stack.remove_call_ret_addr();
        }

        for &res in results.iter().rev() {
            state.stack.push_value(res);
        }

        for (depth, &res) in results.iter().enumerate() {
            if !state.live_future.contains(res) && !state.live_out.contains(res) {
                continue;
            }
            let mut stack = take_stack(&mut state.stack, mode.ctx().has_internal_return);
            mode.with_planner(
                &mut stack,
                &mut state.free_slots,
                PlannerActionSink::Post(inst),
                |planner| planner.emit_store_if_spilled_at_depth(res, depth),
            );
            state.stack = stack;
        }

        mode.on_post_actions(inst);
    }

    state
}
