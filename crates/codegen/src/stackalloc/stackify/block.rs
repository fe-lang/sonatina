use std::ops::ControlFlow;

use cranelift_entity::SecondaryMap;
use smallvec::SmallVec;
use sonatina_ir::{BlockId, Function, InstId, ValueId, inst::control_flow::BranchKind};

use crate::{bitset::BitSet, stackalloc::Actions};

use super::{
    br_table::plan_br_table_compare_chain,
    builder::StackifyContext,
    driver::FunctionPlanner,
    rescue::{clean_dead_stack_prefix, improve_reachability_before_operands},
    slots::FreeSlotPools,
    sym_stack::SymStack,
    trace::StackifyObserver,
    uses::UseTracker,
};

pub(super) struct BlockSimState {
    pub(super) block: BlockId,
    pub(super) free_slots: FreeSlotPools,
    pub(super) prologue: Actions,
    pub(super) injected_prologue: bool,
    pub(super) uses: UseTracker,
    pub(super) stack: SymStack,
}

impl BlockSimState {
    pub(super) fn new(
        block: BlockId,
        stack: SymStack,
        free_slots: FreeSlotPools,
        prologue: Actions,
        uses: UseTracker,
    ) -> Self {
        Self {
            block,
            free_slots,
            prologue,
            injected_prologue: false,
            uses,
            stack,
        }
    }
}

pub(super) enum PlannerActionSink {
    Pre(InstId),
    Post(InstId),
    BrTableCase { inst: InstId, case_idx: usize },
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

/// The per-block instruction walk: threads a `SymStack` through one block, emitting actions and
/// trace events, and dispatching each terminator. Owns the block's `BlockSimState` and borrows the
/// driver ([`FunctionPlanner`]) for the planner/memory seams and cross-block edge bookkeeping.
pub(super) struct BlockPlanner<'d, 'a, 'ctx, O: StackifyObserver> {
    driver: &'d mut FunctionPlanner<'a, 'ctx, O>,
    state: BlockSimState,
}

impl<'d, 'a, 'ctx, O: StackifyObserver> BlockPlanner<'d, 'a, 'ctx, O> {
    pub(super) fn new(driver: &'d mut FunctionPlanner<'a, 'ctx, O>, state: BlockSimState) -> Self {
        Self { driver, state }
    }

    pub(super) fn run(mut self) -> BlockSimState {
        // `func` is a shared `&Function` copied out of the driver, so the layout iterator does not
        // borrow the driver and is free to coexist with the `&mut self` calls in the loop body.
        let func = self.driver.ctx().func;
        let block = self.state.block;
        for inst in func.layout.iter_inst(block) {
            if func.dfg.is_phi(inst) {
                continue;
            }
            if self.plan_inst(inst).is_break() {
                break;
            }
        }
        self.state
    }

    /// Plan one non-phi instruction: dead-prefix cleanup + reachability rescue, then dispatch to
    /// the terminator-specific or normal-instruction planner. Returns `Break` for terminators (the
    /// block walk stops) and `Continue` otherwise.
    fn plan_inst(&mut self, inst: InstId) -> ControlFlow<()> {
        self.driver.debug_assert_inst_actions_empty(inst);

        let is_call = self.driver.ctx().func.dfg.is_call(inst);
        let call_has_stack_continuation =
            is_call && call_has_local_return(self.driver.ctx().func, inst);
        let terminator = terminator_info(self.driver.ctx(), inst);
        let is_return = self.driver.ctx().func.dfg.is_return(inst);
        let is_normal = terminator.is_none() && !is_return;
        let skip_cleanup = skip_pre_exit_cleanup(self.driver.ctx().func, inst);

        let empty_last_use: BitSet<ValueId> = BitSet::default();
        let mut args = SmallVec::<[ValueId; 8]>::new();
        let mut consume_last_use: BitSet<ValueId> = BitSet::default();
        if is_normal {
            args = operand_order_for_stackify(
                self.driver.ctx().func,
                inst,
                &self.driver.ctx().value_aliases,
            );
            consume_last_use = self.state.uses.last_uses_in(self.driver.ctx(), &args);
        }
        let cache_preserve = if is_normal {
            self.state.uses.cache_preserve_in(self.driver.ctx(), &args)
        } else {
            BitSet::default()
        };
        let last_use = if is_normal {
            &consume_last_use
        } else {
            &empty_last_use
        };

        self.inject_prologue_once(inst);
        {
            let func = self.driver.ctx().func;
            let stack = &self.state.stack;
            let live_future = self.state.uses.live_future();
            let live_out = self.state.uses.live_out();
            self.driver.observer().on_inst_start(
                func,
                inst,
                stack,
                live_future,
                live_out,
                last_use,
            );
        }

        let before_cleanup_len = self.driver.pre_actions_len(inst);
        if !skip_cleanup {
            // `live_future` includes cached immediates until their last in-block use, so
            // dead-prefix cleanup does not drop a reusable cached-immediate stack copy.
            let live_future = self.state.uses.live_future();
            let live_out = self.state.uses.live_out();
            let reach = self.driver.ctx().reach;
            self.driver.with_pre_actions(inst, |actions| {
                clean_dead_stack_prefix(
                    reach,
                    &mut self.state.stack,
                    live_future,
                    live_out,
                    actions,
                );
            });
        }
        if is_normal && !skip_cleanup {
            self.rescue_reachability(inst, &args);
        }
        let after_cleanup_len = self.driver.pre_actions_len(inst);
        {
            let (observer, alloc) = self.driver.trace_actions();
            observer.on_inst_actions(
                "cleanup",
                &alloc.pre_actions[inst][before_cleanup_len..after_cleanup_len],
                None,
            );
        }

        if let Some(terminator) = terminator {
            match terminator {
                TerminatorInfo::Jump(dest) => self.plan_jump(inst, dest, after_cleanup_len),
                TerminatorInfo::Br { cond, dests } => {
                    self.plan_br(inst, cond, &dests, after_cleanup_len)
                }
                TerminatorInfo::BrTable {
                    scrutinee,
                    table,
                    default,
                } => self.plan_br_table(inst, scrutinee, table, default),
            }
            return ControlFlow::Break(());
        }

        if is_return {
            self.plan_return(inst, after_cleanup_len);
            return ControlFlow::Break(());
        }

        self.plan_normal_inst(
            inst,
            args,
            last_use,
            &cache_preserve,
            call_has_stack_continuation,
            after_cleanup_len,
        );
        ControlFlow::Continue(())
    }

    /// Inject the block prologue into the first non-phi instruction's pre-actions, exactly once.
    ///
    /// Every block has a terminator that runs through here, so a non-empty prologue is always
    /// injected by the end of the walk (asserted by `plan_block` in the driver).
    fn inject_prologue_once(&mut self, inst: InstId) {
        if self.state.prologue.is_empty() || self.state.injected_prologue {
            return;
        }
        let prologue = &self.state.prologue;
        self.driver
            .with_pre_actions(inst, |actions| actions.extend_from_slice(prologue));
        self.state.injected_prologue = true;
    }

    /// Reachability rescue for `operands` into `inst`'s pre-actions. Called by the normal path and
    /// the `Br`/`BrTable` arms with their own operand list (`args`, `[cond]`, `[scrutinee]`), each
    /// at the point where the rescue must run to preserve emitted action order.
    fn rescue_reachability(&mut self, inst: InstId, operands: &[ValueId]) {
        let func = self.driver.ctx().func;
        let reach = self.driver.ctx().reach;
        self.driver.with_pre_actions(inst, |actions| {
            improve_reachability_before_operands(
                func,
                operands,
                reach,
                &mut self.state.stack,
                &self.state.uses,
                actions,
            );
        });
    }

    fn plan_jump(&mut self, inst: InstId, dest: BlockId, action_start: usize) {
        // The pending-edge case emits its exit + jump trace inside `record_jump_edge` (the deferred
        // token must be captured synchronously with the pending edge); the other cases emit here.
        if self
            .driver
            .record_jump_edge(&mut self.state, inst, dest, action_start)
        {
            return;
        }
        let (observer, alloc) = self.driver.trace_actions();
        observer.on_inst_actions("exit", &alloc.pre_actions[inst][action_start..], Some(dest));
        observer.on_inst_jump(inst, dest);
    }

    fn plan_br(
        &mut self,
        inst: InstId,
        cond: ValueId,
        dests: &[BlockId],
        after_cleanup_len: usize,
    ) {
        let consume_last_use = self.state.uses.last_uses_in(self.driver.ctx(), &[cond]);

        self.rescue_reachability(inst, &[cond]);
        self.driver.with_planner(
            &mut self.state.stack,
            &mut self.state.free_slots,
            PlannerActionSink::Pre(inst),
            |planner| {
                planner.prepare_operands(&[cond], &consume_last_use, &BitSet::default());
            },
        );

        {
            let (observer, alloc) = self.driver.trace_actions();
            observer.on_inst_actions("pre", &alloc.pre_actions[inst][after_cleanup_len..], None);
        }
        {
            let func = self.driver.ctx().func;
            self.driver.observer().on_inst_br(func, inst, cond, dests);
        }

        let mut post_branch_stack = self.state.stack.clone();
        post_branch_stack.pop_operand();

        for succ in dests.iter().copied() {
            self.driver
                .record_branch_edge(&mut self.state, succ, &post_branch_stack);
        }
    }

    fn plan_br_table(
        &mut self,
        inst: InstId,
        scrutinee: ValueId,
        table: Vec<(ValueId, BlockId)>,
        default: Option<BlockId>,
    ) {
        self.rescue_reachability(inst, &[scrutinee]);

        let (case_stacks, default_stack) = plan_br_table_compare_chain(
            &table,
            &self.state.stack,
            |case_idx, case_val, case_stack| {
                self.driver.with_planner(
                    case_stack,
                    &mut self.state.free_slots,
                    PlannerActionSink::BrTableCase { inst, case_idx },
                    |planner| {
                        let consume_last_use = BitSet::<ValueId>::default();
                        let mut compare_args = smallvec::smallvec![scrutinee, case_val];
                        planner.prepare_operands_for_commutative_pair(
                            &mut compare_args,
                            &consume_last_use,
                            &BitSet::default(),
                        );
                    },
                );
            },
        );

        for case in case_stacks {
            self.driver
                .record_br_table_edge(&mut self.state, case.dest, &case.post_compare_stack);
        }
        if let Some(default) = default {
            self.driver
                .record_br_table_edge(&mut self.state, default, &default_stack);
        }

        self.driver.observer().on_inst_br_table(inst);
    }

    fn plan_return(&mut self, inst: InstId, after_cleanup_len: usize) {
        self.driver.with_planner(
            &mut self.state.stack,
            &mut self.state.free_slots,
            PlannerActionSink::Pre(inst),
            |planner| planner.plan_internal_return(inst),
        );

        {
            let (observer, alloc) = self.driver.trace_actions();
            observer.on_inst_actions(
                "return",
                &alloc.pre_actions[inst][after_cleanup_len..],
                None,
            );
        }
        let func = self.driver.ctx().func;
        let ret_vals: SmallVec<[ValueId; 16]> = func
            .dfg
            .return_args(inst)
            .map(|args| args.iter().copied().collect())
            .unwrap_or_default();
        self.driver
            .observer()
            .on_inst_return(func, inst, ret_vals.as_slice());
    }

    fn plan_normal_inst(
        &mut self,
        inst: InstId,
        mut args: SmallVec<[ValueId; 8]>,
        last_use: &BitSet<ValueId>,
        cache_preserve: &BitSet<ValueId>,
        call_has_stack_continuation: bool,
        after_cleanup_len: usize,
    ) {
        let results: SmallVec<[ValueId; 4]> = self
            .driver
            .ctx()
            .func
            .dfg
            .inst_results(inst)
            .iter()
            .map(|&v| self.driver.ctx().canonicalize_value(v))
            .collect();

        self.driver.with_planner(
            &mut self.state.stack,
            &mut self.state.free_slots,
            PlannerActionSink::Pre(inst),
            |planner| {
                if call_has_stack_continuation {
                    planner.prepare_internal_call(inst, &mut args, last_use, cache_preserve);
                } else {
                    planner.prepare_operands_for_inst(inst, &mut args, last_use, cache_preserve);
                }
            },
        );

        {
            let (observer, alloc) = self.driver.trace_actions();
            observer.on_inst_actions("pre", &alloc.pre_actions[inst][after_cleanup_len..], None);
        }
        {
            let func = self.driver.ctx().func;
            self.driver
                .observer()
                .on_inst_normal(func, inst, &args, &results);
        }

        self.state.uses.consume(
            self.driver.ctx(),
            &args,
            self.driver.scratch_slots(),
            &mut self.state.free_slots.scratch,
        );

        self.state.stack.pop_n_operands(args.len());

        if call_has_stack_continuation {
            self.state.stack.pop_call_ret_addr();
        }

        for &res in results.iter().rev() {
            self.state.stack.push_value(res);
        }

        for (depth, &res) in results.iter().enumerate() {
            if self.state.uses.is_dead(res) {
                continue;
            }
            self.driver.with_planner(
                &mut self.state.stack,
                &mut self.state.free_slots,
                PlannerActionSink::Post(inst),
                |planner| planner.emit_store_if_spilled_at_depth(res, depth),
            );
        }

        {
            let (observer, alloc) = self.driver.trace_actions();
            observer.on_inst_actions("post", &alloc.post_actions[inst], None);
        }
    }
}

pub(super) fn skip_pre_exit_cleanup(func: &Function, inst: InstId) -> bool {
    func.dfg.is_exit(inst) && !func.dfg.is_return(inst)
}

/// The alias-canonicalized operand order stackify plans against. For internal calls (those that
/// may return to the caller) the operands are rotated left by one so that a single `SWAP` after
/// pushing the return continuation restores callee ABI order — pairing with
/// `Planner::prepare_internal_call`; see the ABI note there.
pub(super) fn operand_order_for_stackify(
    func: &Function,
    inst: InstId,
    value_aliases: &SecondaryMap<ValueId, Option<ValueId>>,
) -> SmallVec<[ValueId; 8]> {
    let mut args: SmallVec<[ValueId; 8]> = func
        .dfg
        .inst(inst)
        .collect_values()
        .into_iter()
        .map(|v| value_aliases[v].unwrap_or(v))
        .collect();

    if call_has_local_return(func, inst) && !args.is_empty() {
        args.as_mut_slice().rotate_left(1);
    }

    args
}

fn call_has_local_return(func: &Function, inst: InstId) -> bool {
    func.dfg.call_info(inst).is_some_and(|call| {
        func.ctx()
            .func_effects(call.callee())
            .may_return_to_caller()
    })
}
