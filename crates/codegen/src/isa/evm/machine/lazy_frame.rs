use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, Type, ValueId,
    cfg::ControlFlowGraph,
    inst::evm::{inst_set::EvmInstKind, machine_inst_set::EvmMachineInstKind},
    isa::{Isa, evm::Evm},
};

use crate::{
    domtree::DomTree,
    post_domtree::{PDTIdom, PostDomTree},
    stackalloc::{Action, Allocator},
};

use super::module::FuncMachineMap;
use crate::isa::evm::{MachineFuncPlan, ObjLoc, emit::fold_stack_actions};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FrameSite {
    BlockEntry(BlockId),
    EnterFunction,
    PreInst(InstId),
    Inst(InstId),
    PostInst(InstId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum FrameInjectionPoint {
    BeforeSite(FrameSite),
    BeforeAction {
        site: FrameSite,
        action_index: usize,
    },
    AfterAction {
        site: FrameSite,
        action_index: usize,
    },
    AfterSite(FrameSite),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LazyFramePlan {
    enter: FrameInjectionPoint,
    exits: Vec<FrameInjectionPoint>,
}

impl LazyFramePlan {
    pub(crate) fn enter_before_site(&self, site: FrameSite) -> bool {
        self.enter == FrameInjectionPoint::BeforeSite(site)
    }

    pub(crate) fn enter_before_action(&self, site: FrameSite, action_index: usize) -> bool {
        self.enter == FrameInjectionPoint::BeforeAction { site, action_index }
    }

    pub(crate) fn exit_before_site(&self, site: FrameSite) -> bool {
        self.exits
            .iter()
            .copied()
            .any(|point| point == FrameInjectionPoint::BeforeSite(site))
    }

    pub(crate) fn exit_before_action(&self, site: FrameSite, action_index: usize) -> bool {
        self.exits
            .iter()
            .copied()
            .any(|point| point == FrameInjectionPoint::BeforeAction { site, action_index })
    }

    pub(crate) fn exit_after_action(&self, site: FrameSite, action_index: usize) -> bool {
        self.exits
            .iter()
            .copied()
            .any(|point| point == FrameInjectionPoint::AfterAction { site, action_index })
    }

    pub(crate) fn exit_after_site(&self, site: FrameSite) -> bool {
        self.exits
            .iter()
            .copied()
            .any(|point| point == FrameInjectionPoint::AfterSite(site))
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FrameSummary {
    pub(crate) lowering: Option<LazyFramePlan>,
    pub(crate) full_body_active: bool,
    active_pre_insts: FxHashSet<InstId>,
}

impl FrameSummary {
    pub(crate) fn local_frame_active_before_inst(&self, inst: InstId) -> bool {
        self.full_body_active || self.active_pre_insts.contains(&inst)
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct MachineFrameRoots {
    root_def_insts: FxHashSet<InstId>,
    rooted_values: FxHashSet<ValueId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum PostNode {
    Real(BlockId),
    DummyExit(BlockId),
    DummyEntry(BlockId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct DepPoint {
    block: BlockId,
    order: PointOrder,
    point: FrameInjectionPoint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct PointOrder {
    site_rank: u32,
    phase_rank: u32,
    action_rank: u32,
}

struct PointOrderTable {
    entry_block: BlockId,
    inst_order: FxHashMap<InstId, u32>,
}

struct RootUseDepCtx<'a> {
    reachable_returns: &'a FxHashMap<BlockId, Vec<(BlockId, InstId)>>,
    rooted: &'a FxHashSet<ValueId>,
    order: &'a PointOrderTable,
}

pub(crate) fn compute_machine_frame_roots(
    source: &Function,
    machine: &Function,
    map: &FuncMachineMap,
    alloca_loc: &FxHashMap<InstId, ObjLoc>,
    source_isa: &Evm,
) -> MachineFrameRoots {
    let source_roots = compute_source_rooted_frame_values(source, alloca_loc, source_isa);
    let mut roots = MachineFrameRoots::default();
    for source_value in source_roots {
        let Some(machine_value) = map.values[source_value] else {
            continue;
        };
        roots.rooted_values.insert(machine_value);
        collect_root_def_insts(
            machine,
            machine_value,
            &mut roots.root_def_insts,
            &mut FxHashSet::default(),
        );
    }
    roots
}

fn collect_root_def_insts(
    function: &Function,
    value: ValueId,
    root_def_insts: &mut FxHashSet<InstId>,
    seen: &mut FxHashSet<ValueId>,
) {
    if !seen.insert(value) {
        return;
    }
    let Some(inst) = function.dfg.value_inst(value) else {
        return;
    };
    if function.layout.try_inst_block(inst).is_none() {
        return;
    }
    root_def_insts.insert(inst);
    for operand in function.dfg.inst(inst).collect_values() {
        collect_root_def_insts(function, operand, root_def_insts, seen);
    }
}

pub(crate) fn compute_frame_summary(
    function: &Function,
    alloc: &dyn Allocator,
    mem_plan: &MachineFuncPlan,
    roots: &MachineFrameRoots,
) -> FrameSummary {
    if mem_plan.dynamic_frame_layout().is_none() {
        return FrameSummary::default();
    }

    let Some(plan) = compute_lazy_frame_plan_inner(function, alloc, roots) else {
        return FrameSummary {
            lowering: None,
            full_body_active: true,
            active_pre_insts: FxHashSet::default(),
        };
    };

    if validate_lazy_frame_activity(function, alloc, &plan).is_none() {
        return FrameSummary {
            lowering: None,
            full_body_active: true,
            active_pre_insts: FxHashSet::default(),
        };
    };

    let Some(active_pre_insts) = compute_active_pre_insts(function, alloc, &plan) else {
        return FrameSummary {
            lowering: Some(plan),
            full_body_active: true,
            active_pre_insts: FxHashSet::default(),
        };
    };

    FrameSummary {
        lowering: Some(plan),
        full_body_active: false,
        active_pre_insts,
    }
}

fn compute_lazy_frame_plan_inner(
    function: &Function,
    alloc: &dyn Allocator,
    roots: &MachineFrameRoots,
) -> Option<LazyFramePlan> {
    function.layout.entry_block()?;

    let mut cfg = ControlFlowGraph::default();
    cfg.compute(function);
    let dep_points = collect_dep_points(function, &cfg, alloc, roots)?;
    if dep_points.is_empty() {
        return None;
    }

    let mut dep_blocks: Vec<BlockId> = dep_points.iter().map(|point| point.block).collect();
    dep_blocks.sort_unstable_by_key(|block| block.as_u32());
    dep_blocks.dedup();

    let mut dom = DomTree::new();
    dom.compute(&cfg);
    let mut post_dom = PostDomTree::new();
    post_dom.compute(function);

    if dep_blocks
        .iter()
        .any(|&block| !dom.is_reachable(block) || !post_dom.is_reachable(block))
    {
        return None;
    }

    let entry_block = nearest_common_dominator(&dom, &dep_blocks)?;
    if !dep_blocks
        .iter()
        .all(|&block| dom.dominates(entry_block, block))
    {
        return None;
    }

    let enter = earliest_point_in_block(&dep_points, entry_block)?;
    let exits = match nearest_common_postdominator(&post_dom, &dep_blocks)? {
        PostNode::Real(exit_block) if dom.dominates(entry_block, exit_block) => {
            vec![latest_point_in_block_or_entry(&dep_points, exit_block)]
        }
        PostNode::DummyExit(_) => {
            let mut return_blocks: Vec<BlockId> = dep_points
                .iter()
                .filter_map(|point| match point.point {
                    FrameInjectionPoint::AfterSite(FrameSite::PreInst(inst))
                        if function.dfg.is_return(inst) =>
                    {
                        Some(point.block)
                    }
                    _ => None,
                })
                .collect();
            return_blocks.sort_unstable_by_key(|block| block.as_u32());
            return_blocks.dedup();
            if return_blocks.is_empty()
                || return_blocks
                    .iter()
                    .any(|&block| !dom.dominates(entry_block, block))
            {
                return None;
            }
            return return_blocks
                .into_iter()
                .map(|block| latest_point_in_block(&dep_points, block))
                .collect::<Option<Vec<_>>>()
                .map(|exits| LazyFramePlan { enter, exits });
        }
        PostNode::Real(_) | PostNode::DummyEntry(_) => return None,
    };

    if exits.contains(&enter) {
        return None;
    }

    Some(LazyFramePlan { enter, exits })
}

fn compute_active_pre_insts(
    function: &Function,
    alloc: &dyn Allocator,
    plan: &LazyFramePlan,
) -> Option<FxHashSet<InstId>> {
    let mut cfg = ControlFlowGraph::default();
    cfg.compute(function);
    let entry_block = function.layout.entry_block()?;
    let mut active_at_entry: FxHashMap<BlockId, bool> = FxHashMap::default();
    active_at_entry.insert(entry_block, false);
    let mut worklist = vec![entry_block];
    let mut active_pre_insts = FxHashSet::default();
    let machine_isa = sonatina_ir::isa::evm::EvmMachine::new(function.dfg.ctx.triple);

    while let Some(block) = worklist.pop() {
        let mut active = *active_at_entry
            .get(&block)
            .unwrap_or_else(|| panic!("missing active state for block {}", block.as_u32()));
        apply_site_state(plan, FrameSite::BlockEntry(block), &mut active);

        for inst in function.layout.iter_inst(block) {
            let data = machine_isa.inst_set().resolve_inst(function.dfg.inst(inst));
            apply_site_state(plan, FrameSite::PreInst(inst), &mut active);

            match data {
                EvmMachineInstKind::Call(_) => {
                    if let Some((prefix, suffix, prefix_len)) =
                        split_call_actions(alloc.pre_inst(inst).clone())
                    {
                        apply_actions_state(
                            plan,
                            FrameSite::PreInst(inst),
                            &prefix,
                            0,
                            &mut active,
                        );
                        apply_actions_state(
                            plan,
                            FrameSite::PreInst(inst),
                            &suffix,
                            prefix_len,
                            &mut active,
                        );
                    } else {
                        apply_actions_state(
                            plan,
                            FrameSite::PreInst(inst),
                            alloc.pre_inst(inst),
                            0,
                            &mut active,
                        );
                    }
                }
                EvmMachineInstKind::BrTable(br) => {
                    for (case_idx, _) in br.table().iter().enumerate() {
                        let actions = alloc.br_table_case(inst, case_idx);
                        if fold_stack_actions(actions).iter().any(|action| {
                            matches!(
                                action,
                                Action::MemLoadFrameSlot(_) | Action::MemStoreFrameSlot(_)
                            )
                        }) {
                            return None;
                        }
                    }
                }
                _ => apply_actions_state(
                    plan,
                    FrameSite::PreInst(inst),
                    alloc.pre_inst(inst),
                    0,
                    &mut active,
                ),
            }

            apply_site_state(plan, FrameSite::Inst(inst), &mut active);
            if matches!(data, EvmMachineInstKind::Call(_)) && active {
                active_pre_insts.insert(inst);
            }
            apply_after_site_state(plan, FrameSite::Inst(inst), &mut active);

            apply_site_state(plan, FrameSite::PostInst(inst), &mut active);
            apply_actions_state(
                plan,
                FrameSite::PostInst(inst),
                alloc.post_inst(inst),
                0,
                &mut active,
            );
            apply_after_site_state(plan, FrameSite::PostInst(inst), &mut active);
        }

        for succ in cfg.succs_of(block) {
            let succ = *succ;
            if let Some(prev) = active_at_entry.get(&succ) {
                if *prev != active {
                    return None;
                }
            } else {
                active_at_entry.insert(succ, active);
                worklist.push(succ);
            }
        }
    }

    Some(active_pre_insts)
}

fn validate_lazy_frame_activity(
    function: &Function,
    alloc: &dyn Allocator,
    plan: &LazyFramePlan,
) -> Option<()> {
    let mut cfg = ControlFlowGraph::default();
    cfg.compute(function);
    let entry_block = function.layout.entry_block()?;
    let mut active_at_entry: FxHashMap<BlockId, bool> = FxHashMap::default();
    active_at_entry.insert(entry_block, false);
    let mut worklist = vec![entry_block];

    while let Some(block) = worklist.pop() {
        let mut active = *active_at_entry
            .get(&block)
            .unwrap_or_else(|| panic!("missing active state for block {}", block.as_u32()));
        apply_site_state(plan, FrameSite::BlockEntry(block), &mut active);

        for inst in function.layout.iter_inst(block) {
            apply_site_state(plan, FrameSite::PreInst(inst), &mut active);

            if let Some((prefix, suffix, prefix_len)) =
                split_call_actions(alloc.pre_inst(inst).clone())
            {
                apply_actions_state(plan, FrameSite::PreInst(inst), &prefix, 0, &mut active);
                apply_actions_state(
                    plan,
                    FrameSite::PreInst(inst),
                    &suffix,
                    prefix_len,
                    &mut active,
                );
            } else {
                apply_actions_state(
                    plan,
                    FrameSite::PreInst(inst),
                    alloc.pre_inst(inst),
                    0,
                    &mut active,
                );
            }

            apply_site_state(plan, FrameSite::Inst(inst), &mut active);
            apply_after_site_state(plan, FrameSite::Inst(inst), &mut active);

            apply_site_state(plan, FrameSite::PostInst(inst), &mut active);
            apply_actions_state(
                plan,
                FrameSite::PostInst(inst),
                alloc.post_inst(inst),
                0,
                &mut active,
            );
            apply_after_site_state(plan, FrameSite::PostInst(inst), &mut active);
        }

        for succ in cfg.succs_of(block) {
            let succ = *succ;
            if let Some(prev) = active_at_entry.get(&succ) {
                if *prev != active {
                    return None;
                }
            } else {
                active_at_entry.insert(succ, active);
                worklist.push(succ);
            }
        }
    }

    Some(())
}

fn split_call_actions(
    mut actions: smallvec::SmallVec<[Action; 2]>,
) -> Option<(Vec<Action>, Vec<Action>, usize)> {
    let cont_pos = actions
        .iter()
        .position(|action| matches!(action, Action::PushContinuationOffset))?;
    let suffix: Vec<Action> = actions.drain(cont_pos + 1..).collect();
    let marker = actions.remove(cont_pos);
    debug_assert_eq!(marker, Action::PushContinuationOffset);
    let prefix = actions.into_iter().collect::<Vec<_>>();
    let prefix_len = fold_stack_actions(&prefix).len();
    Some((prefix, suffix, prefix_len))
}

fn apply_site_state(plan: &LazyFramePlan, site: FrameSite, active: &mut bool) {
    if plan.enter_before_site(site) {
        *active = true;
    }
    if plan.exit_before_site(site) {
        *active = false;
    }
}

fn apply_after_site_state(plan: &LazyFramePlan, site: FrameSite, active: &mut bool) {
    if plan.exit_after_site(site) {
        *active = false;
    }
}

fn apply_actions_state(
    plan: &LazyFramePlan,
    site: FrameSite,
    actions: &[Action],
    action_index_offset: usize,
    active: &mut bool,
) {
    for (index, _) in fold_stack_actions(actions).iter().enumerate() {
        let index = action_index_offset
            .checked_add(index)
            .expect("lazy frame action index overflow");
        if plan.enter_before_action(site, index) {
            *active = true;
        }
        if plan.exit_before_action(site, index) {
            *active = false;
        }
        if plan.exit_after_action(site, index) {
            *active = false;
        }
    }
}

fn collect_dep_points(
    function: &Function,
    cfg: &ControlFlowGraph,
    alloc: &dyn Allocator,
    roots: &MachineFrameRoots,
) -> Option<Vec<DepPoint>> {
    let reachable_returns = compute_reachable_returns(function, cfg);
    let order = PointOrderTable::new(function)?;
    let root_use = RootUseDepCtx {
        reachable_returns: &reachable_returns,
        rooted: &roots.rooted_values,
        order: &order,
    };
    let mut out = Vec::new();
    let mut seen = FxHashSet::default();

    let entry_block = function.layout.entry_block()?;
    collect_action_dep_points(
        &mut out,
        &mut seen,
        &order,
        entry_block,
        FrameSite::EnterFunction,
        &alloc.enter_function(function),
        0,
    );

    let machine_isa = sonatina_ir::isa::evm::EvmMachine::new(function.dfg.ctx.triple);
    for block in function.layout.iter_block() {
        for inst in function.layout.iter_inst(block) {
            let data = machine_isa.inst_set().resolve_inst(function.dfg.inst(inst));

            match &data {
                EvmMachineInstKind::Call(_) => {
                    if let Some((prefix, suffix, prefix_len)) =
                        split_call_actions(alloc.pre_inst(inst).clone())
                    {
                        collect_action_dep_points(
                            &mut out,
                            &mut seen,
                            &order,
                            block,
                            FrameSite::PreInst(inst),
                            &prefix,
                            0,
                        );
                        collect_action_dep_points(
                            &mut out,
                            &mut seen,
                            &order,
                            block,
                            FrameSite::PreInst(inst),
                            &suffix,
                            prefix_len,
                        );
                    } else {
                        collect_action_dep_points(
                            &mut out,
                            &mut seen,
                            &order,
                            block,
                            FrameSite::PreInst(inst),
                            alloc.pre_inst(inst),
                            0,
                        );
                    }
                }
                EvmMachineInstKind::BrTable(br) => {
                    for (case_idx, _) in br.table().iter().enumerate() {
                        let actions = alloc.br_table_case(inst, case_idx);
                        if fold_stack_actions(actions).iter().any(|action| {
                            matches!(
                                action,
                                Action::MemLoadFrameSlot(_) | Action::MemStoreFrameSlot(_)
                            )
                        }) {
                            return None;
                        }
                    }
                }
                _ => collect_action_dep_points(
                    &mut out,
                    &mut seen,
                    &order,
                    block,
                    FrameSite::PreInst(inst),
                    alloc.pre_inst(inst),
                    0,
                ),
            }

            if roots.root_def_insts.contains(&inst) {
                push_dep_point(
                    &mut out,
                    &mut seen,
                    &order,
                    block,
                    FrameInjectionPoint::BeforeSite(FrameSite::PreInst(inst)),
                );
            }

            collect_root_use_dep_points(
                function, &root_use, block, inst, &data, &mut out, &mut seen,
            );

            collect_action_dep_points(
                &mut out,
                &mut seen,
                &order,
                block,
                FrameSite::PostInst(inst),
                alloc.post_inst(inst),
                0,
            );
        }
    }
    Some(out)
}

fn compute_source_rooted_frame_values(
    function: &Function,
    alloca_loc: &FxHashMap<InstId, ObjLoc>,
    isa: &Evm,
) -> FxHashSet<ValueId> {
    let mut rooted = FxHashSet::default();
    for (&inst, &loc) in alloca_loc {
        if matches!(loc, ObjLoc::StableFrame(_))
            && let Some(result) = function.dfg.inst_result(inst)
        {
            rooted.insert(result);
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for block in function.layout.iter_block() {
            for inst in function.layout.iter_inst(block) {
                let newly_rooted = if function.dfg.is_phi(inst) {
                    let phi = function.dfg.cast_phi(inst).expect("phi downcast failed");
                    phi.args().iter().any(|(value, _)| rooted.contains(value))
                } else {
                    let data = isa.inst_set().resolve_inst(function.dfg.inst(inst));
                    match data {
                        EvmInstKind::Bitcast(bitcast) => rooted.contains(bitcast.from()),
                        EvmInstKind::IntToPtr(int_to_ptr) => {
                            rooted.contains(int_to_ptr.from())
                                && scalar_bit_width(
                                    function.dfg.value_ty(*int_to_ptr.from()),
                                    &function.dfg.ctx,
                                ) == Some(256)
                        }
                        EvmInstKind::PtrToInt(ptr_to_int) => {
                            rooted.contains(ptr_to_int.from())
                                && scalar_bit_width(*ptr_to_int.ty(), &function.dfg.ctx)
                                    == Some(256)
                        }
                        EvmInstKind::Gep(gep) => gep
                            .values()
                            .first()
                            .is_some_and(|value| rooted.contains(value)),
                        _ => false,
                    }
                };

                if newly_rooted {
                    for &result in function.dfg.inst_results(inst) {
                        changed |= rooted.insert(result);
                    }
                }
            }
        }
    }

    rooted
}

fn collect_root_use_dep_points(
    function: &Function,
    root_use: &RootUseDepCtx<'_>,
    block: BlockId,
    inst: InstId,
    data: &EvmMachineInstKind,
    out: &mut Vec<DepPoint>,
    seen: &mut FxHashSet<FrameInjectionPoint>,
) {
    let rooted_operands: FxHashSet<ValueId> = function
        .dfg
        .inst(inst)
        .collect_values()
        .into_iter()
        .filter(|value| root_use.rooted.contains(value))
        .collect();
    if rooted_operands.is_empty() || is_alias_preserving_root_use(function, inst, data) {
        return;
    }

    if !function.dfg.is_return(inst) {
        push_dep_point(
            out,
            seen,
            root_use.order,
            block,
            FrameInjectionPoint::BeforeSite(FrameSite::PostInst(inst)),
        );
    }

    if is_escape_like_root_use(function, inst, data, &rooted_operands) {
        for &(ret_block, ret_inst) in root_use.reachable_returns.get(&block).into_iter().flatten() {
            push_dep_point(
                out,
                seen,
                root_use.order,
                ret_block,
                FrameInjectionPoint::AfterSite(FrameSite::PreInst(ret_inst)),
            );
        }
    }
}

fn is_alias_preserving_root_use(
    function: &Function,
    inst: InstId,
    data: &EvmMachineInstKind,
) -> bool {
    function.dfg.is_phi(inst)
        || matches!(
            data,
            EvmMachineInstKind::Add(_) | EvmMachineInstKind::Sub(_)
        )
}

fn is_escape_like_root_use(
    function: &Function,
    inst: InstId,
    data: &EvmMachineInstKind,
    rooted_operands: &FxHashSet<ValueId>,
) -> bool {
    if function.dfg.is_return(inst) {
        return true;
    }

    match data {
        EvmMachineInstKind::Call(call) => call
            .args()
            .iter()
            .any(|value| rooted_operands.contains(value)),
        EvmMachineInstKind::EvmMstore(mstore) => rooted_operands.contains(mstore.value()),
        EvmMachineInstKind::EvmMstore8(mstore8) => rooted_operands.contains(mstore8.val()),
        EvmMachineInstKind::EvmSstore(sstore) => rooted_operands.contains(sstore.val()),
        EvmMachineInstKind::EvmTstore(tstore) => rooted_operands.contains(tstore.val()),
        _ => function.dfg.may_write_memory(inst),
    }
}

fn compute_reachable_returns(
    function: &Function,
    cfg: &ControlFlowGraph,
) -> FxHashMap<BlockId, Vec<(BlockId, InstId)>> {
    let mut out: FxHashMap<BlockId, Vec<(BlockId, InstId)>> = FxHashMap::default();
    for block in function.layout.iter_block() {
        let mut seen: FxHashSet<BlockId> = FxHashSet::default();
        let mut worklist = vec![block];
        let mut returns = Vec::new();
        while let Some(cur) = worklist.pop() {
            if !seen.insert(cur) {
                continue;
            }
            if let Some(term) = function.layout.last_inst_of(cur)
                && function.dfg.is_return(term)
            {
                returns.push((cur, term));
                continue;
            }
            for succ in cfg.succs_of(cur) {
                worklist.push(*succ);
            }
        }
        returns
            .sort_unstable_by_key(|(ret_block, ret_inst)| (ret_block.as_u32(), ret_inst.as_u32()));
        out.insert(block, returns);
    }
    out
}

fn collect_action_dep_points(
    out: &mut Vec<DepPoint>,
    seen: &mut FxHashSet<FrameInjectionPoint>,
    order: &PointOrderTable,
    block: BlockId,
    site: FrameSite,
    actions: &[Action],
    action_index_offset: usize,
) {
    let folded = fold_stack_actions(actions);
    for (index, action) in folded.iter().enumerate() {
        if matches!(
            action,
            Action::MemLoadFrameSlot(_)
                | Action::MemStoreFrameSlot(_)
                | Action::PushFrameAddr { .. }
        ) {
            push_dep_point(
                out,
                seen,
                order,
                block,
                FrameInjectionPoint::BeforeAction {
                    site,
                    action_index: action_index_offset
                        .checked_add(index)
                        .expect("frame action index overflow"),
                },
            );
        }
    }
}

fn push_dep_point(
    out: &mut Vec<DepPoint>,
    seen: &mut FxHashSet<FrameInjectionPoint>,
    order: &PointOrderTable,
    block: BlockId,
    point: FrameInjectionPoint,
) {
    if !seen.insert(point) {
        return;
    }
    out.push(DepPoint {
        block,
        order: order.key(block, point),
        point,
    });
}

fn earliest_point_in_block(points: &[DepPoint], block: BlockId) -> Option<FrameInjectionPoint> {
    points
        .iter()
        .filter(|point| point.block == block)
        .min_by_key(|point| point.order)
        .map(|point| point.point)
}

fn latest_point_in_block(points: &[DepPoint], block: BlockId) -> Option<FrameInjectionPoint> {
    points
        .iter()
        .filter(|point| point.block == block)
        .max_by_key(|point| point.order)
        .map(|point| point.point)
}

fn latest_point_in_block_or_entry(points: &[DepPoint], block: BlockId) -> FrameInjectionPoint {
    latest_point_in_block(points, block).unwrap_or(FrameInjectionPoint::BeforeSite(
        FrameSite::BlockEntry(block),
    ))
}

impl PointOrderTable {
    fn new(function: &Function) -> Option<Self> {
        let entry_block = function.layout.entry_block()?;
        let mut inst_order = FxHashMap::default();
        for block in function.layout.iter_block() {
            for (index, inst) in function.layout.iter_inst(block).enumerate() {
                inst_order.insert(
                    inst,
                    u32::try_from(index).expect("instruction order overflow"),
                );
            }
        }
        Some(Self {
            entry_block,
            inst_order,
        })
    }

    fn key(&self, block: BlockId, point: FrameInjectionPoint) -> PointOrder {
        let (site, phase_rank, action_rank) = match point {
            FrameInjectionPoint::BeforeSite(site) => (site, 0, 0),
            FrameInjectionPoint::BeforeAction { site, action_index } => (
                site,
                1,
                u32::try_from(action_index)
                    .expect("action index overflow")
                    .checked_mul(2)
                    .expect("action index overflow"),
            ),
            FrameInjectionPoint::AfterAction { site, action_index } => (
                site,
                1,
                u32::try_from(action_index)
                    .expect("action index overflow")
                    .checked_mul(2)
                    .and_then(|rank| rank.checked_add(1))
                    .expect("action index overflow"),
            ),
            FrameInjectionPoint::AfterSite(site) => (site, 2, 0),
        };

        PointOrder {
            site_rank: self.site_rank(block, site),
            phase_rank,
            action_rank,
        }
    }

    fn site_rank(&self, block: BlockId, site: FrameSite) -> u32 {
        let site_base = if block == self.entry_block { 1 } else { 0 };
        match site {
            FrameSite::EnterFunction => {
                debug_assert_eq!(
                    block, self.entry_block,
                    "enter_function site on non-entry block"
                );
                0
            }
            FrameSite::BlockEntry(site_block) => {
                debug_assert_eq!(block, site_block, "block-entry site on wrong block");
                site_base
            }
            FrameSite::PreInst(inst) => self.inst_site_rank(inst, site_base, 0),
            FrameSite::Inst(inst) => self.inst_site_rank(inst, site_base, 1),
            FrameSite::PostInst(inst) => self.inst_site_rank(inst, site_base, 2),
        }
    }

    fn inst_site_rank(&self, inst: InstId, site_base: u32, offset: u32) -> u32 {
        let inst_rank = self
            .inst_order
            .get(&inst)
            .copied()
            .expect("missing instruction order");
        site_base
            .checked_add(1)
            .and_then(|rank| {
                rank.checked_add(inst_rank.checked_mul(3).expect("site rank overflow"))
            })
            .and_then(|rank| rank.checked_add(offset))
            .expect("site rank overflow")
    }
}

fn nearest_common_dominator(dom: &DomTree, blocks: &[BlockId]) -> Option<BlockId> {
    let &first = blocks.first()?;
    dom_chain(dom, first)
        .into_iter()
        .find(|&cand| blocks.iter().all(|&block| dom.dominates(cand, block)))
}

fn dom_chain(dom: &DomTree, mut block: BlockId) -> Vec<BlockId> {
    let mut out = vec![block];
    while let Some(idom) = dom.idom_of(block) {
        out.push(idom);
        block = idom;
    }
    out
}

fn nearest_common_postdominator(post_dom: &PostDomTree, blocks: &[BlockId]) -> Option<PostNode> {
    let &first = blocks.first()?;
    let first_chain = postdom_chain(post_dom, first);
    let other_chains: Vec<FxHashSet<PostNode>> = blocks
        .iter()
        .copied()
        .skip(1)
        .map(|block| postdom_chain(post_dom, block).into_iter().collect())
        .collect();
    first_chain
        .into_iter()
        .find(|cand| other_chains.iter().all(|chain| chain.contains(cand)))
}

fn postdom_chain(post_dom: &PostDomTree, block: BlockId) -> Vec<PostNode> {
    let mut out = vec![PostNode::Real(block)];
    let mut cur = block;
    while let Some(idom) = post_dom.idom_of(cur) {
        let node = match idom {
            PDTIdom::Real(next) => {
                cur = next;
                PostNode::Real(next)
            }
            PDTIdom::DummyExit(dummy) => PostNode::DummyExit(dummy),
            PDTIdom::DummyEntry(dummy) => PostNode::DummyEntry(dummy),
        };
        out.push(node);
        if !matches!(node, PostNode::Real(_)) {
            break;
        }
    }
    out
}

fn scalar_bit_width(ty: Type, module: &sonatina_ir::module::ModuleCtx) -> Option<u16> {
    let bits = match ty {
        Type::I1 => 1,
        Type::I8 => 8,
        Type::I16 => 16,
        Type::I32 => 32,
        Type::I64 => 64,
        Type::I128 => 128,
        Type::I256 => 256,
        Type::EnumTag(_) => return None,
        Type::Unit => 0,
        Type::Compound(_) if ty.is_pointer(module) => 256,
        Type::Compound(_) => return None,
    };
    Some(bits)
}
