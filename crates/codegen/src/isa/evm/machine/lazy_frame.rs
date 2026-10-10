use cranelift_entity::SecondaryMap;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_ir::{
    BlockId, Function, InstId, InstSetExt, ValueId, cfg::ControlFlowGraph,
    inst::evm::machine_inst_set::EvmMachineInstKind, isa::Isa,
};

use crate::{
    domtree::DomTree,
    post_domtree::{PDTIdom, PostDomTree},
    stackalloc::{Action, Allocator},
};

use super::module::FuncMachineMap;
use crate::isa::evm::{
    MachineFuncPlan, ObjLoc, emit::fold_stack_actions, ptr_provenance::Provenance,
};

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

/// A stretch of lowered code that needs the dynamic frame: the frame must be
/// entered no later than `enter` and left no earlier than `exit`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct DepPoint {
    block: BlockId,
    enter: OrderedPoint,
    exit: OrderedPoint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct OrderedPoint {
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

/// Roots every machine value that may address a dynamic-frame alloca. Pointer
/// provenance follows frame addresses through casts, arithmetic, memory, and
/// calls, so every later access through one keeps the frame entered.
pub(crate) fn compute_machine_frame_roots(
    machine: &Function,
    map: &FuncMachineMap,
    alloca_loc: &FxHashMap<InstId, ObjLoc>,
    prov: &SecondaryMap<ValueId, Provenance>,
) -> MachineFrameRoots {
    let mut roots = MachineFrameRoots::default();
    for (source_value, prov) in prov.iter() {
        if let Some(machine_value) = map.values[source_value]
            && prov
                .alloca_insts()
                .any(|alloca| matches!(alloca_loc.get(&alloca), Some(ObjLoc::StableFrame(_))))
        {
            roots.rooted_values.insert(machine_value);
        }
    }

    // A root's definition needs the frame only where it materializes the frame
    // address: through other roots and machine-only values such as the dynamic
    // SP read. Other lowered source values, like a gas reading added to the
    // address, don't.
    let lowered: FxHashSet<ValueId> = map.values.values().flatten().copied().collect();
    let mut work: Vec<ValueId> = roots.rooted_values.iter().copied().collect();
    while let Some(value) = work.pop() {
        if let Some(inst) = machine.dfg.value_inst(value)
            && machine.layout.try_inst_block(inst).is_some()
            && roots.root_def_insts.insert(inst)
        {
            work.extend(
                machine
                    .dfg
                    .inst(inst)
                    .collect_values()
                    .into_iter()
                    .filter(|operand| {
                        roots.rooted_values.contains(operand) || !lowered.contains(operand)
                    }),
            );
        }
    }
    roots
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
            // Every return reached with the frame active must restore the caller's SP,
            // including paths with no frame dependency of their own.
            let mut return_blocks: Vec<BlockId> = cfg
                .post_order()
                .filter_map(|block| {
                    let term = function.layout.last_inst_of(block)?;
                    (function.dfg.is_return(term) && dom.dominates(entry_block, block))
                        .then_some(block)
                })
                .collect();
            return_blocks.sort_unstable_by_key(|block| block.as_u32());
            if return_blocks.is_empty() {
                return None;
            }
            return_blocks
                .into_iter()
                .map(|block| latest_point_in_block_or_entry(&dep_points, block))
                .collect()
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
    let mut entry_active = false;
    apply_enter_function_state(function, alloc, plan, &mut entry_active);
    let mut active_at_entry: FxHashMap<BlockId, bool> = FxHashMap::default();
    active_at_entry.insert(entry_block, entry_active);
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
                    // Emit replays `FrameSite::PreInst` from action index 0 for the base
                    // pre-actions *and* again for every case's compare prep, so an injection
                    // point planned inside the base actions would fire once per case. Bail to
                    // the always-active frame whenever the base actions touch the frame, exactly
                    // as for frame actions inside a case.
                    if actions_touch_frame(alloc.pre_inst(inst)) {
                        return None;
                    }
                    apply_actions_state(
                        plan,
                        FrameSite::PreInst(inst),
                        alloc.pre_inst(inst),
                        0,
                        &mut active,
                    );
                    for (case_idx, _) in br.table().iter().enumerate() {
                        let actions = alloc.br_table_case(inst, case_idx);
                        if actions_touch_frame(actions) {
                            return None;
                        }
                    }
                }
                _ => {
                    apply_actions_state(
                        plan,
                        FrameSite::PreInst(inst),
                        alloc.pre_inst(inst),
                        0,
                        &mut active,
                    );
                }
            }

            apply_after_site_state(plan, FrameSite::PreInst(inst), &mut active);
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
    let mut entry_active = false;
    let mut covered = apply_enter_function_state(function, alloc, plan, &mut entry_active);
    let mut active_at_entry: FxHashMap<BlockId, bool> = FxHashMap::default();
    active_at_entry.insert(entry_block, entry_active);
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
                covered &=
                    apply_actions_state(plan, FrameSite::PreInst(inst), &prefix, 0, &mut active);
                covered &= apply_actions_state(
                    plan,
                    FrameSite::PreInst(inst),
                    &suffix,
                    prefix_len,
                    &mut active,
                );
            } else {
                covered &= apply_actions_state(
                    plan,
                    FrameSite::PreInst(inst),
                    alloc.pre_inst(inst),
                    0,
                    &mut active,
                );
            }

            apply_after_site_state(plan, FrameSite::PreInst(inst), &mut active);
            apply_site_state(plan, FrameSite::Inst(inst), &mut active);
            if function.dfg.is_return(inst) && active {
                return None;
            }
            apply_after_site_state(plan, FrameSite::Inst(inst), &mut active);

            apply_site_state(plan, FrameSite::PostInst(inst), &mut active);
            covered &= apply_actions_state(
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

    // Every frame slot access must run inside the frame; otherwise it would
    // address the caller's frame through the restored dynamic SP.
    covered.then_some(())
}

/// Applies the plan's transitions for the function prologue, returning whether
/// its frame-touching actions run while the frame is active.
fn apply_enter_function_state(
    function: &Function,
    alloc: &dyn Allocator,
    plan: &LazyFramePlan,
    active: &mut bool,
) -> bool {
    apply_site_state(plan, FrameSite::EnterFunction, active);
    let covered = apply_actions_state(
        plan,
        FrameSite::EnterFunction,
        &alloc.enter_function(function),
        0,
        active,
    );
    apply_after_site_state(plan, FrameSite::EnterFunction, active);
    covered
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

/// Applies the plan's transitions around `actions`, returning whether every
/// frame-touching action runs while the frame is active.
fn apply_actions_state(
    plan: &LazyFramePlan,
    site: FrameSite,
    actions: &[Action],
    action_index_offset: usize,
    active: &mut bool,
) -> bool {
    let mut covered = true;
    for (index, action) in fold_stack_actions(actions).iter().enumerate() {
        let index = action_index_offset
            .checked_add(index)
            .expect("lazy frame action index overflow");
        if plan.enter_before_action(site, index) {
            *active = true;
        }
        covered &= *active || !action_touches_frame(action);
        if plan.exit_after_action(site, index) {
            *active = false;
        }
    }
    covered
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
                    // See `compute_active_pre_insts`: base pre-actions that touch the frame make
                    // the lazy plan invalid, because emit replays their action indexes per case.
                    if actions_touch_frame(alloc.pre_inst(inst)) {
                        return None;
                    }
                    collect_action_dep_points(
                        &mut out,
                        &mut seen,
                        &order,
                        block,
                        FrameSite::PreInst(inst),
                        alloc.pre_inst(inst),
                        0,
                    );
                    for (case_idx, _) in br.table().iter().enumerate() {
                        let actions = alloc.br_table_case(inst, case_idx);
                        if actions_touch_frame(actions) {
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
                    FrameInjectionPoint::BeforeSite(FrameSite::PostInst(inst)),
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

fn collect_root_use_dep_points(
    function: &Function,
    root_use: &RootUseDepCtx<'_>,
    block: BlockId,
    inst: InstId,
    data: &EvmMachineInstKind,
    out: &mut Vec<DepPoint>,
    seen: &mut FxHashSet<(FrameInjectionPoint, FrameInjectionPoint)>,
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
            FrameInjectionPoint::BeforeSite(FrameSite::PreInst(inst)),
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
                FrameInjectionPoint::BeforeSite(FrameSite::PreInst(ret_inst)),
                FrameInjectionPoint::AfterSite(FrameSite::PreInst(ret_inst)),
            );
        }
    }
}

/// These uses need no frame themselves: their results are rooted too (or, for
/// lowered geps, feed a rooted result), so the accesses through them carry the
/// dependency.
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
    seen: &mut FxHashSet<(FrameInjectionPoint, FrameInjectionPoint)>,
    order: &PointOrderTable,
    block: BlockId,
    site: FrameSite,
    actions: &[Action],
    action_index_offset: usize,
) {
    let folded = fold_stack_actions(actions);
    for (index, action) in folded.iter().enumerate() {
        if action_touches_frame(action) {
            let action_index = action_index_offset
                .checked_add(index)
                .expect("frame action index overflow");
            push_dep_point(
                out,
                seen,
                order,
                block,
                FrameInjectionPoint::BeforeAction { site, action_index },
                FrameInjectionPoint::AfterAction { site, action_index },
            );
        }
    }
}

/// Frame slot accesses address the frame through the current dynamic SP, so
/// they must run while the frame is entered.
fn action_touches_frame(action: &Action) -> bool {
    matches!(
        action,
        Action::MemLoadFrameSlot(_) | Action::MemStoreFrameSlot(_) | Action::PushFrameAddr { .. }
    )
}

fn actions_touch_frame(actions: &[Action]) -> bool {
    fold_stack_actions(actions).iter().any(action_touches_frame)
}

fn push_dep_point(
    out: &mut Vec<DepPoint>,
    seen: &mut FxHashSet<(FrameInjectionPoint, FrameInjectionPoint)>,
    order: &PointOrderTable,
    block: BlockId,
    enter: FrameInjectionPoint,
    exit: FrameInjectionPoint,
) {
    if !seen.insert((enter, exit)) {
        return;
    }
    let ordered = |point| OrderedPoint {
        order: order.key(block, point),
        point,
    };
    out.push(DepPoint {
        block,
        enter: ordered(enter),
        exit: ordered(exit),
    });
}

fn earliest_point_in_block(points: &[DepPoint], block: BlockId) -> Option<FrameInjectionPoint> {
    points
        .iter()
        .filter(|point| point.block == block)
        .map(|point| point.enter)
        .min_by_key(|enter| enter.order)
        .map(|enter| enter.point)
}

fn latest_point_in_block(points: &[DepPoint], block: BlockId) -> Option<FrameInjectionPoint> {
    points
        .iter()
        .filter(|point| point.block == block)
        .map(|point| point.exit)
        .max_by_key(|exit| exit.order)
        .map(|exit| exit.point)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{isa::evm::memory_plan::StableMode, stackalloc::Actions};
    use cranelift_entity::SecondaryMap;
    use sonatina_parser::parse_module;

    #[derive(Default)]
    struct TestAlloc {
        enter: Actions,
        pre: SecondaryMap<InstId, Actions>,
        post: SecondaryMap<InstId, Actions>,
        cases: SecondaryMap<InstId, Vec<Actions>>,
    }

    impl TestAlloc {
        fn for_function(function: &Function) -> Self {
            let mut alloc = Self::default();
            for block in function.layout.iter_block() {
                for inst in function.layout.iter_inst(block) {
                    let _ = &mut alloc.pre[inst];
                    let _ = &mut alloc.post[inst];
                }
            }
            alloc
        }
    }

    impl Allocator for TestAlloc {
        fn enter_function(&self, _function: &Function) -> Actions {
            self.enter.clone()
        }

        fn pre_inst(&self, inst: InstId) -> &Actions {
            &self.pre[inst]
        }

        fn post_inst(&self, inst: InstId) -> &Actions {
            &self.post[inst]
        }

        fn br_table_case(&self, inst: InstId, case_index: usize) -> &Actions {
            &self.cases[inst][case_index]
        }
    }

    /// `block2` stores a frame slot and reloads it, then returns.
    fn frame_slot_round_trip() -> (sonatina_parser::ParsedModule, [InstId; 2]) {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1, v1.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    return 0.i256;

block2:
    v2.i256 = add v1 1.i256;
    v3.i256 = add v2 2.i256;
    return v3;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];
        let insts = parsed.module.func_store.view(func_ref, |function| {
            let inst = |name| {
                let value = parsed.debug.value(func_ref, name).expect("value exists");
                function
                    .dfg
                    .value_inst(value)
                    .expect("value should be instruction-defined")
            };
            [inst("v2"), inst("v3")]
        });
        (parsed, insts)
    }

    #[test]
    fn lazy_frame_exit_follows_the_last_frame_slot_access() {
        let (parsed, [store_inst, load_inst]) = frame_slot_round_trip();
        let func_ref = parsed.debug.func_order[0];
        parsed.module.func_store.view(func_ref, |function| {
            let mut alloc = TestAlloc::for_function(function);
            alloc.pre[store_inst].push(Action::MemStoreFrameSlot(0));
            alloc.pre[load_inst].push(Action::MemLoadFrameSlot(0));

            let plan =
                compute_lazy_frame_plan_inner(function, &alloc, &MachineFrameRoots::default())
                    .expect("frame slot accesses should produce a lazy frame plan");
            assert!(plan.enter_before_action(FrameSite::PreInst(store_inst), 0));
            assert_eq!(
                plan.exits,
                vec![FrameInjectionPoint::AfterAction {
                    site: FrameSite::PreInst(load_inst),
                    action_index: 0,
                }],
                "the frame must be left after the final reload, not before it"
            );
            assert!(validate_lazy_frame_activity(function, &alloc, &plan).is_some());
        });
    }

    #[test]
    fn lazy_frame_validation_rejects_frame_slot_access_after_exit() {
        let (parsed, [store_inst, load_inst]) = frame_slot_round_trip();
        let func_ref = parsed.debug.func_order[0];
        parsed.module.func_store.view(func_ref, |function| {
            let mut alloc = TestAlloc::for_function(function);
            alloc.pre[store_inst].push(Action::MemStoreFrameSlot(0));
            alloc.pre[load_inst].push(Action::MemLoadFrameSlot(0));

            let plan = LazyFramePlan {
                enter: FrameInjectionPoint::BeforeAction {
                    site: FrameSite::PreInst(store_inst),
                    action_index: 0,
                },
                exits: vec![FrameInjectionPoint::BeforeSite(FrameSite::PreInst(
                    load_inst,
                ))],
            };
            assert!(validate_lazy_frame_activity(function, &alloc, &plan).is_none());
        });
    }

    #[test]
    fn lazy_frame_plan_exits_on_returns_without_frame_dependencies() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i1, v1.i1, v2.i256) -> i256 {
block0:
    br v0 block1 block2;

block1:
    return 0.i256;

block2:
    v3.i256 = add v2 1.i256;
    br v1 block3 block4;

block3:
    return 0.i256;

block4:
    evm_mstore 0.i256 v3;
    return 1.i256;
}
"#;

        for (shared_return, prologue_spill) in [(false, false), (true, false), (false, true)] {
            let source = if shared_return {
                SRC.replace("block3:\n    return 0.i256;", "block3:\n    jump block1;")
            } else {
                SRC.to_owned()
            };
            let parsed = parse_module(&source).expect("module parses");
            let func_ref = parsed.debug.func_order[0];
            parsed.module.func_store.view(func_ref, |function| {
                let root = parsed.debug.value(func_ref, "v3").expect("v3 exists");
                let root_def = function.dfg.value_inst(root).expect("root is defined");
                let mut roots = MachineFrameRoots::default();
                roots.root_def_insts.insert(root_def);
                roots.rooted_values.insert(root);
                let returns: Vec<_> = function
                    .layout
                    .iter_block()
                    .filter(|&block| {
                        function
                            .layout
                            .last_inst_of(block)
                            .is_some_and(|inst| function.dfg.is_return(inst))
                    })
                    .collect();
                let mut alloc = TestAlloc::for_function(function);
                if prologue_spill {
                    alloc.enter.push(Action::MemStoreFrameSlot(0));
                    let ret = function.layout.last_inst_of(returns[0]).unwrap();
                    alloc.pre[ret].push(Action::MemLoadFrameSlot(0));
                }
                let plan = compute_lazy_frame_plan_inner(function, &alloc, &roots)
                    .expect("escaping root should produce a lazy frame plan");
                let escape_ret = function
                    .layout
                    .last_inst_of(*returns.last().unwrap())
                    .unwrap();
                assert!(plan.exit_after_site(FrameSite::PreInst(escape_ret)));
                if !shared_return {
                    assert_eq!(plan.exits.len(), if prologue_spill { 3 } else { 2 });
                    assert!(!plan.exit_before_site(FrameSite::BlockEntry(returns[0])));
                    assert!(plan.exit_before_site(FrameSite::BlockEntry(returns[1])));
                }
                assert_eq!(
                    validate_lazy_frame_activity(function, &alloc, &plan).is_none(),
                    shared_return
                );
                let mem_plan = MachineFuncPlan {
                    arena_base: 0xa0,
                    scratch_words: 0,
                    stable_words: 1,
                    stable_mode: StableMode::DynamicFrame,
                    entry_abs_words: 0,
                    obj_loc: FxHashMap::default(),
                    alloca_loc: FxHashMap::default(),
                    spill_obj: SecondaryMap::new(),
                    call_preserve: FxHashMap::default(),
                };
                let summary = compute_frame_summary(function, &alloc, &mem_plan, &roots);
                assert_eq!(summary.lowering.is_none(), shared_return);
                assert_eq!(summary.full_body_active, shared_return);
                if prologue_spill {
                    assert!(plan.enter_before_action(FrameSite::EnterFunction, 0));
                }
            });
        }
    }

    #[test]
    fn lazy_frame_validation_requires_an_exit_before_return() {
        let (parsed, [store_inst, load_inst]) = frame_slot_round_trip();
        let func_ref = parsed.debug.func_order[0];
        parsed.module.func_store.view(func_ref, |function| {
            let mut alloc = TestAlloc::for_function(function);
            alloc.pre[store_inst].push(Action::MemStoreFrameSlot(0));
            alloc.pre[load_inst].push(Action::MemLoadFrameSlot(0));
            let mut plan = LazyFramePlan {
                enter: FrameInjectionPoint::BeforeAction {
                    site: FrameSite::PreInst(store_inst),
                    action_index: 0,
                },
                exits: Vec::new(),
            };
            assert!(validate_lazy_frame_activity(function, &alloc, &plan).is_none());

            let ret = function
                .layout
                .last_inst_of(function.layout.inst_block(load_inst))
                .expect("return exists");
            plan.exits
                .push(FrameInjectionPoint::AfterSite(FrameSite::PreInst(ret)));
            assert!(validate_lazy_frame_activity(function, &alloc, &plan).is_some());
        });
    }

    #[test]
    fn lazy_frame_plan_enters_in_the_prologue_for_entry_block_dependencies() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %f(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 1.i256;
    return v1;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];
        parsed.module.func_store.view(func_ref, |function| {
            let value = parsed.debug.value(func_ref, "v1").expect("v1 exists");
            let load_inst = function
                .dfg
                .value_inst(value)
                .expect("v1 should be instruction-defined");
            // The argument is spilled to the frame in the prologue and reloaded
            // in the entry block.
            let mut alloc = TestAlloc::for_function(function);
            alloc.enter.push(Action::MemStoreFrameSlot(0));
            alloc.pre[load_inst].push(Action::MemLoadFrameSlot(0));

            let plan =
                compute_lazy_frame_plan_inner(function, &alloc, &MachineFrameRoots::default())
                    .expect("entry-block frame accesses should produce a lazy frame plan");
            assert!(plan.enter_before_action(FrameSite::EnterFunction, 0));
            assert_eq!(
                plan.exits,
                vec![FrameInjectionPoint::AfterAction {
                    site: FrameSite::PreInst(load_inst),
                    action_index: 0,
                }]
            );
            assert!(
                validate_lazy_frame_activity(function, &alloc, &plan).is_some(),
                "an enter in the prologue makes the body's frame accesses active"
            );
        });
    }

    #[test]
    fn br_table_frame_actions_abort_lazy_frame_dependency_collection() {
        const SRC: &str = r#"
target = "evm-ethereum-osaka"

func public %dispatch(v0.i256) -> i256 {
block0:
    v1.i256 = add v0 1.i256;
    br_table v0 block3 (0.i256 block1) (11.i256 block2);

block1:
    return v1;

block2:
    return v1;

block3:
    return v1;
}
"#;

        let parsed = parse_module(SRC).expect("module parses");
        let func_ref = parsed.debug.func_order[0];

        parsed.module.func_store.view(func_ref, |function| {
            let term = function
                .layout
                .iter_all_insts()
                .find(|&inst| function.dfg.cast_br_table(inst).is_some())
                .expect("missing br_table terminator");
            let case_count = function
                .dfg
                .cast_br_table(term)
                .expect("br_table terminator should downcast")
                .table()
                .len();
            let root = parsed.debug.value(func_ref, "v1").expect("v1 exists");
            let root_def = function
                .dfg
                .value_inst(root)
                .expect("v1 should be instruction-defined");
            let mut roots = MachineFrameRoots::default();
            roots.root_def_insts.insert(root_def);
            roots.rooted_values.insert(root);
            let mut cfg = ControlFlowGraph::default();
            cfg.compute(function);

            let mut clean_alloc = TestAlloc::for_function(function);
            clean_alloc.cases[term] = vec![Actions::new(); case_count];
            let clean_dep_points = collect_dep_points(function, &cfg, &clean_alloc, &roots)
                .expect("control br_table should allow lazy-frame dependency collection");
            assert!(
                !clean_dep_points.is_empty(),
                "control br_table should collect lazy-frame dependency points"
            );

            let mut base_action_alloc = TestAlloc::for_function(function);
            base_action_alloc.pre[term].push(Action::MemLoadFrameSlot(0));
            base_action_alloc.cases[term] = vec![Actions::new(); case_count];
            assert!(
                collect_dep_points(function, &cfg, &base_action_alloc, &roots).is_none(),
                "frame-touching br_table base actions must abort dependency collection"
            );

            let mut case_action_alloc = TestAlloc::for_function(function);
            case_action_alloc.cases[term] = vec![Actions::new(); case_count];
            case_action_alloc.cases[term][1].push(Action::MemStoreFrameSlot(0));
            assert!(
                collect_dep_points(function, &cfg, &case_action_alloc, &roots).is_none(),
                "frame-touching br_table case actions must abort dependency collection"
            );

            let mut case_address_alloc = TestAlloc::for_function(function);
            case_address_alloc.cases[term] = vec![Actions::new(); case_count];
            case_address_alloc.cases[term][0].push(Action::PushFrameAddr {
                offset_words: 0,
                extra_bytes: 0,
            });
            assert!(
                collect_dep_points(function, &cfg, &case_address_alloc, &roots).is_none(),
                "frame-address br_table case actions must abort dependency collection"
            );
        });
    }
}
